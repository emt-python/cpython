/*

  Reference Cycle Garbage Collection
  ==================================

  Neil Schemenauer <nas@arctrix.com>

  Based on a post on the python-dev list.  Ideas from Guido van Rossum,
  Eric Tiedemann, and various others.

  http://www.arctrix.com/nas/python/gc/

  The following mailing list threads provide a historical perspective on
  the design of this module.  Note that a fair amount of refinement has
  occurred since those discussions.

  http://mail.python.org/pipermail/python-dev/2000-March/002385.html
  http://mail.python.org/pipermail/python-dev/2000-March/002434.html
  http://mail.python.org/pipermail/python-dev/2000-March/002497.html

  For a highlevel view of the collection process, read the collect
  function.

*/

#include "Python.h"
#include "pycore_context.h"
#include "pycore_initconfig.h"
#include "pycore_interp.h" // PyInterpreterState.gc
#include "pycore_object.h"
#include "pycore_pyerrors.h"
#include "pycore_pystate.h" // _PyThreadState_GET()
#include "pydtrace.h"

#include "obj_temp.h"
#include <numaif.h>
#include <numa.h>
#include <setjmp.h>
#include <string.h>
#include <float.h>

#include "myset.h"
#include "kh_set_wrap.h"
static double total_slow_time = 0.0;
static int total_num_slow = 0;
unsigned long global_try2_sched = 0;
// int need2_check_set = 1;
extern unsigned long num_container_collected;
extern PyThreadState *py_main_tstate;

// khash_t(ptrset) * global_op_set;
// extern sigjmp_buf jump_buffer;

kvec_t(PyObject *) local_ptr_vec;

BookkeepArgs *global_bookkeep_args;
uintptr_t glb_lowest_op = UINTPTR_MAX;
struct timespec global_start, global_current;
#define STRINGIFY(x) #x
#define TOSTRING(x) STRINGIFY(x)
static clock_t last_live_trace_time;
static clock_t last_migrate_time;
extern int enable_bk;
bool very_first_demote = true;
bool forced_demo = false;
bool very_first_mig = true;
khash_t(ptrset_dup) * last_demote_pages; // for lazy demotion
double prev_c_w_percent = 0.0;
// unsigned long get_live_time_thresh;
unsigned long num_gc_cycles = 0, prev_gc_cycles = 0;
struct timespec cutoff_start, cutoff_current;
long cutoff_counter = 0;
int reset_all_temps = 1;
long total_new_op_num = 0;
size_t very_large_num_op = 41000000; // roughly 630 MB
#define PAGE_SIZE 4096
#define PAGE_MASK (~(PAGE_SIZE - 1))
#define LEN_THRESHOLD 2
#define DEPTH_THRESHOLD 2
#define LOWER_BOUND 100000000000000
#define HOT_THRESH 100
#define TRIGGER_SCAN_WM 10 // trigger scan if free DRAN < 10%
#define DRAM_MASK 0
#define CXL_MASK 1
#define DROP_OUT_OFF 7
#define LOCATION_OFF 7
#define HOTNESS_MASK 0x7F
#define RESERVED_MEMORY_MB 200
#define SYS_RESERVE 166

#define AVG_COEFF -0.04157018
#define STDDEV_COEFF 0.01717087
#define NON_ZERO_COEFF 0.20755456
#define SMALL_127_COEFF -0.29469896
#define RANGE_COEFF -0.0458398
#define INTERCEPT_HOT 8.520855288592891
// #define METADATA_SIZE 1024 // reserved metadata size in MB
bool early_return = false;
bool skip_future_slow = false;
double cutoff_limit = 0, global_elapsed = 0;
unsigned long cur_fast_num_hot = 0;
static bool very_first_bk = true;
unsigned long not_in_global_set = 0;
extern OBJ_TEMP *all_temps;
bool is_migration = false;
unsigned int old_num_op = 0;
unsigned int prev_num_op = 0;
unsigned int max_depth = 0;
unsigned int max_length = 0;
unsigned long global_demo_size = 0;
unsigned long global_promo_size = 0;
int global_do_migration = 0;   // swich for enable migration or not. 0: disable, 1: enable
int global_demo_mode = 0;      // switch for demotion mode. 0: disable lazy demotion, 1: always lazy (stale impl), 2: always lazy (new impl), 3: adaptive lazy
int global_hotness_thresh = 0; // switch for hotness threshold. 0: 0, 1: avg, 2: median, 3: mode
double total_eagerness = 0.0, prev_eagerness = 0.0;

// for adaptive lazy demo
#define buffer_size 8
const char *perf_stat_file = "workspace/py_track/perf_stat.log";
const char *bw_file = "workspace/py_track/parsed_bw.txt";
char *perf_stat_full_path;
char *bw_full_path;
double dram_bw_arr[buffer_size];
double cxl_bw_arr[buffer_size];
double llc_miss_arr[buffer_size];
const char *home_dir;
char llc_line[256];
char bw_line[128];
double llc_load_miss_percent = 0.0, avg_llc_miss = 0.0;
double dram_bw = 0.0, cxl_bw = 0.0, avg_cxl_bw = 0.0;
int buffer_index = 0;

typedef struct GEN_ID_BOUND
{
    int gen_id;
    uintptr_t low;
    uintptr_t high;
    uintptr_t head;
} GEN_ID_BOUND;

GEN_ID_BOUND gen_id_bound[NUM_GENERATIONS];

typedef struct cur_survived_node
{
    // uintptr_t op;
    PyObject *op;
    struct cur_survived_node *next, *prev;
} cur_survived_node;

PyGC_Head *global_old;
static int gen_idx = -1;

typedef struct
{
    uintptr_t start;
    uintptr_t end;
} PyObj_range;

typedef struct op_hotness
{
    PyObject *op;
    unsigned long hotness;
} op_hotness;

int compareIntervals(const void *a, const void *b)
{
    PyObj_range *A = (PyObj_range *)a;
    PyObj_range *B = (PyObj_range *)b;
    return A->start - B->start; // Corrected to compare start times
}

static inline uintptr_t max(uintptr_t a, uintptr_t b)
{
    return a > b ? a : b;
}
volatile short terminate_flag = 0;

typedef struct _gc_runtime_state GCState;
void update_recursive_visitor(PyObject *each_op, unsigned long *depth);
void inner_traversing(PyObject *each_op, unsigned int *depth);
bool found_in_local_kset(PyObject *op);
static void add_to_survived_from_young(PyGC_Head *survived);

/*[clinic input]
module gc
[clinic start generated code]*/
/*[clinic end generated code: output=da39a3ee5e6b4b0d input=b5c9690ecc842d79]*/

#ifdef Py_DEBUG
#define GC_DEBUG
#endif

#define GC_NEXT _PyGCHead_NEXT
#define GC_PREV _PyGCHead_PREV

// update_refs() set this bit for all objects in current generation.
// subtract_refs() and move_unreachable() uses this to distinguish
// visited object is in GCing or not.
//
// move_unreachable() removes this flag from reachable objects.
// Only unreachable objects have this flag.
//
// No objects in interpreter have this flag after GC ends.
#define PREV_MASK_COLLECTING _PyGC_PREV_MASK_COLLECTING

// Lowest bit of _gc_next is used for UNREACHABLE flag.
//
// This flag represents the object is in unreachable list in move_unreachable()
//
// Although this flag is used only in move_unreachable(), move_unreachable()
// doesn't clear this flag to skip unnecessary iteration.
// move_legacy_finalizers() removes this flag instead.
// Between them, unreachable list is not normal list and we can not use
// most gc_list_* functions for it.
#define NEXT_MASK_UNREACHABLE (1)

/* Get an object's GC head */
#define AS_GC(o) ((PyGC_Head *)(((char *)(o)) - sizeof(PyGC_Head)))

/* Get the object given the GC head */
#define FROM_GC(g) ((PyObject *)(((char *)(g)) + sizeof(PyGC_Head)))

static inline int gc_is_collecting(PyGC_Head *g)
{
    return (g->_gc_prev & PREV_MASK_COLLECTING) != 0;
}

static inline void
gc_clear_collecting(PyGC_Head *g)
{
    g->_gc_prev &= ~PREV_MASK_COLLECTING;
}

static inline Py_ssize_t
gc_get_refs(PyGC_Head *g)
{
    return (Py_ssize_t)(g->_gc_prev >> _PyGC_PREV_SHIFT);
}

static inline void
gc_set_refs(PyGC_Head *g, Py_ssize_t refs)
{
    g->_gc_prev = (g->_gc_prev & ~_PyGC_PREV_MASK) | ((uintptr_t)(refs) << _PyGC_PREV_SHIFT);
}

static inline void
gc_reset_refs(PyGC_Head *g, Py_ssize_t refs)
{
    g->_gc_prev = (g->_gc_prev & _PyGC_PREV_MASK_FINALIZED) | PREV_MASK_COLLECTING | ((uintptr_t)(refs) << _PyGC_PREV_SHIFT);
}

static inline void
gc_decref(PyGC_Head *g)
{
    _PyObject_ASSERT_WITH_MSG(FROM_GC(g),
                              gc_get_refs(g) > 0,
                              "refcount is too small");
    g->_gc_prev -= 1 << _PyGC_PREV_SHIFT;
}

/* set for debugging information */
#define DEBUG_STATS (1 << 0)         /* print collection statistics */
#define DEBUG_COLLECTABLE (1 << 1)   /* print collectable objects */
#define DEBUG_UNCOLLECTABLE (1 << 2) /* print uncollectable objects */
#define DEBUG_SAVEALL (1 << 5)       /* save all garbage in gc.garbage */
#define DEBUG_LEAK DEBUG_COLLECTABLE |       \
                       DEBUG_UNCOLLECTABLE | \
                       DEBUG_SAVEALL

#define GEN_HEAD(gcstate, n) (&(gcstate)->generations[n].head)
void pre_alloc_all_temps();
static GCState *
get_gc_state(void)
{
    PyInterpreterState *interp = _PyInterpreterState_GET();
    return &interp->gc;
}

void _PyGC_InitState(GCState *gcstate)
{

#define INIT_HEAD(GEN)                            \
    do                                            \
    {                                             \
        GEN.head._gc_next = (uintptr_t)&GEN.head; \
        GEN.head._gc_prev = (uintptr_t)&GEN.head; \
    } while (0)

    for (int i = 0; i < NUM_GENERATIONS; i++)
    {
        assert(gcstate->generations[i].count == 0);
        INIT_HEAD(gcstate->generations[i]);
    };
    gcstate->generation0 = GEN_HEAD(gcstate, 0);
    INIT_HEAD(gcstate->permanent_generation);

#undef INIT_HEAD
}

void create_full_path()
{
    size_t home_len = strlen(home_dir);
    size_t perf_stat_file_len = strlen(perf_stat_file);
    size_t bw_file_len = strlen(bw_file);

    perf_stat_full_path = (char *)malloc(home_len + perf_stat_file_len + 2); // +2 for '/' and '\0'
    bw_full_path = (char *)malloc(home_len + bw_file_len + 2);               // +2 for '/' and '\0'

    if (perf_stat_full_path == NULL || bw_full_path == NULL)
    {
        perror("Failed to allocate file path");
        exit(EXIT_FAILURE);
    }

    strcpy(perf_stat_full_path, home_dir);
    strcat(perf_stat_full_path, "/");
    strcat(perf_stat_full_path, perf_stat_file);
    strcpy(bw_full_path, home_dir);
    strcat(bw_full_path, "/");
    strcat(bw_full_path, bw_file);
}
PyStatus
_PyGC_Init(PyInterpreterState *interp)
{
#ifdef DO_MIGRATION
    global_do_migration = DO_MIGRATION;
    fprintf(stderr, "DO_MIGRATION is %d\n", global_do_migration);
#endif

#ifdef DEMO_MODE
    global_demo_mode = DEMO_MODE;
    fprintf(stderr, "DEMO_MODE is %d\n", global_demo_mode);
#endif

#ifdef HOTNESS_THRESH
    global_hotness_thresh = HOTNESS_THRESH;
    fprintf(stderr, "HOTNESS_THRESH is %d\n", global_hotness_thresh);
#endif
    fprintf(stderr, "PyGC_init called\n");

    pre_alloc_all_temps();
    last_live_trace_time = clock();
    enable_bk = 0;
    // get_live_time_thresh = INT_MAX;  // don't trigger slow scan by default
    py_main_tstate = _PyThreadState_GET();
    for (int i = 0; i < NUM_GENERATIONS; i++)
    {
        gen_id_bound[i].gen_id = i;
        gen_id_bound[i].low = UINTPTR_MAX;
        gen_id_bound[i].high = 0;
        gen_id_bound[i].head = 0;
    }
    GCState *gcstate = &interp->gc;

    gcstate->garbage = PyList_New(0);
    if (gcstate->garbage == NULL)
    {
        return _PyStatus_NO_MEMORY();
    }

    gcstate->callbacks = PyList_New(0);
    if (gcstate->callbacks == NULL)
    {
        return _PyStatus_NO_MEMORY();
    }
    return _PyStatus_OK();
}

/*
_gc_prev values
---------------

Between collections, _gc_prev is used for doubly linked list.

Lowest two bits of _gc_prev are used for flags.
PREV_MASK_COLLECTING is used only while collecting and cleared before GC ends
or _PyObject_GC_UNTRACK() is called.

During a collection, _gc_prev is temporary used for gc_refs, and the gc list
is singly linked until _gc_prev is restored.

gc_refs
    At the start of a collection, update_refs() copies the true refcount
    to gc_refs, for each object in the generation being collected.
    subtract_refs() then adjusts gc_refs so that it equals the number of
    times an object is referenced directly from outside the generation
    being collected.

PREV_MASK_COLLECTING
    Objects in generation being collected are marked PREV_MASK_COLLECTING in
    update_refs().


_gc_next values
---------------

_gc_next takes these values:

0
    The object is not tracked

!= 0
    Pointer to the next object in the GC list.
    Additionally, lowest bit is used temporary for
    NEXT_MASK_UNREACHABLE flag described below.

NEXT_MASK_UNREACHABLE
    move_unreachable() then moves objects not reachable (whether directly or
    indirectly) from outside the generation into an "unreachable" set and
    set this flag.

    Objects that are found to be reachable have gc_refs set to 1.
    When this flag is set for the reachable object, the object must be in
    "unreachable" set.
    The flag is unset and the object is moved back to "reachable" set.

    move_legacy_finalizers() will remove this flag from "unreachable" set.
*/

/*** list functions ***/

static inline void
gc_list_init(PyGC_Head *list)
{
    // List header must not have flags.
    // We can assign pointer by simple cast.
    list->_gc_prev = (uintptr_t)list;
    list->_gc_next = (uintptr_t)list;
}

static inline int
gc_list_is_empty(PyGC_Head *list)
{
    return (list->_gc_next == (uintptr_t)list);
}

/* Append `node` to `list`. */
static inline void
gc_list_append(PyGC_Head *node, PyGC_Head *list)
{
    PyGC_Head *last = (PyGC_Head *)list->_gc_prev;

    // last <-> node
    _PyGCHead_SET_PREV(node, last);
    _PyGCHead_SET_NEXT(last, node);

    // node <-> list
    _PyGCHead_SET_NEXT(node, list);
    list->_gc_prev = (uintptr_t)node;
}

/* Remove `node` from the gc list it's currently in. */
static inline void
gc_list_remove(PyGC_Head *node)
{
    PyGC_Head *prev = GC_PREV(node);
    PyGC_Head *next = GC_NEXT(node);

    _PyGCHead_SET_NEXT(prev, next);
    _PyGCHead_SET_PREV(next, prev);

    node->_gc_next = 0; /* object is not currently tracked */
}

/* Move `node` from the gc list it's currently in (which is not explicitly
 * named here) to the end of `list`.  This is semantically the same as
 * gc_list_remove(node) followed by gc_list_append(node, list).
 */
static void
gc_list_move(PyGC_Head *node, PyGC_Head *list)
{
    /* Unlink from current list. */
    PyGC_Head *from_prev = GC_PREV(node);
    PyGC_Head *from_next = GC_NEXT(node);
    _PyGCHead_SET_NEXT(from_prev, from_next);
    _PyGCHead_SET_PREV(from_next, from_prev);

    /* Relink at end of new list. */
    // list must not have flags.  So we can skip macros.
    PyGC_Head *to_prev = (PyGC_Head *)list->_gc_prev;
    _PyGCHead_SET_PREV(node, to_prev);
    _PyGCHead_SET_NEXT(to_prev, node);
    list->_gc_prev = (uintptr_t)node;
    _PyGCHead_SET_NEXT(node, list);
}

/* append list `from` onto list `to`; `from` becomes an empty list */
static void
gc_list_merge(PyGC_Head *from, PyGC_Head *to)
{
    assert(from != to);
    if (!gc_list_is_empty(from))
    {
        PyGC_Head *to_tail = GC_PREV(to);
        PyGC_Head *from_head = GC_NEXT(from);
        PyGC_Head *from_tail = GC_PREV(from);
        assert(from_head != from);
        assert(from_tail != from);

        _PyGCHead_SET_NEXT(to_tail, from_head);
        _PyGCHead_SET_PREV(from_head, to_tail);

        _PyGCHead_SET_NEXT(from_tail, to);
        _PyGCHead_SET_PREV(to, from_tail);
    }
    gc_list_init(from);
}

static Py_ssize_t
gc_list_size(PyGC_Head *list)
{
    PyGC_Head *gc;
    Py_ssize_t n = 0;
    for (gc = GC_NEXT(list); gc != list; gc = GC_NEXT(gc))
    {
        n++;
    }
    return n;
}

/* Walk the list and mark all objects as non-collecting */
static inline void
gc_list_clear_collecting(PyGC_Head *collectable)
{
    PyGC_Head *gc;
    for (gc = GC_NEXT(collectable); gc != collectable; gc = GC_NEXT(gc))
    {
        gc_clear_collecting(gc);
    }
}

/* Append objects in a GC list to a Python list.
 * Return 0 if all OK, < 0 if error (out of memory for list)
 */
static int
append_objects(PyObject *py_list, PyGC_Head *gc_list)
{
    PyGC_Head *gc;
    for (gc = GC_NEXT(gc_list); gc != gc_list; gc = GC_NEXT(gc))
    {
        PyObject *op = FROM_GC(gc);
        if (op != py_list)
        {
            if (PyList_Append(py_list, op))
            {
                return -1; /* exception */
            }
        }
    }
    return 0;
}

// Constants for validate_list's flags argument.
enum flagstates
{
    collecting_clear_unreachable_clear,
    collecting_clear_unreachable_set,
    collecting_set_unreachable_clear,
    collecting_set_unreachable_set
};

#ifdef GC_DEBUG
// validate_list checks list consistency.  And it works as document
// describing when flags are expected to be set / unset.
// `head` must be a doubly-linked gc list, although it's fine (expected!) if
// the prev and next pointers are "polluted" with flags.
// What's checked:
// - The `head` pointers are not polluted.
// - The objects' PREV_MASK_COLLECTING and NEXT_MASK_UNREACHABLE flags are all
//   `set or clear, as specified by the 'flags' argument.
// - The prev and next pointers are mutually consistent.
static void
validate_list(PyGC_Head *head, enum flagstates flags)
{
    assert((head->_gc_prev & PREV_MASK_COLLECTING) == 0);
    assert((head->_gc_next & NEXT_MASK_UNREACHABLE) == 0);
    uintptr_t prev_value = 0, next_value = 0;
    switch (flags)
    {
    case collecting_clear_unreachable_clear:
        break;
    case collecting_set_unreachable_clear:
        prev_value = PREV_MASK_COLLECTING;
        break;
    case collecting_clear_unreachable_set:
        next_value = NEXT_MASK_UNREACHABLE;
        break;
    case collecting_set_unreachable_set:
        prev_value = PREV_MASK_COLLECTING;
        next_value = NEXT_MASK_UNREACHABLE;
        break;
    default:
        assert(!"bad internal flags argument");
    }
    PyGC_Head *prev = head;
    PyGC_Head *gc = GC_NEXT(head);
    while (gc != head)
    {
        PyGC_Head *trueprev = GC_PREV(gc);
        PyGC_Head *truenext = (PyGC_Head *)(gc->_gc_next & ~NEXT_MASK_UNREACHABLE);
        assert(truenext != NULL);
        assert(trueprev == prev);
        assert((gc->_gc_prev & PREV_MASK_COLLECTING) == prev_value);
        assert((gc->_gc_next & NEXT_MASK_UNREACHABLE) == next_value);
        prev = gc;
        gc = truenext;
    }
    assert(prev == GC_PREV(head));
}
#else
#define validate_list(x, y) \
    do                      \
    {                       \
    } while (0)
#endif

/*** end of list stuff ***/

/* Set all gc_refs = ob_refcnt.  After this, gc_refs is > 0 and
 * PREV_MASK_COLLECTING bit is set for all objects in containers.
 */
static void
update_refs(PyGC_Head *containers)
{
    PyGC_Head *next;
    PyGC_Head *gc = GC_NEXT(containers);

    while (gc != containers)
    {
        next = GC_NEXT(gc);
        /* Move any object that might have become immortal to the
         * permanent generation as the reference count is not accurately
         * reflecting the actual number of live references to this object
         */
        if (_Py_IsImmortal(FROM_GC(gc)))
        {
            gc_list_move(gc, &get_gc_state()->permanent_generation.head);
            gc = next;
            continue;
        }
        gc_reset_refs(gc, Py_REFCNT(FROM_GC(gc)));
        /* Python's cyclic gc should never see an incoming refcount
         * of 0:  if something decref'ed to 0, it should have been
         * deallocated immediately at that time.
         * Possible cause (if the assert triggers):  a tp_dealloc
         * routine left a gc-aware object tracked during its teardown
         * phase, and did something-- or allowed something to happen --
         * that called back into Python.  gc can trigger then, and may
         * see the still-tracked dying object.  Before this assert
         * was added, such mistakes went on to allow gc to try to
         * delete the object again.  In a debug build, that caused
         * a mysterious segfault, when _Py_ForgetReference tried
         * to remove the object from the doubly-linked list of all
         * objects a second time.  In a release build, an actual
         * double deallocation occurred, which leads to corruption
         * of the allocator's internal bookkeeping pointers.  That's
         * so serious that maybe this should be a release-build
         * check instead of an assert?
         */
        _PyObject_ASSERT(FROM_GC(gc), gc_get_refs(gc) != 0);
        gc = next;
    }
}

/* A traversal callback for subtract_refs. */
static int
visit_decref(PyObject *op, void *parent)
{
    _PyObject_ASSERT(_PyObject_CAST(parent), !_PyObject_IsFreed(op));

    if (_PyObject_IS_GC(op))
    {
        PyGC_Head *gc = AS_GC(op);
        /* We're only interested in gc_refs for objects in the
         * generation being collected, which can be recognized
         * because only they have positive gc_refs.
         */
        if (gc_is_collecting(gc))
        {
            gc_decref(gc);
        }
    }
    return 0;
}

/* Subtract internal references from gc_refs.  After this, gc_refs is >= 0
 * for all objects in containers, and is GC_REACHABLE for all tracked gc
 * objects not in containers.  The ones with gc_refs > 0 are directly
 * reachable from outside containers, and so can't be collected.
 */
static void
subtract_refs(PyGC_Head *containers)
{
    traverseproc traverse;
    PyGC_Head *gc = GC_NEXT(containers);
    for (; gc != containers; gc = GC_NEXT(gc))
    {
        PyObject *op = FROM_GC(gc);
        traverse = Py_TYPE(op)->tp_traverse;
        (void)traverse(op,
                       (visitproc)visit_decref,
                       op);
    }
}

/* A traversal callback for move_unreachable. */
static int
visit_reachable(PyObject *op, PyGC_Head *reachable)
{
    if (!_PyObject_IS_GC(op))
    {
        return 0;
    }

    PyGC_Head *gc = AS_GC(op);
    const Py_ssize_t gc_refs = gc_get_refs(gc);
    int ret;

    // Ignore objects in other generation.
    // This also skips objects "to the left" of the current position in
    // move_unreachable's scan of the 'young' list - they've already been
    // traversed, and no longer have the PREV_MASK_COLLECTING flag.
    if (!gc_is_collecting(gc))
    {
        return 0;
    }
    // It would be a logic error elsewhere if the collecting flag were set on
    // an untracked object.
    assert(gc->_gc_next != 0);

    if (gc->_gc_next & NEXT_MASK_UNREACHABLE)
    {
        /* This had gc_refs = 0 when move_unreachable got
         * to it, but turns out it's reachable after all.
         * Move it back to move_unreachable's 'young' list,
         * and move_unreachable will eventually get to it
         * again.
         */
        // Manually unlink gc from unreachable list because the list functions
        // don't work right in the presence of NEXT_MASK_UNREACHABLE flags.
        PyGC_Head *prev = GC_PREV(gc);
        PyGC_Head *next = (PyGC_Head *)(gc->_gc_next & ~NEXT_MASK_UNREACHABLE);
        _PyObject_ASSERT(FROM_GC(prev),
                         prev->_gc_next & NEXT_MASK_UNREACHABLE);
        _PyObject_ASSERT(FROM_GC(next),
                         next->_gc_next & NEXT_MASK_UNREACHABLE);
        prev->_gc_next = gc->_gc_next; // copy NEXT_MASK_UNREACHABLE
        _PyGCHead_SET_PREV(next, prev);

        gc_list_append(gc, reachable);
        gc_set_refs(gc, 1);
    }
    else if (gc_refs == 0)
    {
        /* This is in move_unreachable's 'young' list, but
         * the traversal hasn't yet gotten to it.  All
         * we need to do is tell move_unreachable that it's
         * reachable.
         */
        gc_set_refs(gc, 1);
    }
    /* Else there's nothing to do.
     * If gc_refs > 0, it must be in move_unreachable's 'young'
     * list, and move_unreachable will eventually get to it.
     */
    else
    {
        _PyObject_ASSERT_WITH_MSG(op, gc_refs > 0, "refcount is too small");
    }
    return 0;
}

/* Move the unreachable objects from young to unreachable.  After this,
 * all objects in young don't have PREV_MASK_COLLECTING flag and
 * unreachable have the flag.
 * All objects in young after this are directly or indirectly reachable
 * from outside the original young; and all objects in unreachable are
 * not.
 *
 * This function restores _gc_prev pointer.  young and unreachable are
 * doubly linked list after this function.
 * But _gc_next in unreachable list has NEXT_MASK_UNREACHABLE flag.
 * So we can not gc_list_* functions for unreachable until we remove the flag.
 */
static void
move_unreachable(PyGC_Head *young, PyGC_Head *unreachable)
{
    // previous elem in the young list, used for restore gc_prev.
    PyGC_Head *prev = young;
    PyGC_Head *gc = GC_NEXT(young);

    /* Invariants:  all objects "to the left" of us in young are reachable
     * (directly or indirectly) from outside the young list as it was at entry.
     *
     * All other objects from the original young "to the left" of us are in
     * unreachable now, and have NEXT_MASK_UNREACHABLE.  All objects to the
     * left of us in 'young' now have been scanned, and no objects here
     * or to the right have been scanned yet.
     */

    while (gc != young)
    {
        if (gc_get_refs(gc))
        {
            /* gc is definitely reachable from outside the
             * original 'young'.  Mark it as such, and traverse
             * its pointers to find any other objects that may
             * be directly reachable from it.  Note that the
             * call to tp_traverse may append objects to young,
             * so we have to wait until it returns to determine
             * the next object to visit.
             */
            PyObject *op = FROM_GC(gc);
            traverseproc traverse = Py_TYPE(op)->tp_traverse;
            _PyObject_ASSERT_WITH_MSG(op, gc_get_refs(gc) > 0,
                                      "refcount is too small");
            // NOTE: visit_reachable may change gc->_gc_next when
            // young->_gc_prev == gc.  Don't do gc = GC_NEXT(gc) before!
            (void)traverse(op,
                           (visitproc)visit_reachable,
                           (void *)young);
            // relink gc_prev to prev element.
            _PyGCHead_SET_PREV(gc, prev);
            // gc is not COLLECTING state after here.
            gc_clear_collecting(gc);
            prev = gc;
        }
        else
        {
            /* This *may* be unreachable.  To make progress,
             * assume it is.  gc isn't directly reachable from
             * any object we've already traversed, but may be
             * reachable from an object we haven't gotten to yet.
             * visit_reachable will eventually move gc back into
             * young if that's so, and we'll see it again.
             */
            // Move gc to unreachable.
            // No need to gc->next->prev = prev because it is single linked.
            prev->_gc_next = gc->_gc_next;

            // We can't use gc_list_append() here because we use
            // NEXT_MASK_UNREACHABLE here.
            PyGC_Head *last = GC_PREV(unreachable);
            // NOTE: Since all objects in unreachable set has
            // NEXT_MASK_UNREACHABLE flag, we set it unconditionally.
            // But this may pollute the unreachable list head's 'next' pointer
            // too. That's semantically senseless but expedient here - the
            // damage is repaired when this function ends.
            last->_gc_next = (NEXT_MASK_UNREACHABLE | (uintptr_t)gc);
            _PyGCHead_SET_PREV(gc, last);
            gc->_gc_next = (NEXT_MASK_UNREACHABLE | (uintptr_t)unreachable);
            unreachable->_gc_prev = (uintptr_t)gc;
        }
        gc = (PyGC_Head *)prev->_gc_next;
    }
    // young->_gc_prev must be last element remained in the list.
    young->_gc_prev = (uintptr_t)prev;
    // don't let the pollution of the list head's next pointer leak
    unreachable->_gc_next &= ~NEXT_MASK_UNREACHABLE;
}

static void
untrack_tuples(PyGC_Head *head)
{
    PyGC_Head *next, *gc = GC_NEXT(head);
    while (gc != head)
    {
        PyObject *op = FROM_GC(gc);
        next = GC_NEXT(gc);
        if (PyTuple_CheckExact(op))
        {
            _PyTuple_MaybeUntrack(op);
        }
        gc = next;
    }
}

/* Try to untrack all currently tracked dictionaries */
static void
untrack_dicts(PyGC_Head *head)
{
    PyGC_Head *next, *gc = GC_NEXT(head);
    while (gc != head)
    {
        PyObject *op = FROM_GC(gc);
        next = GC_NEXT(gc);
        if (PyDict_CheckExact(op))
        {
            _PyDict_MaybeUntrack(op);
        }
        gc = next;
    }
}

/* Return true if object has a pre-PEP 442 finalization method. */
static int
has_legacy_finalizer(PyObject *op)
{
    return Py_TYPE(op)->tp_del != NULL;
}

/* Move the objects in unreachable with tp_del slots into `finalizers`.
 *
 * This function also removes NEXT_MASK_UNREACHABLE flag
 * from _gc_next in unreachable.
 */
static void
move_legacy_finalizers(PyGC_Head *unreachable, PyGC_Head *finalizers)
{
    PyGC_Head *gc, *next;
    assert((unreachable->_gc_next & NEXT_MASK_UNREACHABLE) == 0);

    /* March over unreachable.  Move objects with finalizers into
     * `finalizers`.
     */
    for (gc = GC_NEXT(unreachable); gc != unreachable; gc = next)
    {
        PyObject *op = FROM_GC(gc);

        _PyObject_ASSERT(op, gc->_gc_next & NEXT_MASK_UNREACHABLE);
        gc->_gc_next &= ~NEXT_MASK_UNREACHABLE;
        next = (PyGC_Head *)gc->_gc_next;

        if (has_legacy_finalizer(op))
        {
            gc_clear_collecting(gc);
            gc_list_move(gc, finalizers);
        }
    }
}

static inline void
clear_unreachable_mask(PyGC_Head *unreachable)
{
    /* Check that the list head does not have the unreachable bit set */
    assert(((uintptr_t)unreachable & NEXT_MASK_UNREACHABLE) == 0);

    PyGC_Head *gc, *next;
    assert((unreachable->_gc_next & NEXT_MASK_UNREACHABLE) == 0);
    for (gc = GC_NEXT(unreachable); gc != unreachable; gc = next)
    {
        _PyObject_ASSERT((PyObject *)FROM_GC(gc), gc->_gc_next & NEXT_MASK_UNREACHABLE);
        gc->_gc_next &= ~NEXT_MASK_UNREACHABLE;
        next = (PyGC_Head *)gc->_gc_next;
    }
    validate_list(unreachable, collecting_set_unreachable_clear);
}

/* A traversal callback for move_legacy_finalizer_reachable. */
static int
visit_move(PyObject *op, PyGC_Head *tolist)
{
    if (_PyObject_IS_GC(op))
    {
        PyGC_Head *gc = AS_GC(op);
        if (gc_is_collecting(gc))
        {
            gc_list_move(gc, tolist);
            gc_clear_collecting(gc);
        }
    }
    return 0;
}

/* Move objects that are reachable from finalizers, from the unreachable set
 * into finalizers set.
 */
static void
move_legacy_finalizer_reachable(PyGC_Head *finalizers)
{
    traverseproc traverse;
    PyGC_Head *gc = GC_NEXT(finalizers);
    for (; gc != finalizers; gc = GC_NEXT(gc))
    {
        /* Note that the finalizers list may grow during this. */
        traverse = Py_TYPE(FROM_GC(gc))->tp_traverse;
        (void)traverse(FROM_GC(gc),
                       (visitproc)visit_move,
                       (void *)finalizers);
    }
}

/* Clear all weakrefs to unreachable objects, and if such a weakref has a
 * callback, invoke it if necessary.  Note that it's possible for such
 * weakrefs to be outside the unreachable set -- indeed, those are precisely
 * the weakrefs whose callbacks must be invoked.  See gc_weakref.txt for
 * overview & some details.  Some weakrefs with callbacks may be reclaimed
 * directly by this routine; the number reclaimed is the return value.  Other
 * weakrefs with callbacks may be moved into the `old` generation.  Objects
 * moved into `old` have gc_refs set to GC_REACHABLE; the objects remaining in
 * unreachable are left at GC_TENTATIVELY_UNREACHABLE.  When this returns,
 * no object in `unreachable` is weakly referenced anymore.
 */
static int
handle_weakrefs(PyGC_Head *unreachable, PyGC_Head *old)
{
    PyGC_Head *gc;
    PyObject *op;           /* generally FROM_GC(gc) */
    PyWeakReference *wr;    /* generally a cast of op */
    PyGC_Head wrcb_to_call; /* weakrefs with callbacks to call */
    PyGC_Head *next;
    int num_freed = 0;

    gc_list_init(&wrcb_to_call);

    /* Clear all weakrefs to the objects in unreachable.  If such a weakref
     * also has a callback, move it into `wrcb_to_call` if the callback
     * needs to be invoked.  Note that we cannot invoke any callbacks until
     * all weakrefs to unreachable objects are cleared, lest the callback
     * resurrect an unreachable object via a still-active weakref.  We
     * make another pass over wrcb_to_call, invoking callbacks, after this
     * pass completes.
     */
    for (gc = GC_NEXT(unreachable); gc != unreachable; gc = next)
    {
        PyWeakReference **wrlist;

        op = FROM_GC(gc);
        next = GC_NEXT(gc);

        if (PyWeakref_Check(op))
        {
            /* A weakref inside the unreachable set must be cleared.  If we
             * allow its callback to execute inside delete_garbage(), it
             * could expose objects that have tp_clear already called on
             * them.  Or, it could resurrect unreachable objects.  One way
             * this can happen is if some container objects do not implement
             * tp_traverse.  Then, wr_object can be outside the unreachable
             * set but can be deallocated as a result of breaking the
             * reference cycle.  If we don't clear the weakref, the callback
             * will run and potentially cause a crash.  See bpo-38006 for
             * one example.
             */
            _PyWeakref_ClearRef((PyWeakReference *)op);
        }

        if (!_PyType_SUPPORTS_WEAKREFS(Py_TYPE(op)))
            continue;

        /* It supports weakrefs.  Does it have any?
         *
         * This is never triggered for static types so we can avoid the
         * (slightly) more costly _PyObject_GET_WEAKREFS_LISTPTR().
         */
        wrlist = _PyObject_GET_WEAKREFS_LISTPTR_FROM_OFFSET(op);

        /* `op` may have some weakrefs.  March over the list, clear
         * all the weakrefs, and move the weakrefs with callbacks
         * that must be called into wrcb_to_call.
         */
        for (wr = *wrlist; wr != NULL; wr = *wrlist)
        {
            PyGC_Head *wrasgc; /* AS_GC(wr) */

            /* _PyWeakref_ClearRef clears the weakref but leaves
             * the callback pointer intact.  Obscure:  it also
             * changes *wrlist.
             */
            _PyObject_ASSERT((PyObject *)wr, wr->wr_object == op);
            _PyWeakref_ClearRef(wr);
            _PyObject_ASSERT((PyObject *)wr, wr->wr_object == Py_None);
            if (wr->wr_callback == NULL)
            {
                /* no callback */
                continue;
            }

            /* Headache time.  `op` is going away, and is weakly referenced by
             * `wr`, which has a callback.  Should the callback be invoked?  If wr
             * is also trash, no:
             *
             * 1. There's no need to call it.  The object and the weakref are
             *    both going away, so it's legitimate to pretend the weakref is
             *    going away first.  The user has to ensure a weakref outlives its
             *    referent if they want a guarantee that the wr callback will get
             *    invoked.
             *
             * 2. It may be catastrophic to call it.  If the callback is also in
             *    cyclic trash (CT), then although the CT is unreachable from
             *    outside the current generation, CT may be reachable from the
             *    callback.  Then the callback could resurrect insane objects.
             *
             * Since the callback is never needed and may be unsafe in this case,
             * wr is simply left in the unreachable set.  Note that because we
             * already called _PyWeakref_ClearRef(wr), its callback will never
             * trigger.
             *
             * OTOH, if wr isn't part of CT, we should invoke the callback:  the
             * weakref outlived the trash.  Note that since wr isn't CT in this
             * case, its callback can't be CT either -- wr acted as an external
             * root to this generation, and therefore its callback did too.  So
             * nothing in CT is reachable from the callback either, so it's hard
             * to imagine how calling it later could create a problem for us.  wr
             * is moved to wrcb_to_call in this case.
             */
            if (gc_is_collecting(AS_GC(wr)))
            {
                /* it should already have been cleared above */
                assert(wr->wr_object == Py_None);
                continue;
            }

            /* Create a new reference so that wr can't go away
             * before we can process it again.
             */
            Py_INCREF(wr);

            /* Move wr to wrcb_to_call, for the next pass. */
            wrasgc = AS_GC(wr);
            assert(wrasgc != next); /* wrasgc is reachable, but
                                       next isn't, so they can't
                                       be the same */
            gc_list_move(wrasgc, &wrcb_to_call);
        }
    }

    /* Invoke the callbacks we decided to honor.  It's safe to invoke them
     * because they can't reference unreachable objects.
     */
    while (!gc_list_is_empty(&wrcb_to_call))
    {
        PyObject *temp;
        PyObject *callback;

        gc = (PyGC_Head *)wrcb_to_call._gc_next;
        op = FROM_GC(gc);
        _PyObject_ASSERT(op, PyWeakref_Check(op));
        wr = (PyWeakReference *)op;
        callback = wr->wr_callback;
        _PyObject_ASSERT(op, callback != NULL);

        /* copy-paste of weakrefobject.c's handle_callback() */
        temp = PyObject_CallOneArg(callback, (PyObject *)wr);
        if (temp == NULL)
            PyErr_WriteUnraisable(callback);
        else
            Py_DECREF(temp);

        /* Give up the reference we created in the first pass.  When
         * op's refcount hits 0 (which it may or may not do right now),
         * op's tp_dealloc will decref op->wr_callback too.  Note
         * that the refcount probably will hit 0 now, and because this
         * weakref was reachable to begin with, gc didn't already
         * add it to its count of freed objects.  Example:  a reachable
         * weak value dict maps some key to this reachable weakref.
         * The callback removes this key->weakref mapping from the
         * dict, leaving no other references to the weakref (excepting
         * ours).
         */
        Py_DECREF(op);
        if (wrcb_to_call._gc_next == (uintptr_t)gc)
        {
            /* object is still alive -- move it */
            gc_list_move(gc, old);
        }
        else
        {
            ++num_freed;
        }
    }

    return num_freed;
}

static void
debug_cycle(const char *msg, PyObject *op)
{
    PySys_FormatStderr("gc: %s <%s %p>\n",
                       msg, Py_TYPE(op)->tp_name, op);
}

/* Handle uncollectable garbage (cycles with tp_del slots, and stuff reachable
 * only from such cycles).
 * If DEBUG_SAVEALL, all objects in finalizers are appended to the module
 * garbage list (a Python list), else only the objects in finalizers with
 * __del__ methods are appended to garbage.  All objects in finalizers are
 * merged into the old list regardless.
 */
static void
handle_legacy_finalizers(PyThreadState *tstate,
                         GCState *gcstate,
                         PyGC_Head *finalizers, PyGC_Head *old)
{
    assert(!_PyErr_Occurred(tstate));
    assert(gcstate->garbage != NULL);

    PyGC_Head *gc = GC_NEXT(finalizers);
    for (; gc != finalizers; gc = GC_NEXT(gc))
    {
        PyObject *op = FROM_GC(gc);

        if ((gcstate->debug & DEBUG_SAVEALL) || has_legacy_finalizer(op))
        {
            if (PyList_Append(gcstate->garbage, op) < 0)
            {
                _PyErr_Clear(tstate);
                break;
            }
        }
    }
    // add_to_survived_from_young(finalizers);
    gc_list_merge(finalizers, old); // here finalizers contain new survived
}

/* Run first-time finalizers (if any) on all the objects in collectable.
 * Note that this may remove some (or even all) of the objects from the
 * list, due to refcounts falling to 0.
 */
static void
finalize_garbage(PyThreadState *tstate, PyGC_Head *collectable)
{
    destructor finalize;
    PyGC_Head seen;

    /* While we're going through the loop, `finalize(op)` may cause op, or
     * other objects, to be reclaimed via refcounts falling to zero.  So
     * there's little we can rely on about the structure of the input
     * `collectable` list across iterations.  For safety, we always take the
     * first object in that list and move it to a temporary `seen` list.
     * If objects vanish from the `collectable` and `seen` lists we don't
     * care.
     */
    gc_list_init(&seen);

    while (!gc_list_is_empty(collectable))
    {
        PyGC_Head *gc = GC_NEXT(collectable);
        PyObject *op = FROM_GC(gc);
        gc_list_move(gc, &seen);
        if (!_PyGCHead_FINALIZED(gc) &&
            (finalize = Py_TYPE(op)->tp_finalize) != NULL)
        {
            _PyGCHead_SET_FINALIZED(gc);
            Py_INCREF(op);
            finalize(op);
            assert(!_PyErr_Occurred(tstate));
            Py_DECREF(op);
        }
    }
    gc_list_merge(&seen, collectable);
}

/* Break reference cycles by clearing the containers involved.  This is
 * tricky business as the lists can be changing and we don't know which
 * objects may be freed.  It is possible I screwed something up here.
 */
static void
delete_garbage(PyThreadState *tstate, GCState *gcstate,
               PyGC_Head *collectable, PyGC_Head *old)
{
    assert(!_PyErr_Occurred(tstate));
    while (!gc_list_is_empty(collectable))
    {
        PyGC_Head *gc = GC_NEXT(collectable);
        PyObject *op = FROM_GC(gc);

        _PyObject_ASSERT_WITH_MSG(op, Py_REFCNT(op) > 0,
                                  "refcount is too small");

        if (gcstate->debug & DEBUG_SAVEALL)
        {
            assert(gcstate->garbage != NULL);
            if (PyList_Append(gcstate->garbage, op) < 0)
            {
                _PyErr_Clear(tstate);
            }
        }
        else
        {
            inquiry clear;
            if ((clear = Py_TYPE(op)->tp_clear) != NULL)
            {
                Py_INCREF(op);
                (void)clear(op);
                num_container_collected++;
                // erase_from_global((uintptr_t)op);
                if (_PyErr_Occurred(tstate))
                {
                    _PyErr_WriteUnraisableMsg("in tp_clear of",
                                              (PyObject *)Py_TYPE(op));
                }
                Py_DECREF(op);
            }
        }
        if (GC_NEXT(collectable) == gc)
        {
            /* object is still alive, move it, it may die later */
            gc_clear_collecting(gc);
            gc_list_move(gc, old);
        }
    }
}

/* Clear all free lists
 * All free lists are cleared during the collection of the highest generation.
 * Allocated items in the free list may keep a pymalloc arena occupied.
 * Clearing the free lists may give back memory to the OS earlier.
 */
static void
clear_freelists(PyInterpreterState *interp)
{
    _PyTuple_ClearFreeList(interp);
    _PyFloat_ClearFreeList(interp);
    _PyList_ClearFreeList(interp);
    _PyDict_ClearFreeList(interp);
    _PyAsyncGen_ClearFreeLists(interp);
    _PyContext_ClearFreeList(interp);
}

// Show stats for objects in each generations
static void
show_stats_each_generations(GCState *gcstate)
{
    char buf[100];
    size_t pos = 0;

    for (int i = 0; i < NUM_GENERATIONS && pos < sizeof(buf); i++)
    {
        pos += PyOS_snprintf(buf + pos, sizeof(buf) - pos,
                             " %zd",
                             gc_list_size(GEN_HEAD(gcstate, i)));
    }

    PySys_FormatStderr(
        "gc: objects in each generation:%s\n"
        "gc: objects in permanent generation: %zd\n",
        buf, gc_list_size(&gcstate->permanent_generation.head));
}

/* Deduce which objects among "base" are unreachable from outside the list
   and move them to 'unreachable'. The process consist in the following steps:

1. Copy all reference counts to a different field (gc_prev is used to hold
   this copy to save memory).
2. Traverse all objects in "base" and visit all referred objects using
   "tp_traverse" and for every visited object, subtract 1 to the reference
   count (the one that we copied in the previous step). After this step, all
   objects that can be reached directly from outside must have strictly positive
   reference count, while all unreachable objects must have a count of exactly 0.
3. Identify all unreachable objects (the ones with 0 reference count) and move
   them to the "unreachable" list. This step also needs to move back to "base" all
   objects that were initially marked as unreachable but are referred transitively
   by the reachable objects (the ones with strictly positive reference count).

Contracts:

    * The "base" has to be a valid list with no mask set.

    * The "unreachable" list must be uninitialized (this function calls
      gc_list_init over 'unreachable').

IMPORTANT: This function leaves 'unreachable' with the NEXT_MASK_UNREACHABLE
flag set but it does not clear it to skip unnecessary iteration. Before the
flag is cleared (for example, by using 'clear_unreachable_mask' function or
by a call to 'move_legacy_finalizers'), the 'unreachable' list is not a normal
list and we can not use most gc_list_* functions for it. */
static inline void
deduce_unreachable(PyGC_Head *base, PyGC_Head *unreachable)
{
    validate_list(base, collecting_clear_unreachable_clear);
    /* Using ob_refcnt and gc_refs, calculate which objects in the
     * container set are reachable from outside the set (i.e., have a
     * refcount greater than 0 when all the references within the
     * set are taken into account).
     */
    update_refs(base); // gc_prev is used for gc_refs
    subtract_refs(base);

    /* Leave everything reachable from outside base in base, and move
     * everything else (in base) to unreachable.
     *
     * NOTE:  This used to move the reachable objects into a reachable
     * set instead.  But most things usually turn out to be reachable,
     * so it's more efficient to move the unreachable things.  It "sounds slick"
     * to move the unreachable objects, until you think about it - the reason it
     * pays isn't actually obvious.
     *
     * Suppose we create objects A, B, C in that order.  They appear in the young
     * generation in the same order.  If B points to A, and C to B, and C is
     * reachable from outside, then the adjusted refcounts will be 0, 0, and 1
     * respectively.
     *
     * When move_unreachable finds A, A is moved to the unreachable list.  The
     * same for B when it's first encountered.  Then C is traversed, B is moved
     * _back_ to the reachable list.  B is eventually traversed, and then A is
     * moved back to the reachable list.
     *
     * So instead of not moving at all, the reachable objects B and A are moved
     * twice each.  Why is this a win?  A straightforward algorithm to move the
     * reachable objects instead would move A, B, and C once each.
     *
     * The key is that this dance leaves the objects in order C, B, A - it's
     * reversed from the original order.  On all _subsequent_ scans, none of
     * them will move.  Since most objects aren't in cycles, this can save an
     * unbounded number of moves across an unbounded number of later collections.
     * It can cost more only the first time the chain is scanned.
     *
     * Drawback:  move_unreachable is also used to find out what's still trash
     * after finalizers may resurrect objects.  In _that_ case most unreachable
     * objects will remain unreachable, so it would be more efficient to move
     * the reachable objects instead.  But this is a one-time cost, probably not
     * worth complicating the code to speed just a little.
     */
    gc_list_init(unreachable);
    move_unreachable(base, unreachable); // gc_prev is pointer again
    validate_list(base, collecting_clear_unreachable_clear);
    validate_list(unreachable, collecting_set_unreachable_set);
}

/* Handle objects that may have resurrected after a call to 'finalize_garbage', moving
   them to 'old_generation' and placing the rest on 'still_unreachable'.

   Contracts:
       * After this function 'unreachable' must not be used anymore and 'still_unreachable'
         will contain the objects that did not resurrect.

       * The "still_unreachable" list must be uninitialized (this function calls
         gc_list_init over 'still_unreachable').

IMPORTANT: After a call to this function, the 'still_unreachable' set will have the
PREV_MARK_COLLECTING set, but the objects in this set are going to be removed so
we can skip the expense of clearing the flag to avoid extra iteration. */
static inline void
handle_resurrected_objects(PyGC_Head *unreachable, PyGC_Head *still_unreachable,
                           PyGC_Head *old_generation)
{
    // Remove the PREV_MASK_COLLECTING from unreachable
    // to prepare it for a new call to 'deduce_unreachable'
    gc_list_clear_collecting(unreachable);

    // After the call to deduce_unreachable, the 'still_unreachable' set will
    // have the PREV_MARK_COLLECTING set, but the objects are going to be
    // removed so we can skip the expense of clearing the flag.
    PyGC_Head *resurrected = unreachable;
    deduce_unreachable(resurrected, still_unreachable);
    clear_unreachable_mask(still_unreachable);

    // Move the resurrected objects to the old generation for future collection.
    // add_to_survived_from_young(resurrected);
    gc_list_merge(resurrected, old_generation);
}

void debug_type_set(PyGC_Head *gc_head, char *insert_or_delete)
{
    PyGC_Head *gc;
    for (gc = GC_NEXT(gc_head); gc != gc_head; gc = GC_NEXT(gc))
    {
        PyObject *op = FROM_GC(gc);
        PyTypeObject *get_type = Py_TYPE(op);
        if ((void *)get_type == (void *)0xffffffffffffffff)
        {
            fprintf(stderr, "type not set duing %s\n", insert_or_delete);
        }
    }
}

int check_io_type(PyObject *obj)
{
    PyObject *io_module = PyImport_ImportModule("io");
    if (!io_module)
    {
        PyErr_Print();
    }
    // const char *io_types[] = {"IOBase", "IncrementalNewlineDecoder", "RawIOBase", "BufferedIOBase", "BufferedRWPair", "BufferedRandom", "BufferedReader",
    //                           "BufferedWriter", "BytesIOBuffer", "BytesIO", "FileIO", "StringIO", "TextIOBase", "TextIOWrapper", NULL};
    const char *io_types[] = {"FileIO", "BufferedReader", "BufferedWriter", "TextIOWrapper", NULL};
    for (int i = 0; io_types[i] != NULL; i++)
    {
        PyObject *io_type = PyObject_GetAttrString(io_module, io_types[i]);
        if (PyObject_IsInstance(obj, io_type))
        {
            Py_DECREF(io_type);
            // break;
            fprintf(stderr, "skipping %ld, IO type: %s\n", (uintptr_t)obj, io_types[i]);
            return 1;
        }
        Py_DECREF(io_type);
    }
    Py_DECREF(io_module);
    return 0;
}
int check_ipaddr_type(PyObject *obj)
{
    PyObject *ipaddress_module = PyImport_ImportModule("ipaddress");
    if (!ipaddress_module)
    {
        PyErr_Print();
    }
    const char *ipaddr_types[] = {"IPv4Address", "IPv6Address", "IPv4Network", "IPv6Network", NULL};
    for (int i = 0; ipaddr_types[i] != NULL; i++)
    {
        PyObject *ipaddr_type = PyObject_GetAttrString(ipaddress_module, ipaddr_types[i]);
        // if (!ipv4address_class)
        // {
        //     PyErr_Print();
        //     Py_DECREF(ipaddress_module);
        //     return 1;
        // }
        if (PyObject_IsInstance(obj, ipaddr_type))
        {
            Py_DECREF(ipaddr_type);
            // fprintf(stderr, "skipping %ld, ipaddr type: %s\n", (uintptr_t)obj, ipaddr_types[i]);
            return 1;
        }
        Py_DECREF(ipaddr_type);
    }
    Py_DECREF(ipaddress_module);
    return 0;
}

int check_itertools_count_type(PyObject *obj)
{
    PyObject *itertools_module, *count_type;
    itertools_module = PyImport_ImportModule("itertools");
    if (!itertools_module)
    {
        PyErr_Print();
    }
    count_type = PyObject_GetAttrString(itertools_module, "count");
    if (PyObject_IsInstance(obj, count_type))
    {
        Py_DECREF(count_type);
        fprintf(stderr, "skipping %ld, itertools.count\n", (uintptr_t)obj);
        return 1;
    }
    Py_DECREF(count_type);

    return 0;
}

int check_object_type(PyObject *obj)
{
    if (check_io_type(obj) == 1)
    {
        return 1;
    }
    else if (check_ipaddr_type(obj) == 1)
    {
        return 1;
    }
    else if (check_itertools_count_type(obj) == 1)
    {
        return 1;
    }
    else if (PyGen_Check(obj))
        return 1;
    return 0;
}
double try_cascading_old(int slow_idx)
{
    struct timespec start, end;
    double elapsed;
    clock_gettime(CLOCK_MONOTONIC, &start);

    if (!enable_bk || !global_old || gen_idx == -1)
    {
        fprintf(stderr, "unlikely, returned\n");
        return;
    }
    PyGILState_STATE gstate = PyGILState_Ensure();
    clock_gettime(CLOCK_MONOTONIC, &end);
    elapsed = end.tv_sec - start.tv_sec;
    elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
    fprintf(stderr, "\nentering slow.. acquire GIL time: %.3f\n", elapsed);

    PyGC_Head *gc;
    PyObject *container_op;
    int ret;
    fprintf(stderr, "global_old: %ld, generation: %d\n", (uintptr_t)global_old, gen_idx);

    if (gen_id_bound[gen_idx].head == 0)
    {
        gen_id_bound[gen_idx].head = (uintptr_t)global_old;
    }
    else if (gen_id_bound[gen_idx].head != (uintptr_t)global_old)
    {
        fprintf(stderr, "head changed! not cool!\n");
    }
    cutoff_counter = 0;

    PyGC_Head *oldest_gen_head = (PyGC_Head *)gen_id_bound[NUM_GENERATIONS - 1].head;
    PyGC_Head *tracing_head = (oldest_gen_head == NULL) ? global_old : oldest_gen_head; // by default, last gen, otherwise (empty), use recently GC-ed gen
    PyThreadState *tstate = _PyThreadState_GET();
    GCState *gcstate = &tstate->interp->gc;
    // examine how many objects traced by cyclic
    // for (int i = 0; i < 3; i++)
    // {
    //     PyGC_Head *cur_head = GEN_HEAD(gcstate, i);
    //     Py_ssize_t num_ctn_obj = gc_list_size(cur_head);
    //     fprintf(stderr, "GEN %d: %d\n", i, num_ctn_obj);
    // }
    for (int i = 0; i < NUM_GENERATIONS; i++)
    { // traverse all 3 lists
        // uintptr_t local_lowest_op = UINTPTR_MAX;
        // uintptr_t cur_gen_low_bound = gen_id_bound[i].low;
        tracing_head = GEN_HEAD(gcstate, i);
        clock_gettime(CLOCK_MONOTONIC, &cutoff_start);
        for (gc = GC_NEXT(tracing_head); gc != tracing_head; gc = GC_NEXT(gc))
        {
            if (early_return)
                break;
            container_op = FROM_GC(gc);
            uintptr_t casted_op = (uintptr_t)container_op;
            // if (casted_op < cur_gen_low_bound)
            {
                if (check_in_global(casted_op))
                // if (check_in_map(casted_op))
                // if (found_in_kset_helper(container_op))
                {
                    continue;
                }
                // unsigned long cur_len = Py_SIZE(container_op); // || cur_len > 10000000
                // if (cur_len > LEN_THRESHOLD)
                //     continue;
                // if (casted_op < local_lowest_op && casted_op > LOWER_BOUND)
                // {
                //     local_lowest_op = casted_op;
                // }
                insert_into_global(casted_op); // dedup
                // insert_into_map(casted_op, 0);
                // kh_put(ptrset, global_op_set, casted_op, &ret);
                // insert_global_set_helper(container_op);
                kv_push(PyObject *, local_ptr_vec, container_op);
                unsigned long combined = 0;
                update_recursive_visitor(container_op, &combined); // cascading
            }
        }
        // early_return = false;
        // gen_id_bound[i].low = local_lowest_op;
    }
    PyGILState_Release(gstate);
    early_return = false;
    clock_gettime(CLOCK_MONOTONIC, &end);
    elapsed = end.tv_sec - start.tv_sec;
    elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
    fprintf(stderr, "slow trace time (including holding GIL): %.3f seconds, new op: %ld\n", elapsed, kv_size(local_ptr_vec));
    return elapsed;
}

void pre_alloc_all_temps()
{
    // all_temps = (OBJ_TEMP *)calloc(num_op, sizeof(OBJ_TEMP));
    fprintf(stderr, "pre_allocate all_temps\n");
    all_temps = (OBJ_TEMP *)numa_alloc_onnode(very_large_num_op * sizeof(OBJ_TEMP), DRAM_MASK);
    if (all_temps == NULL)
    {
        fprintf(stderr, "Failed to allocate memory for all ops\n");
        return 0;
    }
    memset(all_temps, 0, very_large_num_op * sizeof(OBJ_TEMP));
}

int populate_temps()
{
    unsigned int num_op = 0;
    assert(all_temps != NULL);
    int ret = 0;
    if (old_num_op == 0)
        ret = 1;
    else
        ret = 2;
    prev_num_op = old_num_op;
    num_op = kv_size(local_ptr_vec);
    unsigned int new_num_op = num_op + old_num_op;
    for (int i = old_num_op; i < new_num_op; i++)
    {
        all_temps[i].op = kv_A(local_ptr_vec, i - old_num_op);
    }
    old_num_op = new_num_op;
    return ret;
}

void gen_temps_refchain()
{
    clock_t t;
    t = clock();
    unsigned int num_op;
    if (all_temps)
        free(all_temps);
    if (kv_size(local_ptr_vec) > 0)
    {
        // first time --> malloc
        num_op = kv_size(local_ptr_vec);
        all_temps = (OBJ_TEMP *)malloc(num_op * sizeof(OBJ_TEMP));
        if (all_temps == NULL)
        {
            fprintf(stderr, "Failed to allocate memory for all ops\n");
            return -1;
        }
        for (int i = 0; i < num_op; i++)
        {
            all_temps[i].op = kv_A(local_ptr_vec, i);
            all_temps[i].prev_refcnt = 0;
        }
        old_num_op = num_op;
        // fprintf(stderr, "first time appended %u nodes\n", num_op);
    }
    fprintf(stderr, "total: %u, forming all_temp time: %.3f sec\n", old_num_op, (float)(clock() - t) / CLOCKS_PER_SEC);
}

// return value:
// (cannot happen)-1: no new op & a lot recent collected ops, all_temps freed, sleep and do next slow
// 0: slow scan not triggered， use old all_temps
// 1: slow scan triggered, all_teamp formed
// 2: all_temps realloced
static int try_trigger_slow_scan()
{
    double elapsed;
    struct timespec start, end;
    int ret;
    unsigned int cur_global_size = get_global_size();
    fprintf(stderr, "global_try2_sched: %ld\n", global_try2_sched);
    fprintf(stderr, "recent num_container_collected: %lu, global size: %d\n", num_container_collected, cur_global_size);
    double div = (double)old_num_op / cur_global_size;
    fprintf(stderr, "div: %.3f\n", div);
    // if (is_migration)
    {
        is_migration = false;
#ifdef FORCE_CLEAR_TEMPS
        // reset_pages_hotness();
        reset_pages_bkt_hotness();
#else
        // page_temp_cooling(0.2);
        page_bkt_cooling(0.1);
#endif
        // fprintf(stderr, "clearing diff in metadata\n");
        {
            for (unsigned int i = 0; i < old_num_op; i++)
            {
                all_temps[i].diffs[NUM_SLOTS - 1] = 0;
                // for (int j = 0; j < NUM_SLOTS; j++)
                // {
                //     all_temps[i].diffs[j] = 0;
                // }
                // all_temps[i].diff = 0; // why need?
            }
        }
    }
    fprintf(stderr, "num_gc_cycles: %ld\n", num_gc_cycles);
    if ((num_gc_cycles - prev_gc_cycles < 2000) && !very_first_bk)
        skip_future_slow = true;
    prev_gc_cycles = num_gc_cycles;

    if (skip_future_slow)
    {
        global_try2_sched = 0;
        num_container_collected = 0;
        fprintf(stderr, "skipping next slow\n");
        skip_future_slow = false;
        return 0;
    }
    if (div > 1.15)
    {
        fprintf(stderr, "free and reset metadata\n");
        clock_gettime(CLOCK_MONOTONIC, &start);
        reset_all_temps_func();
        // PyGILState_Release(reset_gil);
        clock_gettime(CLOCK_MONOTONIC, &end);
        elapsed = end.tv_sec - start.tv_sec;
        elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
        fprintf(stderr, "reset_all_temps time: %.3f, for %lu\n", elapsed, old_num_op);
        ret = 1; // all_temps reformed
        goto reset_and_return;
    }

    // if (!very_first_bk && (global_try2_sched < 100 && num_container_collected < 100000)) // if either newly created container_op or recently connected op is small, then just skip slow
    // {
    //     fprintf(stderr, "I don't see much container op created, skip slow...\n");
    //     global_try2_sched = 0;
    //     num_container_collected = 0;
    //     return 0;
    // }
    // do cascade tracing
    kv_init(local_ptr_vec);
    double cur_cascading_time = try_cascading_old(total_num_slow);
    {
        total_slow_time += cur_cascading_time;
        total_num_slow++;
    }
    fprintf(stderr, "total_slow_time: %.3f, total_num_slow: %d\n", total_slow_time, total_num_slow);

    if (!very_first_bk)
    {
        total_new_op_num += kv_size(local_ptr_vec);
    }
    fprintf(stderr, "new_op size: %d, accumulated new_op: %ld\n", kv_size(local_ptr_vec), total_new_op_num);

#ifdef FORCE_REFORM_ALL_TEMPS
    fprintf(stderr, "force reform all_temps!\n");
    reset_all_temps_func();
    ret = 1;
    goto reset_and_return;
#endif
    // if (kv_size(local_ptr_vec) > 1000)
    if (kv_size(local_ptr_vec) < 1000)
    {
        fprintf(stderr, "not much new\n");
        global_try2_sched = 0;
        num_container_collected = 0;
        return 0; // no need to reset prev_refcnt
    }
    else
    {
        clock_gettime(CLOCK_MONOTONIC, &start);
        ret = populate_temps(); // 0. error, 1. reset all_temps, 2. realloc (append) to all_temps
        if (!ret)
            fprintf(stderr, "unlikely, error!!!\n");
        clock_gettime(CLOCK_MONOTONIC, &end);
        elapsed = end.tv_sec - start.tv_sec;
        elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
        fprintf(stderr, "populate_temp time: %.3f\n", elapsed);
    }
    fprintf(stderr, "cur_global_size: %d, old_num_op: %d\n", cur_global_size, old_num_op);

    kv_destroy(local_ptr_vec);

reset_and_return:
    num_container_collected = 0;
    global_try2_sched = 0;
    // num_gc_cycles = 0;
    return ret;
}

static void add_to_survived_from_young(PyGC_Head *survived)
{
    if (!enable_bk)
        return;
    PyGC_Head *gc;
    int ret;
    for (gc = GC_NEXT(survived); gc != survived; gc = GC_NEXT(gc))
    {
        PyObject *op = FROM_GC(gc);
        // try_append_survived_set(op);
    }
}

/* This is the main function.  Read this to understand how the
 * collection process works. */
static Py_ssize_t
gc_collect_main(PyThreadState *tstate, int generation,
                Py_ssize_t *n_collected, Py_ssize_t *n_uncollectable,
                int nofail)
{
    int i;
    Py_ssize_t m = 0;      /* # objects collected */
    Py_ssize_t n = 0;      /* # unreachable objects that couldn't be collected */
    PyGC_Head *young;      /* the generation we are examining */
    PyGC_Head *old;        /* next older generation */
    PyGC_Head unreachable; /* non-problematic unreachable trash */
    PyGC_Head finalizers;  /* objects with, & reachable from, __del__ */
    PyGC_Head *gc;
    _PyTime_t t1 = 0; /* initialize to prevent a compiler warning */
    GCState *gcstate = &tstate->interp->gc;

    // gc_collect_main() must not be called before _PyGC_Init
    // or after _PyGC_Fini()
    assert(gcstate->garbage != NULL);
    assert(!_PyErr_Occurred(tstate));

    if (gcstate->debug & DEBUG_STATS)
    {
        PySys_WriteStderr("gc: collecting generation %d...\n", generation);
        show_stats_each_generations(gcstate);
        t1 = _PyTime_GetPerfCounter();
    }

    if (PyDTrace_GC_START_ENABLED())
        PyDTrace_GC_START(generation);

    /* update collection and allocation counters */
    if (generation + 1 < NUM_GENERATIONS)
        gcstate->generations[generation + 1].count += 1;
    for (i = 0; i <= generation; i++)
        gcstate->generations[i].count = 0;

    /* merge younger generations with one we are currently collecting */
    for (i = 0; i < generation; i++)
    {
        gc_list_merge(GEN_HEAD(gcstate, i), GEN_HEAD(gcstate, generation));
    }

    /* handy references */
    young = GEN_HEAD(gcstate, generation);
    if (generation < NUM_GENERATIONS - 1) // 0, 1
        old = GEN_HEAD(gcstate, generation + 1);
    else
        old = young;
    validate_list(old, collecting_clear_unreachable_clear);

    deduce_unreachable(young, &unreachable);

    untrack_tuples(young);
    // add_to_survived_from_young(young);
    /* Move reachable objects to next generation. */
    if (young != old) // 0, 1
    {
        if (generation == NUM_GENERATIONS - 2) // 1
        {
            gcstate->long_lived_pending += gc_list_size(young);
        }
        /* insert still reachable to global table
         *   `young` is HEAD of all objs that are still reachable (to be merged). */
        gc_list_merge(young, old);
    }
    else
    { // if the oldest gen
        /* We only un-track dicts in full collections, to avoid quadratic
        dict build-up. See issue #14775. */
        untrack_dicts(young);
        gcstate->long_lived_pending = 0;
        gcstate->long_lived_total = gc_list_size(young);
    }

    /* All objects in unreachable are trash, but objects reachable from
     * legacy finalizers (e.g. tp_del) can't safely be deleted.
     */
    gc_list_init(&finalizers);
    // NEXT_MASK_UNREACHABLE is cleared here.
    // After move_legacy_finalizers(), unreachable is normal list.
    move_legacy_finalizers(&unreachable, &finalizers);
    /* finalizers contains the unreachable objects with a legacy finalizer;
     * unreachable objects reachable *from* those are also uncollectable,
     * and we move those into the finalizers list too.
     */
    move_legacy_finalizer_reachable(&finalizers);

    validate_list(&finalizers, collecting_clear_unreachable_clear);
    validate_list(&unreachable, collecting_set_unreachable_clear);

    /* Print debugging information. */
    if (gcstate->debug & DEBUG_COLLECTABLE)
    {
        for (gc = GC_NEXT(&unreachable); gc != &unreachable; gc = GC_NEXT(gc))
        {
            debug_cycle("collectable", FROM_GC(gc));
        }
    }

    /* Clear weakrefs and invoke callbacks as necessary. */
    m += handle_weakrefs(&unreachable, old);

    validate_list(old, collecting_clear_unreachable_clear);
    validate_list(&unreachable, collecting_set_unreachable_clear);

    /* Call tp_finalize on objects which have one. */
    finalize_garbage(tstate, &unreachable);

    /* Handle any objects that may have resurrected after the call
     * to 'finalize_garbage' and continue the collection with the
     * objects that are still unreachable */
    PyGC_Head final_unreachable;
    handle_resurrected_objects(&unreachable, &final_unreachable, old);

    /* Call tp_clear on objects in the final_unreachable set.  This will cause
     * the reference cycles to be broken.  It may also cause some objects
     * in finalizers to be freed.
     */
    m += gc_list_size(&final_unreachable);
    /* delete (future) unreachable objs */
    {
        delete_garbage(tstate, gcstate, &final_unreachable, old);
    }

    /* Collect statistics on uncollectable objects found and print
     * debugging information. */
    for (gc = GC_NEXT(&finalizers); gc != &finalizers; gc = GC_NEXT(gc))
    {
        n++;
        if (gcstate->debug & DEBUG_UNCOLLECTABLE)
            debug_cycle("uncollectable", FROM_GC(gc));
    }
    if (gcstate->debug & DEBUG_STATS)
    {
        double d = _PyTime_AsSecondsDouble(_PyTime_GetPerfCounter() - t1);
        PySys_WriteStderr(
            "gc: done, %zd unreachable, %zd uncollectable, %.4fs elapsed\n",
            n + m, n, d);
    }
    // fprintf(stderr, "%zd unreachable, %zd collected, %zd uncollectable\n", n + m, m, n);

    /* Append instances in the uncollectable set to a Python
     * reachable list of garbage.  The programmer has to deal with
     * this if they insist on creating this type of structure.
     */
    handle_legacy_finalizers(tstate, gcstate, &finalizers, old);
    validate_list(old, collecting_clear_unreachable_clear);
    global_old = old;
    gen_idx = generation;

    /* Clear free list only during the collection of the highest
     * generation */
    if (generation == NUM_GENERATIONS - 1)
    {
        clear_freelists(tstate->interp);
    }

    if (_PyErr_Occurred(tstate))
    {
        if (nofail)
        {
            _PyErr_Clear(tstate);
        }
        else
        {
            _PyErr_WriteUnraisableMsg("in garbage collection", NULL);
        }
    }

    /* Update stats */
    if (n_collected)
    {
        *n_collected = m;
    }
    if (n_uncollectable)
    {
        *n_uncollectable = n;
    }

    struct gc_generation_stats *stats = &gcstate->generation_stats[generation];
    stats->collections++;
    stats->collected += m;
    stats->uncollectable += n;

    if (PyDTrace_GC_DONE_ENABLED())
    {
        PyDTrace_GC_DONE(n + m);
    }

    assert(!_PyErr_Occurred(tstate));
    return n + m;
}

/* Invoke progress callbacks to notify clients that garbage collection
 * is starting or stopping
 */
static void
invoke_gc_callback(PyThreadState *tstate, const char *phase,
                   int generation, Py_ssize_t collected,
                   Py_ssize_t uncollectable)
{
    assert(!_PyErr_Occurred(tstate));

    /* we may get called very early */
    GCState *gcstate = &tstate->interp->gc;
    if (gcstate->callbacks == NULL)
    {
        return;
    }

    /* The local variable cannot be rebound, check it for sanity */
    assert(PyList_CheckExact(gcstate->callbacks));
    PyObject *info = NULL;
    if (PyList_GET_SIZE(gcstate->callbacks) != 0)
    {
        info = Py_BuildValue("{sisnsn}",
                             "generation", generation,
                             "collected", collected,
                             "uncollectable", uncollectable);
        if (info == NULL)
        {
            PyErr_WriteUnraisable(NULL);
            return;
        }
    }

    PyObject *phase_obj = PyUnicode_FromString(phase);
    if (phase_obj == NULL)
    {
        Py_XDECREF(info);
        PyErr_WriteUnraisable(NULL);
        return;
    }

    PyObject *stack[] = {phase_obj, info};
    for (Py_ssize_t i = 0; i < PyList_GET_SIZE(gcstate->callbacks); i++)
    {
        PyObject *r, *cb = PyList_GET_ITEM(gcstate->callbacks, i);
        Py_INCREF(cb); /* make sure cb doesn't go away */
        r = PyObject_Vectorcall(cb, stack, 2, NULL);
        if (r == NULL)
        {
            PyErr_WriteUnraisable(cb);
        }
        else
        {
            Py_DECREF(r);
        }
        Py_DECREF(cb);
    }
    Py_DECREF(phase_obj);
    Py_XDECREF(info);
    assert(!_PyErr_Occurred(tstate));
    if (!strcmp(phase, "stop") && enable_bk)
    {
        num_gc_cycles++;
    }
}

/* Perform garbage collection of a generation and invoke
 * progress callbacks.
 */
static Py_ssize_t
gc_collect_with_callback(PyThreadState *tstate, int generation)
{
    assert(!_PyErr_Occurred(tstate));
    Py_ssize_t result, collected, uncollectable;
    invoke_gc_callback(tstate, "start", generation, 0, 0);
    result = gc_collect_main(tstate, generation, &collected, &uncollectable, 0);
    invoke_gc_callback(tstate, "stop", generation, collected, uncollectable);
    assert(!_PyErr_Occurred(tstate));
    return result;
}

static Py_ssize_t
gc_collect_generations(PyThreadState *tstate)
{
    GCState *gcstate = &tstate->interp->gc;
    /* Find the oldest generation (highest numbered) where the count
     * exceeds the threshold.  Objects in the that generation and
     * generations younger than it will be collected. */
    Py_ssize_t n = 0;
    for (int i = NUM_GENERATIONS - 1; i >= 0; i--)
    {
        if (gcstate->generations[i].count > gcstate->generations[i].threshold)
        {
            /* Avoid quadratic performance degradation in number
            of tracked objects (see also issue #4074):

            To limit the cost of garbage collection, there are two strategies;
                - make each collection faster, e.g. by scanning fewer objects
                - do less collections
            This heuristic is about the latter strategy.

            In addition to the various configurable thresholds, we only trigger a
            full collection if the ratio

                long_lived_pending / long_lived_total

            is above a given value (hardwired to 25%).

            The reason is that, while "non-full" collections (i.e., collections of
            the young and middle generations) will always examine roughly the same
            number of objects -- determined by the aforementioned thresholds --,
            the cost of a full collection is proportional to the total number of
            long-lived objects, which is virtually unbounded.

            Indeed, it has been remarked that doing a full collection every
            <constant number> of object creations entails a dramatic performance
            degradation in workloads which consist in creating and storing lots of
            long-lived objects (e.g. building a large list of GC-tracked objects would
            show quadratic performance, instead of linear as expected: see issue #4074).

            Using the above ratio, instead, yields amortized linear performance in
            the total number of objects (the effect of which can be summarized
            thusly: "each full garbage collection is more and more costly as the
            number of objects grows, but we do fewer and fewer of them").

            This heuristic was suggested by Martin von Löwis on python-dev in
            June 2008. His original analysis and proposal can be found at:
            http://mail.python.org/pipermail/python-dev/2008-June/080579.html
            */
            if (i == NUM_GENERATIONS - 1 && gcstate->long_lived_pending < gcstate->long_lived_total / 4)
                continue;
            n = gc_collect_with_callback(tstate, i);
            break;
        }
    }
    return n;
}

#include "clinic/gcmodule.c.h"

/*[clinic input]
gc.enable

Enable automatic garbage collection.
[clinic start generated code]*/

static PyObject *
gc_enable_impl(PyObject *module)
/*[clinic end generated code: output=45a427e9dce9155c input=81ac4940ca579707]*/
{
    PyGC_Enable();
    Py_RETURN_NONE;
}

/*[clinic input]
gc.disable

Disable automatic garbage collection.
[clinic start generated code]*/

static PyObject *
gc_disable_impl(PyObject *module)
/*[clinic end generated code: output=97d1030f7aa9d279 input=8c2e5a14e800d83b]*/
{
    PyGC_Disable();
    Py_RETURN_NONE;
}

/*[clinic input]
gc.isenabled -> bool

Returns true if automatic garbage collection is enabled.
[clinic start generated code]*/

static int
gc_isenabled_impl(PyObject *module)
/*[clinic end generated code: output=1874298331c49130 input=30005e0422373b31]*/
{
    return PyGC_IsEnabled();
}

/*[clinic input]
gc.collect -> Py_ssize_t

    generation: int(c_default="NUM_GENERATIONS - 1") = 2

Run the garbage collector.

With no arguments, run a full collection.  The optional argument
may be an integer specifying which generation to collect.  A ValueError
is raised if the generation number is invalid.

The number of unreachable objects is returned.
[clinic start generated code]*/

static Py_ssize_t
gc_collect_impl(PyObject *module, int generation)
/*[clinic end generated code: output=b697e633043233c7 input=40720128b682d879]*/
{
    PyThreadState *tstate = _PyThreadState_GET();

    if (generation < 0 || generation >= NUM_GENERATIONS)
    {
        _PyErr_SetString(tstate, PyExc_ValueError, "invalid generation");
        return -1;
    }

    GCState *gcstate = &tstate->interp->gc;
    Py_ssize_t n;
    if (gcstate->collecting)
    {
        /* already collecting, don't do anything */
        n = 0;
    }
    else
    {
        gcstate->collecting = 1;
        n = gc_collect_with_callback(tstate, generation);
        gcstate->collecting = 0;
    }
    return n;
}

/*[clinic input]
gc.set_debug

    flags: int
        An integer that can have the following bits turned on:
        DEBUG_STATS - Print statistics during collection.
        DEBUG_COLLECTABLE - Print collectable objects found.
        DEBUG_UNCOLLECTABLE - Print unreachable but uncollectable objects
            found.
        DEBUG_SAVEALL - Save objects to gc.garbage rather than freeing them.
        DEBUG_LEAK - Debug leaking programs (everything but STATS).
    /

Set the garbage collection debugging flags.

Debugging information is written to sys.stderr.
[clinic start generated code]*/

static PyObject *
gc_set_debug_impl(PyObject *module, int flags)
/*[clinic end generated code: output=7c8366575486b228 input=5e5ce15e84fbed15]*/
{
    GCState *gcstate = get_gc_state();
    gcstate->debug = flags;
    Py_RETURN_NONE;
}

/*[clinic input]
gc.get_debug -> int

Get the garbage collection debugging flags.
[clinic start generated code]*/

static int
gc_get_debug_impl(PyObject *module)
/*[clinic end generated code: output=91242f3506cd1e50 input=91a101e1c3b98366]*/
{
    GCState *gcstate = get_gc_state();
    return gcstate->debug;
}

PyDoc_STRVAR(gc_set_thresh__doc__,
             "set_threshold(threshold0, [threshold1, threshold2]) -> None\n"
             "\n"
             "Sets the collection thresholds.  Setting threshold0 to zero disables\n"
             "collection.\n");

static PyObject *
gc_set_threshold(PyObject *self, PyObject *args)
{
    GCState *gcstate = get_gc_state();
    if (!PyArg_ParseTuple(args, "i|ii:set_threshold",
                          &gcstate->generations[0].threshold,
                          &gcstate->generations[1].threshold,
                          &gcstate->generations[2].threshold))
        return NULL;
    for (int i = 3; i < NUM_GENERATIONS; i++)
    {
        /* generations higher than 2 get the same threshold */
        gcstate->generations[i].threshold = gcstate->generations[2].threshold;
    }
    Py_RETURN_NONE;
}

/*[clinic input]
gc.get_threshold

Return the current collection thresholds.
[clinic start generated code]*/

static PyObject *
gc_get_threshold_impl(PyObject *module)
/*[clinic end generated code: output=7902bc9f41ecbbd8 input=286d79918034d6e6]*/
{
    GCState *gcstate = get_gc_state();
    return Py_BuildValue("(iii)",
                         gcstate->generations[0].threshold,
                         gcstate->generations[1].threshold,
                         gcstate->generations[2].threshold);
}

/*[clinic input]
gc.get_count

Return a three-tuple of the current collection counts.
[clinic start generated code]*/

static PyObject *
gc_get_count_impl(PyObject *module)
/*[clinic end generated code: output=354012e67b16398f input=a392794a08251751]*/
{
    GCState *gcstate = get_gc_state();
    return Py_BuildValue("(iii)",
                         gcstate->generations[0].count,
                         gcstate->generations[1].count,
                         gcstate->generations[2].count);
}

static int
referrersvisit(PyObject *obj, PyObject *objs)
{
    Py_ssize_t i;
    for (i = 0; i < PyTuple_GET_SIZE(objs); i++)
        if (PyTuple_GET_ITEM(objs, i) == obj)
            return 1;
    return 0;
}

static int
gc_referrers_for(PyObject *objs, PyGC_Head *list, PyObject *resultlist)
{
    PyGC_Head *gc;
    PyObject *obj;
    traverseproc traverse;
    for (gc = GC_NEXT(list); gc != list; gc = GC_NEXT(gc))
    {
        obj = FROM_GC(gc);
        traverse = Py_TYPE(obj)->tp_traverse;
        if (obj == objs || obj == resultlist)
            continue;
        if (traverse(obj, (visitproc)referrersvisit, objs))
        {
            if (PyList_Append(resultlist, obj) < 0)
                return 0; /* error */
        }
    }
    return 1; /* no error */
}

PyDoc_STRVAR(gc_get_referrers__doc__,
             "get_referrers(*objs) -> list\n\
    Return the list of objects that directly refer to any of objs.");

static PyObject *
gc_get_referrers(PyObject *self, PyObject *args)
{
    if (PySys_Audit("gc.get_referrers", "(O)", args) < 0)
    {
        return NULL;
    }

    PyObject *result = PyList_New(0);
    if (!result)
    {
        return NULL;
    }

    GCState *gcstate = get_gc_state();
    for (int i = 0; i < NUM_GENERATIONS; i++)
    {
        if (!(gc_referrers_for(args, GEN_HEAD(gcstate, i), result)))
        {
            Py_DECREF(result);
            return NULL;
        }
    }
    return result;
}

/* Append obj to list; return true if error (out of memory), false if OK. */
static int
referentsvisit(PyObject *obj, PyObject *list)
{
    // PyObject_Print(obj, stderr, 1);
    // fprintf(stderr, "\t from inner\n");
    return PyList_Append(list, obj) < 0;
}

PyDoc_STRVAR(gc_get_referents__doc__,
             "get_referents(*objs) -> list\n\
    Return the list of objects that are directly referred to by objs.");

// static PyObject *
gc_get_referents(PyObject *self, PyObject *args)
{
    Py_ssize_t i;
    if (PySys_Audit("gc.get_referents", "(O)", args) < 0)
    {
        return NULL;
    }
    PyObject *result = PyList_New(0);

    if (result == NULL)
        return NULL;

    for (i = 0; i < PyTuple_GET_SIZE(args); i++)
    {
        traverseproc traverse;
        PyObject *obj = PyTuple_GET_ITEM(args, i);

        if (!_PyObject_IS_GC(obj))
            continue;
        traverse = Py_TYPE(obj)->tp_traverse;
        if (!traverse)
            continue;
        if (traverse(obj, referentsvisit, result))
        {
            Py_DECREF(result);
            return NULL;
        }
    }
    return result;
}

// static PyObject *
// gc_get_referents(PyObject *self, PyObject *args)
// {
//     Py_ssize_t i;
//     if (PySys_Audit("gc.get_referents", "(O)", args) < 0)
//     {
//         return NULL;
//     }
//     PyObject *result = PyList_New(0);

//     if (result == NULL)
//         return NULL;

//     int ret;
//     for (i = 0; i < PyTuple_GET_SIZE(args); i++)
//     {
//         PyObject *obj = PyTuple_GET_ITEM(args, i);
//         unsigned int combined = 0;
//         inner_traversing(obj, &combined);
//         // unsigned int new_depth = (*combined >> 16) & 0xffff;
//         // fprintf(stderr, "cur_depth: %d\n", cur_depth);
//     }
//     // fprintf(stderr, "global live op size: %u\n", global_op_size);

//     return result;
//     // return NULL;
// }

/*[clinic input]
gc.get_objects
    generation: Py_ssize_t(accept={int, NoneType}, c_default="-1") = None
        Generation to extract the objects from.

Return a list of objects tracked by the collector (excluding the list returned).

If generation is not None, return only the objects tracked by the collector
that are in that generation.
[clinic start generated code]*/

static PyObject *
gc_get_objects_impl(PyObject *module, Py_ssize_t generation)
/*[clinic end generated code: output=48b35fea4ba6cb0e input=ef7da9df9806754c]*/
{
    PyThreadState *tstate = _PyThreadState_GET();
    int i;
    PyObject *result;
    GCState *gcstate = &tstate->interp->gc;

    if (PySys_Audit("gc.get_objects", "n", generation) < 0)
    {
        return NULL;
    }

    result = PyList_New(0);
    if (result == NULL)
    {
        return NULL;
    }

    /* If generation is passed, we extract only that generation */
    if (generation != -1)
    {
        if (generation >= NUM_GENERATIONS)
        {
            _PyErr_Format(tstate, PyExc_ValueError,
                          "generation parameter must be less than the number of "
                          "available generations (%i)",
                          NUM_GENERATIONS);
            goto error;
        }

        if (generation < 0)
        {
            _PyErr_SetString(tstate, PyExc_ValueError,
                             "generation parameter cannot be negative");
            goto error;
        }

        if (append_objects(result, GEN_HEAD(gcstate, generation)))
        {
            goto error;
        }

        return result;
    }

    /* If generation is not passed or None, get all objects from all generations */
    for (i = 0; i < NUM_GENERATIONS; i++)
    {
        if (append_objects(result, GEN_HEAD(gcstate, i)))
        {
            goto error;
        }
    }
    return result;

error:
    Py_DECREF(result);
    return NULL;
}

/*[clinic input]
gc.get_stats

Return a list of dictionaries containing per-generation statistics.
[clinic start generated code]*/

static PyObject *
gc_get_stats_impl(PyObject *module)
/*[clinic end generated code: output=a8ab1d8a5d26f3ab input=1ef4ed9d17b1a470]*/
{
    int i;
    struct gc_generation_stats stats[NUM_GENERATIONS], *st;

    /* To get consistent values despite allocations while constructing
    the result list, we use a snapshot of the running stats. */
    GCState *gcstate = get_gc_state();
    for (i = 0; i < NUM_GENERATIONS; i++)
    {
        stats[i] = gcstate->generation_stats[i];
    }

    PyObject *result = PyList_New(0);
    if (result == NULL)
        return NULL;

    for (i = 0; i < NUM_GENERATIONS; i++)
    {
        PyObject *dict;
        st = &stats[i];
        dict = Py_BuildValue("{snsnsn}",
                             "collections", st->collections,
                             "collected", st->collected,
                             "uncollectable", st->uncollectable);
        if (dict == NULL)
            goto error;
        if (PyList_Append(result, dict))
        {
            Py_DECREF(dict);
            goto error;
        }
        Py_DECREF(dict);
    }
    return result;

error:
    Py_XDECREF(result);
    return NULL;
}

/*[clinic input]
gc.is_tracked

    obj: object
    /

Returns true if the object is tracked by the garbage collector.

Simple atomic objects will return false.
[clinic start generated code]*/

static PyObject *
gc_is_tracked(PyObject *module, PyObject *obj)
/*[clinic end generated code: output=14f0103423b28e31 input=d83057f170ea2723]*/
{
    PyObject *result;

    if (_PyObject_IS_GC(obj) && _PyObject_GC_IS_TRACKED(obj))
        result = Py_True;
    else
        result = Py_False;
    return Py_NewRef(result);
}

/*[clinic input]
gc.is_finalized

    obj: object
    /

Returns true if the object has been already finalized by the GC.
[clinic start generated code]*/

static PyObject *
gc_is_finalized(PyObject *module, PyObject *obj)
/*[clinic end generated code: output=e1516ac119a918ed input=201d0c58f69ae390]*/
{
    if (_PyObject_IS_GC(obj) && _PyGCHead_FINALIZED(AS_GC(obj)))
    {
        Py_RETURN_TRUE;
    }
    Py_RETURN_FALSE;
}

/*[clinic input]
gc.freeze

Freeze all current tracked objects and ignore them for future collections.

This can be used before a POSIX fork() call to make the gc copy-on-write friendly.
Note: collection before a POSIX fork() call may free pages for future allocation
which can cause copy-on-write.
[clinic start generated code]*/

static PyObject *
gc_freeze_impl(PyObject *module)
/*[clinic end generated code: output=502159d9cdc4c139 input=b602b16ac5febbe5]*/
{
    GCState *gcstate = get_gc_state();
    for (int i = 0; i < NUM_GENERATIONS; ++i)
    {
        gc_list_merge(GEN_HEAD(gcstate, i), &gcstate->permanent_generation.head);
        gcstate->generations[i].count = 0;
    }
    Py_RETURN_NONE;
}

/*[clinic input]
gc.unfreeze

Unfreeze all objects in the permanent generation.

Put all objects in the permanent generation back into oldest generation.
[clinic start generated code]*/

static PyObject *
gc_unfreeze_impl(PyObject *module)
/*[clinic end generated code: output=1c15f2043b25e169 input=2dd52b170f4cef6c]*/
{
    GCState *gcstate = get_gc_state();
    gc_list_merge(&gcstate->permanent_generation.head,
                  GEN_HEAD(gcstate, NUM_GENERATIONS - 1));
    Py_RETURN_NONE;
}

/*[clinic input]
gc.get_freeze_count -> Py_ssize_t

Return the number of objects in the permanent generation.
[clinic start generated code]*/

static Py_ssize_t
gc_get_freeze_count_impl(PyObject *module)
/*[clinic end generated code: output=61cbd9f43aa032e1 input=45ffbc65cfe2a6ed]*/
{
    GCState *gcstate = get_gc_state();
    return gc_list_size(&gcstate->permanent_generation.head);
}

PyDoc_STRVAR(gc__doc__,
             "This module provides access to the garbage collector for reference cycles.\n"
             "\n"
             "enable() -- Enable automatic garbage collection.\n"
             "disable() -- Disable automatic garbage collection.\n"
             "isenabled() -- Returns true if automatic collection is enabled.\n"
             "collect() -- Do a full collection right now.\n"
             "get_count() -- Return the current collection counts.\n"
             "get_stats() -- Return list of dictionaries containing per-generation stats.\n"
             "set_debug() -- Set debugging flags.\n"
             "get_debug() -- Get debugging flags.\n"
             "set_threshold() -- Set the collection thresholds.\n"
             "get_threshold() -- Return the current the collection thresholds.\n"
             "get_objects() -- Return a list of all objects tracked by the collector.\n"
             "is_tracked() -- Returns true if a given object is tracked.\n"
             "is_finalized() -- Returns true if a given object has been already finalized.\n"
             "get_referrers() -- Return the list of objects that refer to an object.\n"
             "get_referents() -- Return the list of objects that an object refers to.\n"
             "freeze() -- Freeze all tracked objects and ignore them for future collections.\n"
             "unfreeze() -- Unfreeze all objects in the permanent generation.\n"
             "get_freeze_count() -- Return the number of objects in the permanent generation.\n");

static PyMethodDef GcMethods[] = {
    GC_ENABLE_METHODDEF
        GC_DISABLE_METHODDEF
            GC_ISENABLED_METHODDEF
                GC_SET_DEBUG_METHODDEF
                    GC_GET_DEBUG_METHODDEF
                        GC_GET_COUNT_METHODDEF{"set_threshold", gc_set_threshold, METH_VARARGS, gc_set_thresh__doc__},
    GC_GET_THRESHOLD_METHODDEF
        GC_COLLECT_METHODDEF
            GC_GET_OBJECTS_METHODDEF
                GC_GET_STATS_METHODDEF
                    GC_IS_TRACKED_METHODDEF
                        GC_IS_FINALIZED_METHODDEF{"get_referrers", gc_get_referrers, METH_VARARGS,
                                                  gc_get_referrers__doc__},
    {"get_referents", gc_get_referents, METH_VARARGS,
     gc_get_referents__doc__},
    GC_FREEZE_METHODDEF
        GC_UNFREEZE_METHODDEF
            GC_GET_FREEZE_COUNT_METHODDEF{NULL, NULL} /* Sentinel */
};

static int
gcmodule_exec(PyObject *module)
{
    GCState *gcstate = get_gc_state();

    /* garbage and callbacks are initialized by _PyGC_Init() early in
     * interpreter lifecycle. */
    assert(gcstate->garbage != NULL);
    if (PyModule_AddObjectRef(module, "garbage", gcstate->garbage) < 0)
    {
        return -1;
    }
    assert(gcstate->callbacks != NULL);
    if (PyModule_AddObjectRef(module, "callbacks", gcstate->callbacks) < 0)
    {
        return -1;
    }

#define ADD_INT(NAME)                                     \
    if (PyModule_AddIntConstant(module, #NAME, NAME) < 0) \
    {                                                     \
        return -1;                                        \
    }
    ADD_INT(DEBUG_STATS);
    ADD_INT(DEBUG_COLLECTABLE);
    ADD_INT(DEBUG_UNCOLLECTABLE);
    ADD_INT(DEBUG_SAVEALL);
    ADD_INT(DEBUG_LEAK);
#undef ADD_INT
    return 0;
}

static PyModuleDef_Slot gcmodule_slots[] = {
    {Py_mod_exec, gcmodule_exec},
    {Py_mod_multiple_interpreters, Py_MOD_PER_INTERPRETER_GIL_SUPPORTED},
    {0, NULL}};

static struct PyModuleDef gcmodule = {
    PyModuleDef_HEAD_INIT,
    .m_name = "gc",
    .m_doc = gc__doc__,
    .m_size = 0, // per interpreter state, see: get_gc_state()
    .m_methods = GcMethods,
    .m_slots = gcmodule_slots};

PyMODINIT_FUNC
PyInit_gc(void)
{
    return PyModuleDef_Init(&gcmodule);
}

/* C API for controlling the state of the garbage collector */
int PyGC_Enable(void)
{
    GCState *gcstate = get_gc_state();
    int old_state = gcstate->enabled;
    gcstate->enabled = 1;
    return old_state;
}

int PyGC_Disable(void)
{
    GCState *gcstate = get_gc_state();
    int old_state = gcstate->enabled;
    gcstate->enabled = 0;
    return old_state;
}

int PyGC_IsEnabled(void)
{
    GCState *gcstate = get_gc_state();
    return gcstate->enabled;
}

/* Public API to invoke gc.collect() from C */
Py_ssize_t
PyGC_Collect(void)
{
    PyThreadState *tstate = _PyThreadState_GET();
    GCState *gcstate = &tstate->interp->gc;

    if (!gcstate->enabled)
    {
        return 0;
    }

    Py_ssize_t n;
    if (gcstate->collecting)
    {
        /* already collecting, don't do anything */
        n = 0;
    }
    else
    {
        gcstate->collecting = 1;
        PyObject *exc = _PyErr_GetRaisedException(tstate);
        n = gc_collect_with_callback(tstate, NUM_GENERATIONS - 1);
        _PyErr_SetRaisedException(tstate, exc);
        gcstate->collecting = 0;
    }

    return n;
}

Py_ssize_t
_PyGC_CollectNoFail(PyThreadState *tstate)
{
    /* Ideally, this function is only called on interpreter shutdown,
    and therefore not recursively.  Unfortunately, when there are daemon
    threads, a daemon thread can start a cyclic garbage collection
    during interpreter shutdown (and then never finish it).
    See http://bugs.python.org/issue8713#msg195178 for an example.
    */
    GCState *gcstate = &tstate->interp->gc;
    if (gcstate->collecting)
    {
        return 0;
    }

    Py_ssize_t n;
    gcstate->collecting = 1;
    n = gc_collect_main(tstate, NUM_GENERATIONS - 1, NULL, NULL, 1);
    gcstate->collecting = 0;
    return n;
}

void _PyGC_DumpShutdownStats(PyInterpreterState *interp)
{
    GCState *gcstate = &interp->gc;
    if (!(gcstate->debug & DEBUG_SAVEALL) && gcstate->garbage != NULL && PyList_GET_SIZE(gcstate->garbage) > 0)
    {
        const char *message;
        if (gcstate->debug & DEBUG_UNCOLLECTABLE)
            message = "gc: %zd uncollectable objects at "
                      "shutdown";
        else
            message = "gc: %zd uncollectable objects at "
                      "shutdown; use gc.set_debug(gc.DEBUG_UNCOLLECTABLE) to list them";
        /* PyErr_WarnFormat does too many things and we are at shutdown,
        the warnings module's dependencies (e.g. linecache) may be gone
        already. */
        if (PyErr_WarnExplicitFormat(PyExc_ResourceWarning, "gc", 0,
                                     "gc", NULL, message,
                                     PyList_GET_SIZE(gcstate->garbage)))
            PyErr_WriteUnraisable(NULL);
        if (gcstate->debug & DEBUG_UNCOLLECTABLE)
        {
            PyObject *repr = NULL, *bytes = NULL;
            repr = PyObject_Repr(gcstate->garbage);
            if (!repr || !(bytes = PyUnicode_EncodeFSDefault(repr)))
                PyErr_WriteUnraisable(gcstate->garbage);
            else
            {
                PySys_WriteStderr(
                    "      %s\n",
                    PyBytes_AS_STRING(bytes));
            }
            Py_XDECREF(repr);
            Py_XDECREF(bytes);
        }
    }
}

void _PyGC_Fini(PyInterpreterState *interp)
{
    fprintf(stderr, "_PyGC_Fini called \n");
    GCState *gcstate = &interp->gc;
    Py_CLEAR(gcstate->garbage);
    Py_CLEAR(gcstate->callbacks);
    if (all_temps)
    {
        numa_free(all_temps, very_large_num_op * sizeof(OBJ_TEMP));
        all_temps = NULL;
    }

    /* We expect that none of this interpreters objects are shared
    with other interpreters.
    See https://github.com/python/cpython/issues/90228. */
}

/* for debugging */
void _PyGC_Dump(PyGC_Head *g)
{
    _PyObject_Dump(FROM_GC(g));
}

#ifdef Py_DEBUG
static int
visit_validate(PyObject *op, void *parent_raw)
{
    PyObject *parent = _PyObject_CAST(parent_raw);
    if (_PyObject_IsFreed(op))
    {
        _PyObject_ASSERT_FAILED_MSG(parent,
                                    "PyObject_GC_Track() object is not valid");
    }
    return 0;
}
#endif

/* extension modules might be compiled with GC support so these
functions must always be available */

void PyObject_GC_Track(void *op_raw)
{
    PyObject *op = _PyObject_CAST(op_raw);
    if (_PyObject_GC_IS_TRACKED(op))
    {
        _PyObject_ASSERT_FAILED_MSG(op,
                                    "object already tracked "
                                    "by the garbage collector");
    }
    _PyObject_GC_TRACK(op);

#ifdef Py_DEBUG
    /* Check that the object is valid: validate objects traversed
    by tp_traverse() */
    traverseproc traverse = Py_TYPE(op)->tp_traverse;
    (void)traverse(op, visit_validate, op);
#endif
}

void PyObject_GC_UnTrack(void *op_raw)
{
    PyObject *op = _PyObject_CAST(op_raw);
    /* Obscure:  the Py_TRASHCAN mechanism requires that we be able to
     * call PyObject_GC_UnTrack twice on an object.
     */
    if (_PyObject_GC_IS_TRACKED(op))
    {
        _PyObject_GC_UNTRACK(op);
    }
}

int PyObject_IS_GC(PyObject *obj)
{
    return _PyObject_IS_GC(obj);
}

void _Py_ScheduleGC(PyInterpreterState *interp)
{
    GCState *gcstate = &interp->gc;
    if (gcstate->collecting == 1)
    {
        return;
    }
    struct _ceval_state *ceval = &interp->ceval;
    if (!_Py_atomic_load_relaxed(&ceval->gc_scheduled))
    {
        _Py_atomic_store_relaxed(&ceval->gc_scheduled, 1);
        _Py_atomic_store_relaxed(&ceval->eval_breaker, 1);
    }
}

void _PyObject_GC_Link(PyObject *op)
{
    PyGC_Head *g = AS_GC(op);
    assert(((uintptr_t)g & (sizeof(uintptr_t) - 1)) == 0); // g must be correctly aligned

    PyThreadState *tstate = _PyThreadState_GET();
    GCState *gcstate = &tstate->interp->gc;
    g->_gc_next = 0;
    g->_gc_prev = 0;
    gcstate->generations[0].count++; /* number of allocated GC objects */
    // fprintf(stderr, "GC trying to schedule\n"); // TODO, determine whether to schedule GC depends on number of recently scheduled
    // if (enable_bk)
    global_try2_sched++;
    if (gcstate->generations[0].count > gcstate->generations[0].threshold &&
        gcstate->enabled &&
        gcstate->generations[0].threshold &&
        !gcstate->collecting &&
        !_PyErr_Occurred(tstate))
    {
        _Py_ScheduleGC(tstate->interp);
    }
}

void _Py_RunGC(PyThreadState *tstate)
{
    GCState *gcstate = &tstate->interp->gc;
    gcstate->collecting = 1;
    gc_collect_generations(tstate);
    gcstate->collecting = 0;
}

static PyObject *
gc_alloc(size_t basicsize, size_t presize)
{
    PyThreadState *tstate = _PyThreadState_GET();
    if (basicsize > PY_SSIZE_T_MAX - presize)
    {
        return _PyErr_NoMemory(tstate);
    }
    size_t size = presize + basicsize;
    char *mem = PyObject_Malloc(size);
    if (mem == NULL)
    {
        return _PyErr_NoMemory(tstate);
    }
    ((PyObject **)mem)[0] = NULL;
    ((PyObject **)mem)[1] = NULL;
    PyObject *op = (PyObject *)(mem + presize);
    _PyObject_GC_Link(op);
    return op;
}

PyObject *
_PyObject_GC_New(PyTypeObject *tp)
{
    size_t presize = _PyType_PreHeaderSize(tp);
    PyObject *op = gc_alloc(_PyObject_SIZE(tp), presize);
    if (op == NULL)
    {
        return NULL;
    }
    _PyObject_Init(op, tp);
    return op;
}

PyVarObject *
_PyObject_GC_NewVar(PyTypeObject *tp, Py_ssize_t nitems)
{
    PyVarObject *op;

    if (nitems < 0)
    {
        PyErr_BadInternalCall();
        return NULL;
    }
    size_t presize = _PyType_PreHeaderSize(tp);
    size_t size = _PyObject_VAR_SIZE(tp, nitems);
    op = (PyVarObject *)gc_alloc(size, presize);
    if (op == NULL)
    {
        return NULL;
    }
    _PyObject_InitVar(op, tp, nitems);
    return op;
}

PyObject *
PyUnstable_Object_GC_NewWithExtraData(PyTypeObject *tp, size_t extra_size)
{
    size_t presize = _PyType_PreHeaderSize(tp);
    PyObject *op = gc_alloc(_PyObject_SIZE(tp) + extra_size, presize);
    if (op == NULL)
    {
        return NULL;
    }
    memset(op, 0, _PyObject_SIZE(tp) + extra_size);
    _PyObject_Init(op, tp);
    return op;
}

PyVarObject *
_PyObject_GC_Resize(PyVarObject *op, Py_ssize_t nitems)
{
    const size_t basicsize = _PyObject_VAR_SIZE(Py_TYPE(op), nitems);
    const size_t presize = _PyType_PreHeaderSize(((PyObject *)op)->ob_type);
    _PyObject_ASSERT((PyObject *)op, !_PyObject_GC_IS_TRACKED(op));
    if (basicsize > (size_t)PY_SSIZE_T_MAX - presize)
    {
        return (PyVarObject *)PyErr_NoMemory();
    }
    char *mem = (char *)op - presize;
    mem = (char *)PyObject_Realloc(mem, presize + basicsize);
    if (mem == NULL)
    {
        return (PyVarObject *)PyErr_NoMemory();
    }
    op = (PyVarObject *)(mem + presize);
    Py_SET_SIZE(op, nitems);
    return op;
}

void PyObject_GC_Del(void *op)
{
    size_t presize = _PyType_PreHeaderSize(((PyObject *)op)->ob_type);
    PyGC_Head *g = AS_GC(op);
    if (_PyObject_GC_IS_TRACKED(op))
    {
#ifdef Py_DEBUG
        if (PyErr_WarnExplicitFormat(PyExc_ResourceWarning, "gc", 0,
                                     "gc", NULL, "Object of type %s is not untracked before destruction",
                                     ((PyObject *)op)->ob_type->tp_name))
        {
            PyErr_WriteUnraisable(NULL);
        }
#endif
        gc_list_remove(g);
    }
    GCState *gcstate = get_gc_state();
    if (gcstate->generations[0].count > 0)
    {
        gcstate->generations[0].count--;
    }
    PyObject_Free(((char *)op) - presize);
}

int PyObject_GC_IsTracked(PyObject *obj)
{
    if (_PyObject_IS_GC(obj) && _PyObject_GC_IS_TRACKED(obj))
    {
        return 1;
    }
    return 0;
}

int PyObject_GC_IsFinalized(PyObject *obj)
{
    if (_PyObject_IS_GC(obj) && _PyGCHead_FINALIZED(AS_GC(obj)))
    {
        return 1;
    }
    return 0;
}

void PyUnstable_GC_VisitObjects(gcvisitobjects_t callback, void *arg)
{
    size_t i;
    GCState *gcstate = get_gc_state();
    int origenstate = gcstate->enabled;
    gcstate->enabled = 0;
    for (i = 0; i < NUM_GENERATIONS; i++)
    {
        PyGC_Head *gc_list, *gc;
        gc_list = GEN_HEAD(gcstate, i);
        for (gc = GC_NEXT(gc_list); gc != gc_list; gc = GC_NEXT(gc))
        {
            PyObject *op = FROM_GC(gc);
            Py_INCREF(op);
            int res = callback(op, arg);
            Py_DECREF(op);
            if (!res)
            {
                goto done;
            }
        }
    }
done:
    gcstate->enabled = origenstate;
}

static int cascadingvisitor(PyObject *inner_op, unsigned long *combined)
{
    // if (check_in_set((uintptr_t)inner_op))
    // if (found_in_local_kset(inner_op))
    if (check_in_global((uintptr_t)inner_op))
    // if (check_in_map((uintptr_t)inner_op))
    // if (found_in_kset_helper(inner_op))
    {
        return 0;
    }

    // *combined += 1; // increase length, stop while traversing
    // unsigned int extracted_len = *combined & 0xFFFFFFFF;
    // if (extracted_len > LEN_THRESHOLD) //
    // {
    //     // max_length = extracted_len;
    //     return;
    // }

    insert_into_global((uintptr_t)inner_op);
    // insert_into_map((uintptr_t)inner_op, 0);
    // insert_global_set_helper(inner_op);
    kv_push(PyObject *, local_ptr_vec, inner_op); // vector, dynamic resizing
    // inner_traversing(inner_op, combined); // for testing gc.get_referents()
    update_recursive_visitor(inner_op, combined); // for real
    return 0;
}
void inner_traversing(PyObject *each_op, unsigned int *combined)
{
    if (!each_op || !_PyObject_IS_GC(each_op))
    {
        return;
    }
    traverseproc traverse = Py_TYPE(each_op)->tp_traverse;
    if (!traverse)
        return;

    // unsigned int new_len = 0;
    // new_len |= (*combined << 16);

    unsigned int last_length = *combined & 0xFFFF;
    *combined &= 0xFFFF0000; // reset the lower 2 bytes (lengths), this is needed
    // fprintf(stderr, "last length preserved: %u\n", last_length);

    *combined += (1 << 16); // increase depths
    unsigned int extractedDepth = (*combined >> 16);
    fprintf(stderr, "depth: %u\n", extractedDepth);

    traverse(each_op, (visitproc)cascadingvisitor, combined);
    *combined = (*combined & 0xFFFF0000) | last_length;
    // set length to last_length
}

void update_recursive_visitor(PyObject *each_op, unsigned long *combined)
{
    if (early_return)
        return;
    if (!each_op)
    {
        return;
    }
    if (_Py_IsImmortal(each_op))
    {
        return;
    }

    PyTypeObject *t = Py_TYPE(each_op);
    if (!t->tp_iter || !t->tp_repr)
        return;
    if (!_PyObject_IS_GC(each_op))
        return;
    traverseproc traverse;
    traverse = Py_TYPE(each_op)->tp_traverse;
    if (!traverse)
        return;
    // {
    // unsigned int last_length = *combined & 0xFFFFFFFF;
    // *combined &= 0xFFFFFFFF00000000; // reset the lower 2 bytes (lengths), this is needed
    // *combined += ((uint64_t)1 << 32);
    //     unsigned int extractedDepth = (*combined >> 32);
    //     if (extractedDepth > DEPTH_THRESHOLD) //
    //     {
    //         // max_depth = extractedDepth;
    //         return;
    //     }
    // }
#ifdef EARLY_CUTOFF
    if (++cutoff_counter % 20 == 0)
    {
        clock_gettime(CLOCK_MONOTONIC, &cutoff_current);
        double elapsed_ = (cutoff_current.tv_sec - cutoff_start.tv_sec) + (cutoff_current.tv_nsec - cutoff_start.tv_nsec) / 1.0e9;
        if (elapsed_ > cutoff_limit)
        {
            // cutoff_limit *= 2;
            fprintf(stderr, "Early stop, elapsed_: %.3f, counter: %d, cutoff_limit update: %.3f\n", elapsed_, cutoff_counter, cutoff_limit);
            early_return = true;
        }
    }
#endif
    traverse(each_op, (visitproc)cascadingvisitor, combined);
    // *combined = (*combined & 0xFFFFFFFF00000000) | last_length;
}
unsigned long max_num_hot = 0; // accumulated hot objs for 10 fast cycles
double cur_hot_in_all = 0.0;   // current ratio of changed op within old_num_op
unsigned int zero_hot_num = 0;

void get_mlr_hotness_C()
{
    for (int i = 0; i < old_num_op; i++)
    {
        double sum = 0;
        double sum_squared_diff = 0;
        int non_zero_count = 0;
        int smaller_than_127_count = 0;
        int min = all_temps[i].diffs[0];
        int max = all_temps[i].diffs[0];
        for (int j = 0; j < NUM_SLOTS - 1; j++)
        {
            uint8_t value = all_temps[i].diffs[j];
            sum += value;

            if (value != 0)
                non_zero_count++;

            if (value < 127)
                smaller_than_127_count++;
            if (all_temps[i].diffs[j] < min)
            {
                min = all_temps[i].diffs[j];
            }
            if (all_temps[i].diffs[j] > max)
            {
                max = all_temps[i].diffs[j];
            }
        }
        double average = sum / NUM_SLOTS;

        for (int j = 0; j < NUM_SLOTS - 1; j++)
        {
            uint8_t value = all_temps[i].diffs[j];
            sum_squared_diff += (value - average) * (value - average);
        }

        double variance = sum_squared_diff / NUM_SLOTS;
        double std_dev = sqrt(variance);
        int range = max - min;

        int infered_hotness = (int)(INTERCEPT_HOT + AVG_COEFF * average + STDDEV_COEFF * std_dev +
                                    NON_ZERO_COEFF * non_zero_count + SMALL_127_COEFF * smaller_than_127_count +
                                    RANGE_COEFF * range);
        if (infered_hotness > 127) // max value for uint8_t 's 7 LSB, since MSB is used for dropout
            infered_hotness = 127;
        all_temps[i].diffs[NUM_SLOTS - 1] = (uint8_t)infered_hotness; // TODO, if later wants to remain drop_off, this must be masked only 7 LSB
    }
}

short get_mlr_hotness_C_per_obj(int i)
{
    double sum = 0;
    double sum_squared_diff = 0;
    int non_zero_count = 0;
    int smaller_than_127_count = 0;
    int min = all_temps[i].diffs[0];
    int max = all_temps[i].diffs[0];

    for (int j = 0; j < NUM_SLOTS - 1; j++)
    {
        uint8_t value = all_temps[i].diffs[j];
        sum += value;

        if (value != 0)
            non_zero_count++;

        if (value < 127)
            smaller_than_127_count++;

        if (value < min)
            min = value;

        if (value > max)
            max = value;
    }

    double average = sum / (NUM_SLOTS - 1);
    for (int j = 0; j < NUM_SLOTS - 1; j++)
    {
        uint8_t value = all_temps[i].diffs[j];
        sum_squared_diff += (value - average) * (value - average);
    }

    double variance = sum_squared_diff / (NUM_SLOTS - 1);
    double std_dev = sqrt(variance);

    int range = max - min;

    int infered_hotness = (int)(INTERCEPT_HOT + AVG_COEFF * average +
                                STDDEV_COEFF * std_dev +
                                NON_ZERO_COEFF * non_zero_count +
                                SMALL_127_COEFF * smaller_than_127_count +
                                RANGE_COEFF * range);

    if (infered_hotness > 127)
        infered_hotness = 127;

    if (sum != 0)
        cur_fast_num_hot++;

    return (short)infered_hotness;
}

int check_in_global_helper(uintptr_t op)
{
    if (1)
    {
        return check_in_global(op);
        // return check_in_map(op);
        // return found_in_kset_helper((PyObject *)op);
    }
    else
    {
        return 1;
    }
}

#define get_growth(op) (op->ob_refcnt_split[PY_LITTLE_ENDIAN])

void record_temp(int scan_idx, unsigned int start_idx, unsigned int end_idx)
{
    fprintf(stderr, "scan_idx: %d, sampling from: %u, to: %u\n", scan_idx, start_idx, end_idx);
    // int prev_scan_idx = (scan_idx == 0) ? (NUM_SLOTS - 2) : (scan_idx - 1);
    // fprintf(stderr, "prev_scan_idx: %d, cur scan_idx: %d\n", prev_scan_idx, scan_idx);
    for (int i = start_idx; i < end_idx; i++)
    {
        if (all_temps[i].diffs[NUM_SLOTS - 1] & (1 << DROP_OUT_OFF))
        {
            continue;
        }
        if (sigsetjmp(jump_buffer, 1) == 0)
        {
            // uint8_t diff = (abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt) >= 127) ? 127 : (uint8_t)abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt);
            // all_temps[i].diffs[scan_idx] = (abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt) >= 127) ? 127 : (uint8_t)abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt);

            int current_growth = get_growth(all_temps[i].op);
            int growth = abs(current_growth - all_temps[i].prev_refcnt);
            all_temps[i].diffs[scan_idx] = (uint8_t)((growth >= 127) ? 127 : growth);
            all_temps[i].prev_refcnt = current_growth;
        }
        else
        {
            all_temps[i].diffs[NUM_SLOTS - 1] |= (1 << DROP_OUT_OFF); // segfualt occured, mark it as drop out
            not_in_global_set++;
        }
    }
}

extern volatile short terminate_flag_refchain;

void swap(OBJ_TEMP *a, OBJ_TEMP *b)
{
    OBJ_TEMP temp = *a;
    *a = *b;
    *b = temp;
}

// Dutch National Flag Algorithm, 3-way partitioning [0: low]: cold, [low: mid]: warm, [mid: old_num_op]: hot
// void sort_dnf(int *low, int *mid, int *high)
// {
//     // fprintf(stderr, "before low: %d, mid: %d, high: %d\n", *low, *mid, *high);
//     while (*mid <= *high)
//     {
//         if ((all_temps[*mid].diff & HOTNESS_MASK) < 1)
//         {
//             swap(&all_temps[*low], &all_temps[*mid]);
//             (*low)++;
//             (*mid)++;
//         }
//         else if ((all_temps[*mid].diff & HOTNESS_MASK) < 7) // doesn't matter since we are not using
//         {
//             (*mid)++;
//         }
//         else
//         {
//             swap(&all_temps[*mid], &all_temps[*high]);
//             (*high)--;
//         }
//     }
//     fprintf(stderr, "after low: %d, mid: %d, high: %d, all: %d\n", *low, *mid, *high, old_num_op);
// }

double do_migration(void **pages, int num_pages, int dest_node)
{
    int *nodes = calloc(num_pages, sizeof(int));
    // int *nodes = numa_alloc_onnode(num_pages * sizeof(int), 0);
    int *status = calloc(num_pages, sizeof(int));
    // int *status = numa_alloc_onnode(num_pages * sizeof(int), 0);
    // memset(status, 0, num_pages * sizeof(int));
    if (dest_node == 0)
    {
        // promotion, to DRAM
        fprintf(stderr, "doing promotion\n");
        for (int i = 0; i < num_pages; i++)
        {
            nodes[i] = DRAM_MASK; // DRAM
        }
    }
    else
    {
        // demotion, to CXL
        fprintf(stderr, "doing demotion\n");
        for (int i = 0; i < num_pages; i++)
        {
            nodes[i] = CXL_MASK; // CXL
        }
    }
    struct timespec start, end;
    double elapsed = 0;
    clock_gettime(CLOCK_MONOTONIC, &start);

    long ret = move_pages(0, num_pages, pages, nodes, status, MPOL_MF_MOVE);

    clock_gettime(CLOCK_MONOTONIC, &end);
    elapsed = end.tv_sec - start.tv_sec;
    elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;

    int not_moved = 0;
    for (int i = 0; i < num_pages; ++i)
    {
        if (status[i] != dest_node)
        {
            not_moved++;
        }
    }
    fprintf(stderr, "not_moved: %d\n", not_moved);
    // populate page location here
    for (int i = 0; i < num_pages; i++)
    {
        // set_location_pages((uintptr_t)pages[i], dest_node);
        set_location_pages_bkt((uintptr_t)pages[i], dest_node);
    }
    free(pages);
    free(nodes);
    free(status);
    // numa_free(pages, num_pages * sizeof(void *));
    // numa_free(nodes, num_pages * sizeof(int));
    // numa_free(status, num_pages * sizeof(int));
    return elapsed;
}

typedef struct
{
    void *pageAddress;
    int count;
} PageCount;
int comparePageCount(const void *a, const void *b)
{
    return ((PageCount *)b)->count - ((PageCount *)a)->count;
}

bool is_page_aligned(void *addr)
{
    size_t page_size = sysconf(_SC_PAGESIZE);
    return ((size_t)addr % page_size) == 0;
}

double align_obj_2_page_bd_revised(unsigned int start_idx, unsigned int end_idx)
{
    double elapsed = 0;
    struct timespec start, end;
    assert(end_idx != 0);
    int in_dram = 0, in_cxl = 0;
    if (very_first_mig)
    {
        void **pages_arr = calloc(old_num_op, sizeof(void *));
        int *status_arr = calloc(old_num_op, sizeof(int));
        for (int i = 0; i < old_num_op; i++)
        {
            // pages_arr[i] = (void *)all_temps[i].op;
            pages_arr[i] = (void *)((uintptr_t)all_temps[i].op & PAGE_MASK);
            if (!is_page_aligned(pages_arr[i]))
                fprintf(stderr, "unlikely! not aligned\n");
        }

        clock_gettime(CLOCK_MONOTONIC, &start);
        int ret = move_pages(0, old_num_op, pages_arr, NULL, status_arr, 0); // see where the pages are
        clock_gettime(CLOCK_MONOTONIC, &end);
        elapsed = end.tv_sec - start.tv_sec;
        elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;

        if (ret != 0)
        {
            perror("move_pages failed");
            free(pages_arr);
            free(status_arr);
            return;
        }
        for (unsigned int i = 0; i < old_num_op; i++)
        {
            if (1)
            { // for debugging
                if (status_arr[i] == 0)
                    in_dram++;
                else if (status_arr[i] == 1)
                    in_cxl++;
                else if (status_arr[i] < 0)
                    fprintf(stderr, "unlikely, failed\n");
            }
            // short cur_op_hotness = all_temps[i].diffs[NUM_SLOTS - 1] & HOTNESS_MASK;
            short cur_op_hotness = get_mlr_hotness_C_per_obj(i);
            // insert_into_pages((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, (bool)status_arr[i]);
            insert_into_bucket((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, (bool)status_arr[i], 0);
        }
        free(pages_arr);
        free(status_arr);
    }
    else if (reset_all_temps == 0)
    {
        for (unsigned int i = 0; i < old_num_op; i++)
        {
            // short cur_op_hotness = all_temps[i].diffs[NUM_SLOTS - 1] & HOTNESS_MASK;
            short cur_op_hotness = get_mlr_hotness_C_per_obj(i);
            // insert_into_pages_only_exists((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness);
            insert_into_bucket((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, 0, 1);
        }
    }
    else if (reset_all_temps == 2)
    {
        for (unsigned int i = 0; i < prev_num_op; i++)
        {
            // short cur_op_hotness = all_temps[i].diffs[NUM_SLOTS - 1] & HOTNESS_MASK;
            short cur_op_hotness = get_mlr_hotness_C_per_obj(i);
            // insert_into_pages_only_exists((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness);
            insert_into_bucket((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, 0, 1);
        }
        int new_op_num = old_num_op - prev_num_op;
        assert(new_op_num > 0);
        void **pages_arr = calloc(new_op_num, sizeof(void *));
        int *status_arr = calloc(new_op_num, sizeof(int));
        for (int i = 0; i < new_op_num; i++)
        {
            // pages_arr[i] = (void *)all_temps[i + prev_num_op].op;
            pages_arr[i] = (void *)((uintptr_t)all_temps[i + prev_num_op].op & PAGE_MASK);
            if (!is_page_aligned(pages_arr[i]))
                fprintf(stderr, "unlikly! not aligned\n");
        }

        clock_gettime(CLOCK_MONOTONIC, &start);
        int ret = move_pages(0, new_op_num, pages_arr, NULL, status_arr, 0);
        clock_gettime(CLOCK_MONOTONIC, &end);
        elapsed = end.tv_sec - start.tv_sec;
        elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
        if (ret != 0)
        {
            perror("move_pages failed");
            free(pages_arr);
            free(status_arr);
            return;
        }
        for (int i = 0; i < new_op_num; i++)
        {
            { // for debugging
                if (status_arr[i] == 0)
                    in_dram++;
                else if (status_arr[i] == 1)
                    in_cxl++;
                else if (status_arr[i] < 0)
                    fprintf(stderr, "unlikely, failed\n");
            }
        }
        for (unsigned int i = prev_num_op; i < old_num_op; i++)
        {
            // short cur_op_hotness = all_temps[i].diffs[NUM_SLOTS - 1] & HOTNESS_MASK;
            short cur_op_hotness = get_mlr_hotness_C_per_obj(i);
            // insert_into_pages((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, (bool)status_arr[i - prev_num_op]);
            insert_into_bucket((uintptr_t)all_temps[i].op & PAGE_MASK, cur_op_hotness, (bool)status_arr[i - prev_num_op], 0);
        }
        free(pages_arr);
        free(status_arr);
    }
    else if (reset_all_temps == 1) // all_temps reformed, should happen only for non-first scan && div > 1.15
    {
        fprintf(stderr, "UNLIKELY!!! op set changed extensively? Check once!\n");
    }
    fprintf(stderr, "dram_num: %d, cxl_num: %d\n", in_dram, in_cxl);
    return elapsed;
}

bool is_old_num_remain_still()
{
    double one_percent_diff_flunc = 0.01 * prev_num_op;
    double low = prev_num_op - one_percent_diff_flunc;
    double high = prev_num_op + one_percent_diff_flunc;
    if (old_num_op >= low && old_num_op <= high)
    {
        fprintf(stderr, "old_num_op not changed too much");
        return true;
    }
}

bool check8MSB(uintptr_t ptr)
{
    uintptr_t mask = 0xFF0000000000;
    // return ((ptr & mask) >> ((sizeof(void *) * 8) - 8)) == 0x7F;
    return ((ptr & mask) >> 40) == 0x7F;
}

// sets the mo
uintptr_t combine_op_hotness(uintptr_t value, uint8_t hotness)
{
    uintptr_t mask = 0x00FFFFFFFFFF;
    uintptr_t clearedValue = value & mask;
    uintptr_t newValue = ((uintptr_t)hotness) << 40;
    return clearedValue | newValue;
}

int count_duplicates(void **arr1, int size1, void **arr2, int size2)
{
    int duplicates = 0;

    for (int i = 0; i < size1; i++)
    {
        for (int j = 0; j < size2; j++)
        {
            if (arr1[i] == arr2[j])
            {
                duplicates++;
                break;
            }
        }
    }
    return duplicates;
}
int check_dram_free()
{
    long long free_dram_size;
    if (numa_node_size(DRAM_MASK, &free_dram_size) <= 0)
    {
        fprintf(stderr, "Failed to get DRAM size");
        return -1;
    }
    long long free_dram_size_mb = free_dram_size / 1048576; // Convert bytes to MB
    // free_dram_size_mb = (free_dram_size_mb > RESERVED_MEMORY_MB) ? free_dram_size_mb - RESERVED_MEMORY_MB : 0;
    int dram_free = (int)free_dram_size_mb;
    fprintf("dram size is currently: %d\n", dram_free);
    return dram_free;
}
void get_rss_ratio(int *dram_percent, int *cxl_percent)
{
    FILE *numa_maps;
    char line[1024];

    numa_maps = fopen("/proc/self/numa_maps", "r");
    if (!numa_maps)
    {
        perror("Error opening /proc/self/numa_maps");
    }
    int pages_in_node_0 = 0, pages_in_node_1 = 0;
    while (fgets(line, sizeof(line), numa_maps))
    {
        if (strstr(line, "anon") != NULL)
        {
            int node0 = 0, node1 = 0;
            char *token = strtok(line, " ");
            while (token != NULL)
            {
                if (sscanf(token, "N0=%d", &node0) == 1)
                {
                    pages_in_node_0 += node0;
                }
                if (sscanf(token, "N1=%d", &node1) == 1)
                {
                    pages_in_node_1 += node1;
                }
                token = strtok(NULL, " ");
            }
        }
    }
    fclose(numa_maps);
    int total_pages = pages_in_node_0 + pages_in_node_1;
    if (total_pages == 0)
    {
        printf("No pages found in node 0 or node 1.\n");
    }
    pages_in_node_0 -= (very_large_num_op * sizeof(OBJ_TEMP)) / PAGE_SIZE;
    if (pages_in_node_0 <= 0)
        pages_in_node_0 = 0;
    *dram_percent = (int)((pages_in_node_0 * 100.0) / total_pages);
    // *cxl_percent = (int)((pages_in_node_1 * 100.0) / total_pages);
    *cxl_percent = 100 - *dram_percent;
}

void *parse_llc_miss_bw_routine(void *args)
{
    while (!terminate_flag_refchain)
    {
        FILE *file1 = fopen(perf_stat_full_path, "r");
        FILE *file2 = fopen(bw_full_path, "r");

        if (file1 == NULL || file2 == NULL)
        {
            perror("Unable to open file");
            sleep(2);
            continue;
        }
        llc_load_miss_percent = 0.0;
        cxl_bw = 0.0;

        // parse llc miss file
        while (fgets(llc_line, sizeof(llc_line), file1))
        {
            if (strstr(llc_line, "LLC-load-misses") != NULL)
            {
                sscanf(llc_line, "%*[^#]# %lf%%", &llc_load_miss_percent);
                break;
            }
        }
        fclose(file1);
        if (llc_load_miss_percent == 0.0)
        {
            fprintf(stderr, "error, LLC-load-misses percentage not found.\n");
        }

        // parse bw file
        if (fgets(bw_line, sizeof(bw_line), file2) != NULL)
        {
            sscanf(bw_line, "%lf %lf", &dram_bw, &cxl_bw);
            if (sscanf(bw_line, "%lf %lf", &dram_bw, &cxl_bw) == 2)
            {
                // fprintf(stderr, "dram_bw = %.2lf, cxl_bw = %.2lf\n", dram_bw, cxl_bw);
            }
            else
            {
                fprintf(stderr, "Failed to parse the line: %s\n", bw_line);
            }
        }
        else
        {
            fprintf(stderr, "Error reading the first line of bw file.\n");
        }
        fclose(file2);

        if (llc_load_miss_percent < 1e-9 || cxl_bw < 1e-9)
        {
            fprintf(stderr, "no data yet, wait till next loop\n");
            sleep(1);
            continue;
        }

        int num_non_zero_llc_miss = 0;
        int num_non_zero_bw = 0;
        double total_llc_miss = 0.0;
        double total_cxl_bw = 0.0;
        for (int i = 0; i < buffer_size; i++)
        {
            if (llc_miss_arr[i] != 0.0)
            {
                total_llc_miss += llc_miss_arr[i];
                num_non_zero_llc_miss++;
            }
            if (cxl_bw_arr[i] != 0.0)
            {
                total_cxl_bw += cxl_bw_arr[i];
                num_non_zero_bw++;
            }
        }
        // before new data comes, calculate average
        avg_llc_miss = (num_non_zero_llc_miss > 0) ? (total_llc_miss / num_non_zero_llc_miss) : 0.0;
        avg_cxl_bw = (num_non_zero_bw > 0) ? (total_cxl_bw / num_non_zero_bw) : 0.0;

        llc_miss_arr[buffer_index] = llc_load_miss_percent;
        cxl_bw_arr[buffer_index] = cxl_bw;
        buffer_index = (buffer_index + 1) % buffer_size;
        // if(llc_load_miss_percent >> avg_llc_miss) // do something

        // printing
        // for (int i = 0; i < buffer_size; i++)
        // {
        //     fprintf(stderr, "%.2lf ", llc_miss_arr[i]);
        // }
        // fprintf(stderr, "\n");
        // for (int i = 0; i < buffer_size; i++)
        // {
        //     fprintf(stderr, "%.2lf ", cxl_bw_arr[i]);
        // }
        // fprintf(stderr, "\n");
        // fprintf(stderr, "buffer_index: %d, num_non_zero: %d, avg llc miss: %.2lf, avg cxl bw: %.2lf\n", buffer_index, num_non_zero_llc_miss, avg_llc_miss, avg_cxl_bw);
        // fprintf(stderr, "\n");
        sleep(1);
        // struct timespec req;
        // req.tv_sec = 1;
        // req.tv_nsec = 200000000L;
        // nanosleep(&req, NULL);
    }
    return NULL;
}

double calculate_averaged_eagerness(double arr[])
{
    // fprintf(stderr, "origin:\n");
    // for (int i = 0; i < buffer_size; i++)
    // {
    //     fprintf(stderr, "%.2lf ", arr[i]);
    // }
    // fprintf(stderr, "\n");
    double total_sum = 0.0;
    double total_sum_squares = 0.0;
    double extents[buffer_size];

    // Step 1: Precompute the total sum and sum of squares of all elements
    for (int i = 0; i < buffer_size; i++)
    {
        total_sum += arr[i];
        total_sum_squares += arr[i] * arr[i];
    }

    // Step 2: Compute the changing extent for each element and store it
    double min_extent = DBL_MAX;
    double max_extent = DBL_MIN;

    for (int i = 0; i < buffer_size; i++)
    {
        // Sum and sum of squares excluding arr[i]
        double sum_others = total_sum - arr[i];
        double sum_squares_others = total_sum_squares - (arr[i] * arr[i]);

        int count_others = buffer_size - 1;

        // Calculate avg_others and stddev_others
        double avg_others = sum_others / count_others;
        double variance_others = (sum_squares_others / count_others) - (avg_others * avg_others);
        double stddev_others = sqrt(variance_others);

        double changing_extent = 0.0;
        if (stddev_others > 1e-9)
        {
            double numerator = arr[i] - avg_others;
            if (numerator <= 0)
                changing_extent = 0;
            else
            {
                changing_extent = numerator / stddev_others;
            }
            // fprintf(stderr, "arr[i]: %.2lf, avg_others: %.2lf, numerator: %.2lf, stddev_others: %.2lf\n", arr[i], avg_others, numerator, stddev_others);
        }

        extents[i] = changing_extent;

        // Update the min and max changing extents
        if (changing_extent < min_extent)
        {
            min_extent = changing_extent;
        }
        if (changing_extent > max_extent)
        {
            max_extent = changing_extent;
        }
    }

    // Step 3: Normalize the changing extents to the range 0 to 1
    double normalized_extents[buffer_size];
    if (max_extent > min_extent)
    {
        for (int i = 0; i < buffer_size; i++)
        {
            normalized_extents[i] = (extents[i] - min_extent) / (max_extent - min_extent);
        }
    }
    else
    {
        // If all changing extents are the same, normalize to 0
        for (int i = 0; i < buffer_size; i++)
        {
            normalized_extents[i] = 0;
        }
    }

    // Step 4: Calculate the average of the normalized changing extents
    double normalized_sum = 0.0;
    for (int i = 0; i < buffer_size; i++)
    {
        normalized_sum += normalized_extents[i];
    }

    // fprintf(stderr, "normailzed:\n");
    // for (int i = 0; i < buffer_size; i++)
    // {
    //     fprintf(stderr, "%.2lf ", normalized_extents[i]);
    // }
    // fprintf(stderr, "\n");
    return normalized_sum / buffer_size;
}

double try_trigger_migration_revised(unsigned int start_idx, unsigned int end_idx)
{
    struct timespec start, end;
    double elapsed = 0;
    // reset_bkt_page_num_pair();

    fprintf(stderr, "migration from %u to %u\n", start_idx, end_idx);
    fprintf(stderr, "--------start\n");
    uintptr_t *cold_arr = NULL, *hot_arr = NULL;
    double cur_migration_time = 0.0;
    int cold_warm_idx = 0, warm_hot_idx = 0, high = old_num_op - 1;
    int ret;
    bool enable_lazy = 0;

    double look_page_location_time = align_obj_2_page_bd_revised(start_idx, end_idx); // update page temperature inside
    cur_migration_time += look_page_location_time;
    fprintf(stderr, "look_page_location_time: %.3f\n", look_page_location_time);

    max_num_hot = max(max_num_hot, cur_fast_num_hot);
    cur_hot_in_all = (double)cur_fast_num_hot / old_num_op;
    fprintf(stderr, "cur_fast_num_hot: %ld, old_num_op: %lu, cur_hot_in_all: %.3f\n", cur_fast_num_hot, old_num_op, cur_hot_in_all);
    // return 0.0;
    // short min_hotness, max_hotness;
    // get_page_hotness_bound(&min_hotness, &max_hotness);

    short split = 0; // <= split: cold, > split, hot
    // get distribution of hotness, then test different split
    // if (global_hotness_thresh == 0)
    // {
    //     if (global_bookkeep_args->doIO)
    //     {
    //         populate_hotness_vec(); // if you want to see distribution
    //     }
    //     split = 0;
    // }
    // else if (global_hotness_thresh == 1) // avg
    // {
    //     clock_gettime(CLOCK_MONOTONIC, &start);
    //     short avg = get_avg_hotness();
    //     clock_gettime(CLOCK_MONOTONIC, &end);
    //     elapsed = end.tv_sec - start.tv_sec;
    //     elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
    //     fprintf(stderr, "get avg time: %.3f, avg: %hd\n", elapsed, avg);
    //     split = avg;
    // }
    // else if (global_hotness_thresh == 2) // median
    // {
    //     populate_hotness_vec();
    //     clock_gettime(CLOCK_MONOTONIC, &start);
    //     short median = get_median_hotness();
    //     clock_gettime(CLOCK_MONOTONIC, &end);
    //     elapsed = end.tv_sec - start.tv_sec;
    //     elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
    //     fprintf(stderr, "get median time: %.3f, median: %hd\n", elapsed, median);
    //     split = median;
    // }
    // else if (global_hotness_thresh == 3) // 2nd mode
    // {

    //     populate_hotness_vec();
    //     clock_gettime(CLOCK_MONOTONIC, &start);
    //     short mode = get_2nd_mode_hotness();
    //     clock_gettime(CLOCK_MONOTONIC, &end);
    //     elapsed = end.tv_sec - start.tv_sec;
    //     elapsed += (end.tv_nsec - start.tv_nsec) / 1000000000.0;
    //     fprintf(stderr, "get mode time: %.3f, mode: %hd\n", elapsed, mode);
    //     split = mode;
    // }

    // unsigned int max_size = get_pages_size();
    unsigned int max_size = get_pages_bkt_size();
    int demo_size = 0, promo_size = 0;
    void **demote_pages = calloc(max_size, sizeof(void *));
    void **promote_pages = calloc(max_size, sizeof(void *));
    print_bucket_stat();

    // void **demote_pages = numa_alloc_onnode(max_size * sizeof(void *), 0);
    // void **promote_pages = numa_alloc_onnode(max_size * sizeof(void *), 0);
    int free_dram_size = check_dram_free();
    free_dram_size -= SYS_RESERVE; // adjust size
    if (free_dram_size <= 0)
        free_dram_size = 0;
    int free_dram_pages = free_dram_size * 256;
    int bkt_split = 0;
    fprintf(stderr, "free_dram_pages: %d\n", free_dram_pages);

    if (global_demo_mode == 0)
    {
        bkt_split = determine_split_eager(0, free_dram_pages);
        // populate_mig_pages_wo_hit_again(demote_pages, promote_pages, &demo_size, &promo_size, split);
        // populate_mig_pages_eager(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
        populate_mig_pages_eager(demote_pages, &demo_size, &free_dram_pages, bkt_split, false);
    }
    else if (global_demo_mode == 1) // deprecated lazy demo mode, for future ref, do not use
    {
        bkt_split = determine_split_eager(0, free_dram_pages);
        // populate_mig_pages_wo_hit_again(demote_pages, promote_pages, &demo_size, &promo_size, split);
        // populate_mig_pages_eager(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
        populate_mig_pages_eager(demote_pages, &demo_size, &free_dram_pages, bkt_split, false);
    }
    else if (global_demo_mode == 2) // force lazy
    {
        bkt_split = determine_split_eager(1, free_dram_pages);
        // populate_mig_pages(demote_pages, promote_pages, &demo_size, &promo_size, split);
        // populate_mig_pages_lazy(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
        populate_mig_pages_lazy(demote_pages, &demo_size, &free_dram_pages, bkt_split, false);
    }
    else if (global_demo_mode == 3)
    {
        // adaptive lazy demo
        // 1. get RSS distribution
        int dram_percent = 0, cxl_percent = 0;
        get_rss_ratio(&dram_percent, &cxl_percent);
        fprintf(stderr, "Pages in node 0: %d%%\n", dram_percent);
        fprintf(stderr, "Pages in node 1: %d%%\n", cxl_percent);
        // 2. get eagerness
        {
            double dram_percent_norm = dram_percent / 100.0;
            fprintf(stderr, "DRAM percent: %.2f\n", dram_percent_norm);
            double avg_llc_eagerness = calculate_averaged_eagerness(llc_miss_arr);
            fprintf(stderr, "avg_llc_eagerness: %.2lf\n", avg_llc_eagerness);
            double avg_cxl_eagerness = calculate_averaged_eagerness(cxl_bw_arr);
            fprintf(stderr, "avg_cxl_eagerness: %.2lf\n", avg_cxl_eagerness);
            total_eagerness = dram_percent_norm * avg_llc_eagerness * avg_cxl_eagerness;
            fprintf(stderr, "total_eagerness: %.2f\n", total_eagerness);
            if (total_eagerness >= 0.03)
                enable_lazy = false;
            else
                enable_lazy = true;
        }
        // enable_lazy = false; // for testing
        if (very_first_bk)
        {
            bkt_split = 5;
        }
        else
        {
            bkt_split = determine_split_eager(enable_lazy, free_dram_pages);
            fprintf(stderr, "bkt_split after calc: %d\n", bkt_split);

            if (total_eagerness - prev_eagerness < 0) // less eager, push left
            {
                bkt_split = (--bkt_split < 0) ? 0 : bkt_split;
            }
            else
            {
                // do nothing, shouldn't push right since if so there should be pages in both demo and promo
            }
        }
        fprintf(stderr, "bkt_split final: %d\n", bkt_split);
        prev_eagerness = total_eagerness; // update prev_eagerness

        if (enable_lazy)
        {
            fprintf(stderr, "lazy demote\n");
            // populate_mig_pages(demote_pages, promote_pages, &demo_size, &promo_size, split);
            // populate_mig_pages_lazy(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
            populate_mig_pages_lazy(demote_pages, &demo_size, &free_dram_pages, bkt_split, false);
        }
        else
        {
            fprintf(stderr, "eager demote\n");
            // populate_mig_pages_wo_hit_again(demote_pages, promote_pages, &demo_size, &promo_size, split);
            // populate_mig_pages_eager(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
            populate_mig_pages_eager(demote_pages, &demo_size, &free_dram_pages, bkt_split, false); // populate demo first
        }
        // for quick testing
        // populate_mig_pages(demote_pages, promote_pages, &demo_size, &promo_size, split);
        // populate_mig_pages_lazy(demote_pages, promote_pages, &demo_size, &promo_size, &free_dram_pages, bkt_split);
    }
    // int dupCount = count_duplicates(promote_pages, promo_size, demote_pages, demo_size);
    // fprintf(stderr, "Number of duplicates: %d\n", dupCount);
    fprintf(stderr, "before filtering demo_size: %d\n", demo_size);

    if (free_dram_size < 50 && demo_size > 0) // if # need to promo > available DRAM size, then first to demotion
    {
        // && promo_size > (cur_dram_free + 50) * 256
        fprintf(stderr, "entering demotion\n");
        // if(promo_size <= (cur_dram_free + 50) * 256)
        // continue;
        // if (global_demo_mode == 2 || (global_demo_mode == 3 && enable_lazy))
        //     goto do_demo;
        // if (promo_size < demo_size) // no need to demote all of them
        //     demo_size = promo_size;
        // else // means we need to do demo anyway regardless lazy or not
        // {
        //     // forced_demo = true;
        //     fprintf(stderr, "doing forced demo\n");
        //     goto do_demo;
        // }
        if (global_demo_mode == 0 || global_demo_mode == 2 || global_demo_mode == 3)
        {
        do_demo:
            if (demo_size < max_size)
            {
                demote_pages = realloc(demote_pages, demo_size * sizeof(void *));
            }
            double first_demo_time = do_migration(demote_pages, demo_size, CXL_MASK); // Demote to CXL
            fprintf(stderr, "demo_time: %.3f\n", first_demo_time);
            cur_migration_time += first_demo_time;
            is_migration = true;
            very_first_demote = false; // TODO: check once, unnecessary here?
        }
        else if (global_demo_mode == 1) // stale demo impl, do not use
        {
            if (very_first_demote)
            {
                last_demote_pages = kh_init(ptrset_dup);
                for (int i = 0; i < demo_size; i++)
                {
                    kh_put(ptrset_dup, last_demote_pages, demote_pages[i], &ret);
                }
                if (demo_size < max_size)
                {
                    demote_pages = realloc(demote_pages, demo_size * sizeof(void *));
                }
                double first_demo_time = do_migration(demote_pages, demo_size, CXL_MASK); // Demote to CXL
                fprintf(stderr, "demo_time: %.3f\n", first_demo_time);
                cur_migration_time += first_demo_time;
                is_migration = true;
                very_first_demote = false;
            }
            else
            {
                // if not first demo, check intersection ratio
                size_t prev_demo_size = kh_size(last_demote_pages);
                size_t dupCount = 0;
                for (int i = 0; i < demo_size; i++)
                {
                    khint_t k = kh_get(ptrset_dup, last_demote_pages, demote_pages[i]);
                    if (k != kh_end(last_demote_pages))
                    {
                        dupCount++;
                    }
                }
                double intersection_ratio = (double)dupCount / prev_demo_size;
                fprintf(stderr, "intersection_ratio: %.3f\n", intersection_ratio);
                if (intersection_ratio > 0.6)
                {
                    // demote current demote_pages
                    if (demo_size < max_size)
                    {
                        demote_pages = realloc(demote_pages, demo_size * sizeof(void *));
                    }
                    double future_demo_time = do_migration(demote_pages, demo_size, CXL_MASK); // Demote to CXL
                    cur_migration_time += future_demo_time;
                    fprintf(stderr, "future_demo_time: %.3f\n", future_demo_time);
                    is_migration = true;
                    kh_destroy(ptrset_dup, last_demote_pages);
                    last_demote_pages = kh_init(ptrset_dup);
                    for (int i = 0; i < demo_size; i++)
                    {
                        kh_put(ptrset_dup, last_demote_pages, demote_pages[i], &ret);
                    }
                }
                else
                {
                    kh_destroy(ptrset_dup, last_demote_pages);
                    last_demote_pages = kh_init(ptrset_dup);
                    for (int i = 0; i < demo_size; i++)
                    {
                        kh_put(ptrset_dup, last_demote_pages, demote_pages[i], &ret);
                    }
                    demo_size = 0;
                    free(demote_pages);
                    demote_pages = NULL;
                }
            }
        }
    }
    else
    {
        demo_size = 0;
        free(demote_pages);
        demote_pages = NULL;
    }
    // entering promotion, re-calculate free local size
    int cur_dram_free = check_dram_free();
    cur_dram_free -= SYS_RESERVE; // adjust size
    if (cur_dram_free <= 0)
        cur_dram_free = 0;
    free_dram_pages = cur_dram_free * 256;
    fprintf(stderr, "cur_dram_free: %d MB\n", cur_dram_free);

    populate_mig_pages_eager(promote_pages, &promo_size, &free_dram_pages, bkt_split, true); // populate promo pages
    if (promo_size > 0 && free_dram_pages > 0)
    {
        fprintf(stderr, "before filtering  promo_size: %d, free dram pages: %d\n", promo_size, free_dram_pages);
        if (free_dram_pages < promo_size) // this is for safely
        {
            promo_size = free_dram_pages;
            fprintf(stderr, "resized promo_size: %d\n", promo_size);
        }

        if (promo_size < max_size)
        {
            // promote_pages = (void **)numa_realloc(promote_pages, max_size * sizeof(void *), promo_size * sizeof(void *));
            promote_pages = realloc(promote_pages, promo_size * sizeof(void *));
        }
        double promo_time = do_migration(promote_pages, promo_size, DRAM_MASK); // promote to DRAM
        cur_migration_time += promo_time;
        fprintf(stderr, "promo_time: %.3f\n", promo_time);
        is_migration = true;
    }
    else
    {
        free(promote_pages);
        // numa_free(promote_pages, max_size * sizeof(void *));
        promote_pages = NULL;
        promo_size = 0;
    }
    global_demo_size += demo_size;
    global_promo_size += promo_size;
    fprintf(stderr, "pages size: %d, split: %hd, demo_size: %d, promo_size: %d\n", max_size, split, demo_size, promo_size);

    // prev_c_w_percent = cur_c_w_percent; // remember to update prev_c_w_percent for next try_migration
    if (very_first_mig)
        very_first_mig = false;
    fprintf(stderr, "cur_migration_time: %.3f\n", cur_migration_time);
    fprintf(stderr, "--------end\n");

    if (global_bookkeep_args->doIO)
    {
        FILE *hotness_fd = fopen("page_hotness.txt", "a");
        if (hotness_fd == NULL)
        {
            perror("Failed to hotness file");
            return 1;
        }
        PyGILState_STATE gstate = PyGILState_Ensure();
        dump_page_hotness(hotness_fd);
        PyGILState_Release(gstate);
        fprintf(stderr, "writing complete\n");
        fclose(hotness_fd);
    }

    clear_hotness_vec();
    return cur_migration_time;
}

// return code:
//  -1: error
//  0: terminated by user
//  1: trigger scan
int trigger_bk()
{
    // return 1; // dummy switch quick testing
    long long total_dram_size;
    long long free_dram_size;
    total_dram_size = numa_node_size(DRAM_MASK, NULL);
    while (!terminate_flag_refchain)
    {
        if (numa_node_size(DRAM_MASK, &free_dram_size) <= 0)
        {
            fprintf(stderr, "Unlikely! Failed to get DRAM node free size\n");
            return -1;
        }
        double freePercentage = ((double)free_dram_size / total_dram_size) * 100.0;
        int free_dram_size_mb = free_dram_size / 1048576;

        // if (freePercentage < TRIGGER_SCAN_WM) // 35%
        fprintf(stderr, "free_dram_size: %d mb\n", free_dram_size_mb);
        if (free_dram_size_mb < global_bookkeep_args->metadata_resv) // by doing this, we make sure we have enough place for metadata on local DRAM
        {
            fprintf(stderr, "Start triggering scan\n");
            return 1;
        }

        // fprintf(stderr, "freePercentage: %.2f, no need to offload, free_dram_size: %.2f\n", freePercentage, free_dram_size_mb);
        usleep(500000);
    }
    return 0; // terminated by user
}

void *manual_trigger_scan(void *arg)
{
#if defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 0)
    fprintf(stderr, "using accumulated hotness (AH)\n");
#elif defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 1)
    fprintf(stderr, "using median hotness (MH)\n");
#endif
    pthread_t parse_llc_thread_id; // for adaptive lazy demo
    global_bookkeep_args = (BookkeepArgs *)arg;
    if (global_bookkeep_args->doIO)
    {
        char *home = getenv("HOME"); // Get the value of $HOME
        if (home == NULL)
        {
            fprintf(stderr, "HOME environment variable not set.\n");
            return NULL;
        }
        const char *suffix = "/workspace/py_track/page_hotness.txt";
        char filename[1024];
        snprintf(filename, sizeof(filename), "%s%s", home, suffix);

        // Check if the file exists
        if (access(filename, F_OK) == 0)
        {
            // File exists, so remove it
            if (remove(filename) == 0)
            {
                fprintf(stderr, "File '%s' deleted.\n", filename);
            }
            else
            {
                perror("Error deleting the file");
            }
        }
    }
    if (global_demo_mode == 3)
    {
        // format llc and bw file paths
        home_dir = getenv("HOME");
        create_full_path();
        fprintf(stderr, "perf_stat_full_path: %s\n", perf_stat_full_path);
        fprintf(stderr, "bw_full_path: %s\n", bw_full_path);
        // spawn thread
        if (pthread_create(&parse_llc_thread_id, NULL, parse_llc_miss_bw_routine, NULL) != 0)
        {
            perror("Failed to create thread");
            return 1;
        }
    }

#ifdef PARTIAL_SCAN
    fprintf(stderr, "partial_scan defined\n");
#else
    fprintf(stderr, "doing whole scan\n");
#endif

    if (numa_available() == -1 || numa_num_configured_nodes() < 2)
    {
        fprintf(stderr, "CXL offloading is not supported!\n");
        return NULL;
    }
    numa_set_preferred(0);
    reset_bkt_page_num_pair();
    // global_op_set = kh_init(ptrset);
    // init_global_set_helper();
    // else if return 1: start triggering scan

    enable_bk = 1;
    if (trigger_bk() == 0)
    {
        return NULL;
    }
    // pre-allocate all_temps to DRAM

    if (!global_bookkeep_args->cutoff_limit)
    {
        cutoff_limit = 2;
    }
    else
    {
        cutoff_limit = (double)global_bookkeep_args->cutoff_limit / 1000000.0;
    }
    fprintf(stderr, "trigger from manual\n");
    fprintf(stderr, "skip future slow thresh: %d\n", global_bookkeep_args->skip_future_slow_thresh);
    unsigned int doIO_ = global_bookkeep_args->doIO;
    int fast_scan_idx = -1;
    double cur_mig_time = 0;
    uintptr_t foundInner = 0;
    uintptr_t prev_changed_max = 0;
    uintptr_t prev_changed_min = ULONG_MAX;
    int trigger_drop_thresh = 50; // percentage
    bool do_drop_unhot_op;
    long temp_diff = 0;
    double total_migration_time = 0;
    double total_fast_time = 0.0;
    int total_fast_num = 0;

    struct timespec start_fast, end_fast;
    clock_gettime(CLOCK_MONOTONIC, &global_start);
    // int scan_stat = 0;
    // while (!terminate_flag_refchain)
    // {
    //     usleep(200000);
    // } // what??
    reset_all_temps = 1;
    while (!terminate_flag_refchain)
    {
    rollback_slow_scan:
        if (trigger_bk() == 0)
        {
            break;
        }
        zero_hot_num = 0;
        cur_fast_num_hot = 0; // reset for every fast scan
        not_in_global_set = 0;
        if (fast_scan_idx == -1)
        {
            reset_all_temps = try_trigger_slow_scan();
            fprintf(stderr, "reset_all_temps: %d\n", reset_all_temps);
            if (reset_all_temps == -1)
            {
                usleep(2000000);
                fprintf(stderr, "unlikely, check once\n");
                goto rollback_slow_scan;
            }
            fast_scan_idx = 0; // start fast scan
        }
        clock_gettime(CLOCK_MONOTONIC, &start_fast);
        unsigned int partition = old_num_op / (NUM_SLOTS - 1);
        if (fast_scan_idx == 0)
        {
            if (reset_all_temps == 1)
            {
                for (int i = 0; i < old_num_op; i++)
                {
                    if (sigsetjmp(jump_buffer, 1) == 0)
                    {
                        all_temps[i].prev_refcnt = get_growth(all_temps[i].op);
                    }
                    else
                    {
                        all_temps[i].diffs[NUM_SLOTS - 1] |= (1 << DROP_OUT_OFF);
                        not_in_global_set++;
                    }
                }
            }
            else if (reset_all_temps == 2)
            {
                fprintf(stderr, "previous part need record, new part need only update prev_recnt\n");
#ifdef PARTIAL_SCAN
                record_temp(fast_scan_idx, 0, partition);
#else
                record_temp(fast_scan_idx, 0, prev_num_op);
#endif
                for (int i = prev_num_op; i < old_num_op; i++)
                {
                    if (sigsetjmp(jump_buffer, 1) == 0)
                    {
                        all_temps[i].prev_refcnt = get_growth(all_temps[i].op);
                    }
                    else
                    {
                        all_temps[i].diffs[NUM_SLOTS - 1] |= (1 << DROP_OUT_OFF);
                        not_in_global_set++;
                    }
                }
            }
            else
            { // use old_num_op and record all
#ifdef PARTIAL_SCAN
                record_temp(fast_scan_idx, 0, partition);
#else
                record_temp(fast_scan_idx, 0, old_num_op);
#endif
            }
        }
        else if (fast_scan_idx == 1)
        {
            if (reset_all_temps == 1 || reset_all_temps == 2)
            {
#ifdef PARTIAL_SCAN
                for (int i = partition; i < partition * 2; i++)
#else
                for (int i = 0; i < old_num_op; i++)
#endif
                {
                    if (all_temps[i].diffs[NUM_SLOTS - 1] & (1 << DROP_OUT_OFF))
                    {
                        continue;
                    }
                    if (sigsetjmp(jump_buffer, 1) == 0)
                    {
                        // all_temps[i].diffs[fast_scan_idx] = (abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt) >= 127) ? 127 : (uint8_t)abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt);
                        // all_temps[i].prev_refcnt = get_growth(all_temps[i].op);

                        int current_growth = get_growth(all_temps[i].op);
                        int growth = abs(current_growth - all_temps[i].prev_refcnt);
                        all_temps[i].diffs[fast_scan_idx] = (uint8_t)((growth >= 127) ? 127 : growth);
                        all_temps[i].prev_refcnt = current_growth;
                    }
                    else
                    {
                        all_temps[i].diffs[NUM_SLOTS - 1] |= (1 << DROP_OUT_OFF);
                        not_in_global_set++;
                    }
                }
            }
            else
            { // 0 --> slow scan not triggered
#ifdef PARTIAL_SCAN
                record_temp(fast_scan_idx, partition, partition * 2);
#else
                record_temp(fast_scan_idx, 0, old_num_op);
#endif
            }
        }
        else if (fast_scan_idx == 2)
        {
            if (reset_all_temps == 1 || reset_all_temps == 2)
            {
#ifdef PARTIAL_SCAN
                for (int i = partition * 2; i < partition * 3; i++)
#else
                for (int i = 0; i < old_num_op; i++)
#endif
                {
                    // foundInner = (uintptr_t)all_temps[i].op;
                    // if (foundInner > prev_changed_min && foundInner < prev_changed_max)
                    {
                        if (all_temps[i].diffs[NUM_SLOTS - 1] & (1 << DROP_OUT_OFF))
                        {
                            continue;
                        }
                        if (sigsetjmp(jump_buffer, 1) == 0)
                        {
                            // all_temps[i].diffs[fast_scan_idx] = (abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt) >= 127) ? 127 : (uint8_t)abs(get_growth(all_temps[i].op) - all_temps[i].prev_refcnt);
                            // all_temps[i].prev_refcnt = get_growth(all_temps[i].op);
                            int current_growth = get_growth(all_temps[i].op);
                            int growth = abs(current_growth - all_temps[i].prev_refcnt);
                            all_temps[i].diffs[fast_scan_idx] = (uint8_t)((growth >= 127) ? 127 : growth);
                            all_temps[i].prev_refcnt = current_growth;
                        }
                        else
                        {
                            all_temps[i].diffs[NUM_SLOTS - 1] |= (1 << DROP_OUT_OFF); // not in the set, drop out
                            not_in_global_set++;
                        }
                    }
                    // else
                    // {
                    //     all_temps[i].diff |= (1 << DROP_OUT_OFF); // falls outside chaning range, also drop out
                    // }
                }
            }
            else
            { // 0: use old_num_op
#ifdef PARTIAL_SCAN
                record_temp(fast_scan_idx, partition * 2, partition * 3);
#else
                record_temp(fast_scan_idx, 0, old_num_op);
#endif
            }
        }
        else if (fast_scan_idx != NUM_SLOTS - 1) // [0:6]
        {
#ifdef PARTIAL_SCAN
            record_temp(fast_scan_idx, partition * fast_scan_idx, partition * (fast_scan_idx + 1));
#else
            record_temp(fast_scan_idx, 0, old_num_op);
#endif
        }

        clock_gettime(CLOCK_MONOTONIC, &end_fast);
        double cur_fast_time = end_fast.tv_sec - start_fast.tv_sec;
        cur_fast_time += (end_fast.tv_nsec - start_fast.tv_nsec) / 1000000000.0;
        fprintf(stderr, "fast %d, cur_fast_time: %.3f\n", fast_scan_idx, cur_fast_time);
        total_fast_time += cur_fast_time;
        if (fast_scan_idx != -1)
            total_fast_num++;
        fprintf(stderr, "total_fast_num: %d, total_fast_time: %.3f\n", total_fast_num, total_fast_time);

        // fprintf(stderr, "", );
        // relaxed fast
        // if (fast_scan_idx != 0 || (fast_scan_idx == 0 && reset_all_temps != 1))
        // {
        // double deleted_in_all = (double)not_in_global_set / old_num_op;
        // fprintf(stderr, "not_in_global_set: %d, deleted_in_all: %.3f\n", not_in_global_set, deleted_in_all);
        // if (deleted_in_all > 0.9)
        // {
        //     fprintf(stderr, "unlikely, most op are deleted, rollback to slow\n");
        //     usleep(2000000);
        //     fast_scan_idx = -2; // a lot of op are deleted, rollback to slow
        // }
        // if (cur_hot_in_all < 0.01) // limited # changed op, OR, similar # hot, relax fast trace
        // {
        //     fprintf(stderr, "small # changed, rollback to slow...\n");
        //     usleep(2000000);
        //     // fast_scan_idx = -2;
        // }
        // }

        // if (fast_scan_idx == 3)
        // {
        //     total_migration_time += try_trigger_migration_revised(0, partition * 4);
        // }

        if (++fast_scan_idx >= NUM_SLOTS - 1)
        {
            fast_scan_idx = -1; // roll back to slow scan

            // determine if we want to skip future slow trace
            // clock_gettime(CLOCK_MONOTONIC, &global_current);
            // global_elapsed = global_current.tv_sec - global_start.tv_sec;
            // global_elapsed += (global_current.tv_nsec - global_start.tv_nsec) / 1000000000.0;
            // if (total_num_slow % 3 == 0 && total_slow_time > (double)global_elapsed / (100 / global_bookkeep_args->skip_future_slow_thresh))
            // {
            //     fprintf(stderr, "skipping future slow\n");
            //     skip_future_slow = true;
            // }

            if (global_do_migration)
                cur_mig_time = try_trigger_migration_revised(0, partition * 7); // do migration
            total_migration_time += cur_mig_time;
            fprintf(stderr, "total_migration_time: %.3f\n", total_migration_time);
            max_num_hot = 0;
            if (very_first_bk)
                very_first_bk = false;
            if (doIO_)
            {
                fprintf(stderr, "flushing...\n");
                PyGILState_STATE gstate = PyGILState_Ensure();
                struct timespec ts;
                clock_gettime(CLOCK_MONOTONIC, &ts);
                for (int i = 0; i < old_num_op; i++)
                {
                    // bool print_obj = false;
                    // if ((all_temps[i].diff & HOTNESS_MASK) && !(all_temps[i].diff & (1 << DROP_OUT_OFF)))
                    //     print_obj = true;
                    int zero_cnt = 0;
                    for (int j = 0; j < NUM_SLOTS - 1; j++)
                    {
                        if (all_temps[i].diffs[j] == 0)
                            zero_cnt++;
                    }
                    if (zero_cnt == 7)
                        continue;
                    uintptr_t found_inner = (uintptr_t)all_temps[i].op;
                    // if (check_in_global_helper(found_inner))
                    // if (print_obj)
                    {
                        fprintf(global_bookkeep_args->fd, "%ld.%ld\t%ld", ts.tv_sec, ts.tv_nsec, found_inner);
                        // fprintf(global_bookkeep_args->fd, "\t%s", Py_TYPE(found_inner)->tp_name);
                        for (int j = 0; j < NUM_SLOTS - 1; j++)
                        {
                            fprintf(global_bookkeep_args->fd, "\t%hd", all_temps[i].diffs[j]);
                        }
                        fprintf(global_bookkeep_args->fd, "\t%hd", all_temps[i].diffs[NUM_SLOTS - 1] & HOTNESS_MASK);
                        // PyObject_Print(all_temps[i].op, global_bookkeep_args->fd, 0);
                        fprintf(global_bookkeep_args->fd, "\n");
                    }
                }
                fflush(global_bookkeep_args->fd);
                PyGILState_Release(gstate);
            }
        }
        // skip_fast_scans:
        //     if ((cur_fast_time > 2.5 && cur_hot_in_all < 0.05) || (fast_scan_idx == -1 && cur_mig_time < 0.001))
        //     {
        //         fprintf(stderr, "relaxed fast/slow, sleep longer\n");
        //         // usleep(global_bookkeep_args->sample_dur * 2);
        //         usleep((int)cur_fast_time * 1000000);
        //     }
        //     else

        usleep(global_bookkeep_args->sample_dur);
    }
    if (global_demo_mode == 3)
    {
        fprintf(stderr, "joining\n");
        pthread_join(parse_llc_thread_id, NULL);
    }
    numa_set_localalloc();
    terminate_flag_refchain = 0;
    enable_bk = 0;
    fprintf(stderr, "Summary: total_slow_num: %d, total_slow_time: %.3f, total_migration_time: %.3f, num_gc_cycles: %ld, total_new_op_num: %ld\n", total_num_slow, total_slow_time, total_migration_time, num_gc_cycles, total_new_op_num);
    fprintf(stderr, "global_demo_size: %lu, global_promo_size: %lu\n", global_demo_size, global_promo_size);
    // free(all_temps);
    kh_destroy(ptrset_dup, last_demote_pages);
    // free_map();
    free_global();
    // free_pages();
    free_pages_bkt();
    reset_bkt_page_num_pair();
    // destroy_global_set_helper();
}