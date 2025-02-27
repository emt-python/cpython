#include <unordered_set>
#include <unordered_map>
#include <tuple>
#include "../Include/myset.h"
#include "../Include/obj_temp.h"
#include <cstdint>
#include <cstdio>
#include <mutex>
#include <vector>
#include <numeric> // For std::accumulate
#include <algorithm>
#include <map>
#include <Python.h>
#include <limits>
#include <chrono>
#include <ctime>
// #include <numa.h>
// #include <numaif.h>
// numa_set_preferred(0);
std::mutex global_set_mutex;
static std::unordered_set<uintptr_t> global_unordered_set;
static std::unordered_map<uintptr_t, bool> global_unordered_map;
static std::unordered_map<void *, int> pages_loc_hotness;
// static std::unordered_map<uintptr_t, std::pair<short, bool>> map_pair;
static std::unordered_map<uintptr_t, std::pair<short, std::pair<bool, bool>>> map_pair; // <addr, <hotness, <loc, lazy>>>
static std::vector<short> hotness_vec;
static bool first_demo = true;
extern OBJ_TEMP *all_temps;
extern unsigned int old_num_op;

#include <array>
#include <math.h>                                                                            // for log2 function
static std::unordered_map<uintptr_t, std::pair<short, std::pair<bool, bool>>> page_bkt_pair; // <addr, <bkt_idx, <loc, lazy>>>
#define NUM_BUCKETS 11
static std::array<int, NUM_BUCKETS> bkt_page_num_pair = {};
static short hot_bkt_idx_position[2];

// global_unordered_set
extern "C" void insert_into_global(uintptr_t value)
{
    global_unordered_set.insert(value);
}

extern "C" int check_in_global(uintptr_t value)
{
    return global_unordered_set.find(value) != global_unordered_set.end();
}

extern "C" int check_in_global_safe(uintptr_t value)
{
    std::lock_guard<std::mutex> guard(global_set_mutex);
    return global_unordered_set.find(value) != global_unordered_set.end();
}

extern "C" void free_global()
{
    global_unordered_set.clear();
}

extern "C" unsigned int get_global_size()
{
    return global_unordered_set.size();
}

extern "C" void erase_from_global(uintptr_t value)
{
    global_unordered_set.erase(value);
}

extern "C" void erase_from_global_safe(uintptr_t value)
{
    std::lock_guard<std::mutex> guard(global_set_mutex);
    global_unordered_set.erase(value);
}

extern "C" void print_global_addr(FILE *fd, int round)
{
    for (auto it = global_unordered_set.begin(); it != global_unordered_set.end(); ++it)
    {
        fprintf(fd, "%d\t%ld\n", round, *it);
    }
}
extern "C" int valid_global_set()
{
    return (&global_unordered_set != nullptr);
}

extern "C" void reset_all_temps_func()
{
    free(all_temps);
    unsigned int new_num_op = global_unordered_set.size();
    all_temps = (OBJ_TEMP *)calloc(new_num_op, sizeof(OBJ_TEMP));
    unsigned int i = 0;
    for (auto it = global_unordered_set.begin(); it != global_unordered_set.end(); ++it)
    {
        all_temps[i].op = (PyObject *)*it;
        // all_temps[i].prev_refcnt = 0;
        i++;
    }
    old_num_op = new_num_op;
}

// global_unordered_map
extern "C" void insert_into_map(uintptr_t value, bool val)
{
    global_unordered_map[value] = val;
}

extern "C" int check_in_map(uintptr_t value)
{
    return global_unordered_map.find(value) != global_unordered_map.end();
}

extern "C" void erase_from_map(uintptr_t value)
{
    global_unordered_map.erase(value);
}

extern "C" void free_map()
{
    global_unordered_map.clear();
}

extern "C" unsigned int get_map_size()
{
    return global_unordered_map.size();
}

// pages_loc_hotness
// map_pair
extern "C" void insert_into_pages(uintptr_t page_addr, short hotness, bool location)
{
    auto it = map_pair.find(page_addr);
    if (it != map_pair.end())
    {
        // if (is_hot)
        it->second.first += hotness;
    }
    else
    {
        // map_pair.emplace(page_addr, std::make_pair(is_hot ? hotness : 0, false));
        // map_pair[page_addr] = std::make_pair(is_hot ? hotness : 0, false);
        // map_pair[page_addr] = std::make_pair(hotness, location);                        // false (0): DRAM, true (1): CXL
        map_pair[page_addr] = std::make_pair(hotness, std::make_pair(location, false)); // false (0): DRAM, true (1): CXL
    }
}
extern "C" void insert_into_pages_only_exists(uintptr_t page_addr, short hotness)
{
    auto it = map_pair.find(page_addr);
    if (it != map_pair.end())
    {
        it->second.first += hotness;
    }
}

extern "C" int check_in_pages(uintptr_t page) // not used
{
    // return pages_loc_hotness.find(page) != pages_loc_hotness.end();
    return map_pair.find(page) != map_pair.end();
}

extern "C" void erase_from_pages(uintptr_t page) // not used
{
    // pages_loc_hotness.erase(page);
    map_pair.erase(page);
}

extern "C" void free_pages()
{
    // pages_loc_hotness.clear();
    map_pair.clear();
}

extern "C" unsigned int get_pages_size()
{
    // return pages_loc_hotness.size();
    return map_pair.size();
}

int process_signed_value(int input)
{
    // Mask out the 2nd MSB and the remaining bits except the LSB 14
    int mask = 0x3FFFFFFF; // 0011 1111 1111 1111 in binary
    int processed_value = input & mask;

    // If MSB is set (negative number), set MSB in processed value
    if (input & 0x80000000)
    {                                  // 1000 0000 0000 0000 in binary
        processed_value |= 0x80000000; // 1000 0000 0000 0000 in binary
    }

    return processed_value;
}

bool getSecondMSB(int num)
{
    return (num & (1 << 30)) >> 30; // Isolate the 2nd MSB and normalize it to 0 or 1
}

extern "C" void populate_mig_pages(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, short split)
{
    if (first_demo)
    {
        populate_mig_pages_wo_hit_again(demote_pages, promote_pages, demo_size, promo_size, split);
        first_demo = false;
    }
    else
    {
        for (auto it = map_pair.begin(); it != map_pair.end(); ++it)
        {
            if (it->second.first <= split && !it->second.second.first) // is cold and is in DRAM
            {
                if (it->second.second.second) // if hit again
                {
                    *demote_pages = (void *)it->first;
                    demote_pages++;
                    (*demo_size)++;
                    it->second.second.second = false;
                }
                else
                {
                    it->second.second.second = true;
                }
            }
            else if (it->second.first > split && it->second.second.first) // is hot and is in CXL
            {
                *promote_pages = (void *)it->first;
                promote_pages++;
                (*promo_size)++;
                it->second.second.second = false;
            }
        }
    }
}

extern "C" void populate_mig_pages_wo_hit_again(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, short split)
{
    for (auto it = map_pair.begin(); it != map_pair.end(); ++it)
    {
        if (it->second.first <= split && !it->second.second.first) // is cold and is in DRAM
        {
            *demote_pages = (void *)it->first;
            demote_pages++;
            (*demo_size)++;
        }
        else if (it->second.first > split && it->second.second.first) // is hot and is in CXL
        {
            *promote_pages = (void *)it->first;
            promote_pages++;
            (*promo_size)++;
        }
    }
}

extern "C" void get_page_hotness_bound(short *min_val, short *max_val) // not used
{
    short min = SHRT_MAX;
    short max = SHRT_MIN;

    // for (const auto &it : pages_loc_hotness)
    for (const auto &it : map_pair)
    {
        // int processed = process_signed_value(it.second);
        auto value = it.second;
        if (it.second.first < min)
        {
            min = it.second.first;
        }
        if (it.second.first > max)
        {
            max = it.second.first;
        }
    }
    fprintf(stderr, "min: %hd, max: %hd\n", min, max);
    *min_val = min;
    *max_val = max;
}
extern "C" void print_all_pages_hotness() // for debugging, not used
{
    for (auto it = map_pair.begin(); it != map_pair.end(); ++it)
    {
        fprintf(stderr, "page: %p, hotness: %hd\n", it->first, it->second.first);
    }
    fflush(stderr);
}

extern "C" void reset_pages_hotness()
{
    fprintf(stderr, "resetting pages hotness\n");
    for (auto it = map_pair.begin(); it != map_pair.end(); ++it)
    {
        it->second.first = 0;
    }
}

extern "C" void page_temp_cooling(float cooling_weight)
{
    fprintf(stderr, "resetting pages hotness\n");
    for (auto it = map_pair.begin(); it != map_pair.end(); ++it)
    {
        it->second.first *= (1 - cooling_weight);
    }
}

extern "C" void set_location_pages(uintptr_t page, bool location)
{
    auto it = map_pair.find(page);
    if (it != map_pair.end())
    {
        if (location)
            it->second.second.first = 1;
        else
            it->second.second.first = 0;
        // // clear hotness
        // it->second.first = 0;
    }
}

extern "C" void populate_hotness_vec()
{
    // for (const auto &entry : map_pair)
    for (const auto &entry : page_bkt_pair)
    {
        hotness_vec.push_back(entry.second.first);
    }
}

extern "C" short get_avg_hotness()
{
    double average = static_cast<double>(std::accumulate(hotness_vec.begin(), hotness_vec.end(), 0)) / hotness_vec.size();
    return (short)average;
}

extern "C" short get_median_hotness()
{
    std::sort(hotness_vec.begin(), hotness_vec.end());
    double median = 0;
    size_t n = hotness_vec.size();
    if (n % 2 == 0)
    {
        median = (hotness_vec[n / 2 - 1] + hotness_vec[n / 2]) / 2.0;
    }
    else
    {
        median = hotness_vec[n / 2];
    }
    return (short)median;
}

extern "C" short get_mode_hotness()
{
    std::map<short, int> frequency_map;
    for (const short value : hotness_vec)
    {
        frequency_map[value]++;
    }

    short mode = hotness_vec[0];
    int max_count = 0;
    for (const auto &pair : frequency_map)
    {
        if (pair.second > max_count)
        {
            max_count = pair.second;
            mode = pair.first;
        }
    }
    return mode;
}

extern "C" short get_2nd_mode_hotness()
{
    if (hotness_vec.empty())
        return std::numeric_limits<short>::min(); // Return some error value if empty

    std::map<short, int> frequency_map;

    // Populate the frequency map
    for (const short value : hotness_vec)
    {
        frequency_map[value]++;
    }

    short first_mode = hotness_vec[0];
    short second_mode = first_mode; // Initialize second mode to a valid value
    int first_max_count = 0;
    int second_max_count = 0;

    // Find both first and second modes
    for (const auto &pair : frequency_map)
    {
        if (pair.second > first_max_count)
        {
            // Shift current first mode to second mode
            second_max_count = first_max_count;
            second_mode = first_mode;

            // Update first mode
            first_max_count = pair.second;
            first_mode = pair.first;
        }
        else if (pair.second > second_max_count && pair.first != first_mode)
        {
            // Update second mode only if it is not the first mode
            second_max_count = pair.second;
            second_mode = pair.first;
        }
    }

    // If the second mode was never updated and all values are the same
    if (second_max_count == 0)
    {
        return std::numeric_limits<short>::min(); // Or handle appropriately
    }

    return second_mode;
}

extern "C" void clear_hotness_vec()
{
    hotness_vec.clear();
}

extern "C" void dump_page_hotness(FILE *fd)
{
    // auto now = std::chrono::system_clock::now();
    // std::time_t current_time = std::chrono::system_clock::to_time_t(now);
    // std::tm *local_time = std::localtime(&current_time);
    // char cur_time[30];
    // std::strftime(cur_time, sizeof(cur_time), "%Y-%m-%d %H:%M:%S", local_time);
    auto now = std::chrono::system_clock::now();
    auto duration_in_ms = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch());
    // auto duration_in_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch());

    for (short number : hotness_vec)
    {
        fprintf(fd, "%lld %hd\n", duration_in_ms.count(), number);
    }
}

extern "C" void dump_bucket_distribution(FILE *fd)
{
    auto now = std::chrono::system_clock::now();
    auto duration_in_ms = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch());
    fprintf(fd, "%lld ", duration_in_ms.count());
    for (int i = 0; i < 11; i++)
        fprintf(fd, "%d ", bkt_page_num_pair[i]);
    fprintf(fd, "\n");
}

// bucket-based hotness classification
// bucket_index: [min_hot, max_hot]
// 0: 0-1
// 1: 2-3
// 2: 4-7
// 3: 8-15
// 4: 16-31
// 5: 32-63
// 6: 64-127
// 7: 128-255
// 8: 256-511
// 9: 512-1023
// 10: > 1023

extern "C" void reset_bkt_page_num_pair()
{
    for (int i = 0; i < 11; i++)
    {
        bkt_page_num_pair[i] = 0;
    }
}

short get_bkt_idx(short hotness)
{
    // if (hotness == -1)
    //     return -1;
    if (hotness == 0)
        return 0;
    else if (hotness > 1023)
        return 10;
    return (short)log2(hotness);
}

#if defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 1)
// median
#include <queue>
#include <functional>

class MedianTracker
{
private:
    std::priority_queue<short, std::vector<short>, std::less<short>> lowers;     // max-heap
    std::priority_queue<short, std::vector<short>, std::greater<short>> highers; // min-heap

    void rebalanceHeaps()
    {
        if (lowers.size() > highers.size() + 1)
        {
            highers.push(lowers.top());
            lowers.pop();
        }
        else if (highers.size() > lowers.size())
        {
            lowers.push(highers.top());
            highers.pop();
        }
    }

public:
    MedianTracker() = default;

    void insertValue(short value)
    {
        if (lowers.empty() || value < lowers.top())
        {
            lowers.push(value);
        }
        else
        {
            highers.push(value);
        }
        rebalanceHeaps();
    }

    short getMedian() const
    {
        if (lowers.empty() && highers.empty())
        {
            // No data; handle as you wish
            return 0.0;
        }

        if (lowers.size() == highers.size())
        {
            // Even number of elements
            return (lowers.top() + highers.top()) / 2.0;
        }
        // Odd number: lowers has one extra
        return lowers.top();
    }
};
static std::unordered_map<uintptr_t, MedianTracker> page_median_data;

#endif

extern "C" void insert_into_bucket(uintptr_t page_addr, short hotness, bool location, bool insert_if_exists)
{
    // auto it = page_bkt_pair.find(page_addr);
    // if (it != page_bkt_pair.end())
    // {
    //     short bkt_idx_before = get_bkt_idx(it->second.first);
    //     it->second.first += hotness;
    //     short bkt_idx_after = get_bkt_idx(it->second.first);
    //     if (bkt_idx_before != bkt_idx_after) // if page already exists, update bkt_idx if needed
    //     {
    //         bkt_page_num_pair[bkt_idx_before]--;
    //         bkt_page_num_pair[bkt_idx_after]++;
    //         // fprintf(stderr, "before: %hd, after: %hd\n", bkt_idx_before, bkt_idx_after);
    //     }
    // }
    // else
    // {
    //     page_bkt_pair[page_addr] = std::make_pair(hotness, std::make_pair(location, false));
    //     short bkt_idx = get_bkt_idx(hotness);
    //     bkt_page_num_pair[bkt_idx]++; // newly inserted pages, shouldn't be double calculated, thus safe to inc num
    // }
    auto [it, inserted] = page_bkt_pair.emplace(page_addr, std::make_pair(hotness, std::make_pair(location, false)));
    if (!inserted) // false => page already exists
    {
        short bkt_idx_before = -1;
        short bkt_idx_after = -1;

#if defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 0)
        // --- Accumulated Hotness (AH) ---
        bkt_idx_before = get_bkt_idx(it->second.first);
        it->second.first += hotness; // Accumulate new hotness
        bkt_idx_after = get_bkt_idx(it->second.first);

#elif defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 1)
        // --- Median Hotness ---
        short old_median = page_median_data[page_addr].getMedian();
        bkt_idx_before = get_bkt_idx(old_median);

        // Insert the new hotness sample
        page_median_data[page_addr].insertValue(hotness);

        short new_median = page_median_data[page_addr].getMedian();
        bkt_idx_after = get_bkt_idx(new_median);

        // Optionally update the short in page_bkt_pair with the new median
        // or something else. For example:
        it->second.first = static_cast<short>(new_median);
#endif
        if (bkt_idx_before != bkt_idx_after)
        {
            if (bkt_idx_before >= 0 && bkt_idx_before < NUM_BUCKETS &&
                bkt_page_num_pair[bkt_idx_before] > 0)
            {
                bkt_page_num_pair[bkt_idx_before]--;
            }
            bkt_page_num_pair[bkt_idx_after]++;
        }
    }
    else if (!insert_if_exists) // skip checking if insert_if_exists == true
    {                           // true: Newly inserted page
        short bkt_idx = 0;
#if defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 0)
        // --- Accumulated Hotness ---
        bkt_idx = get_bkt_idx(hotness);
#elif defined(PAGE_HOTNESS_DETER) && (PAGE_HOTNESS_DETER == 1)
        // --- Median Hotness ---
        auto &medianTracker = page_median_data[page_addr];
        medianTracker.insertValue(hotness);
        short median = medianTracker.getMedian();
        bkt_idx = get_bkt_idx(median);
#endif
        bkt_page_num_pair[bkt_idx]++;
    }
}

// not used
extern "C" void insert_into_bucket_only_exists(uintptr_t page_addr, short hotness)
{
    auto it = page_bkt_pair.find(page_addr);
    if (it != page_bkt_pair.end())
    {
        short bkt_idx_before = get_bkt_idx(it->second.first);
        it->second.first += hotness;
        short bkt_idx_after = get_bkt_idx(it->second.first);
        if (bkt_idx_before != bkt_idx_after)
        {
            if (!(bkt_idx_before == 0 && bkt_page_num_pair[bkt_idx_before] == 0))
            {
                bkt_page_num_pair[bkt_idx_before]--; // Only decrement if bkt_idx_before is valid
            }
            bkt_page_num_pair[bkt_idx_after]++; // Always increment the new bucket
        }
        // else if (bkt_idx_before == 0 || bkt_idx_after == 0)
        // {
        //     fprintf(stderr, "before: %d, after: %d\n", bkt_idx_before, bkt_idx_after);
        // }
    }
}
static int demo_pages_split[11] = {0};
static int promo_pages_split[11] = {0};

extern "C" int determine_split_eager(bool check_lazy, int free_dram_pages)
{
    int total_pages = get_pages_bkt_size();
    for (int i = 0; i < 10; i++) // reset split array
    {
        demo_pages_split[i] = 0;
        promo_pages_split[i] = 0;
    }

    for (auto &it : page_bkt_pair)
    {
        short bkt_idx = get_bkt_idx(it.second.first);

        if (!it.second.second.first) // in DRAM
        {
            if (check_lazy && !it.second.second.second)
                continue;
            // if (bkt_idx == 0)
            //     demo_pages_split[0]++;
            // if (bkt_idx <= 1)
            //     demo_pages_split[1]++;
            // if (bkt_idx <= 2)
            //     demo_pages_split[2]++;
            // if (bkt_idx <= 3)
            //     demo_pages_split[3]++;
            // if (bkt_idx <= 4)
            //     demo_pages_split[4]++;
            // if (bkt_idx <= 5)
            //     demo_pages_split[5]++;
            // if (bkt_idx <= 6)
            //     demo_pages_split[6]++;
            // if (bkt_idx <= 7)
            //     demo_pages_split[7]++;
            // if (bkt_idx <= 8)
            //     demo_pages_split[8]++;
            // if (bkt_idx <= 9)
            //     demo_pages_split[9]++;
            // for (int i = 0; i <= 9; i++)
            // {
            //     if (bkt_idx <= i)
            //     {
            //         demo_pages_split[i]++;
            //     }
            // }
            for (int i = bkt_idx; i <= 9; i++)
            {
                demo_pages_split[i]++;
            }
        }
    }
    for (int i = 0; i < 10; i++) // here we don't consider largest bucket
    {
        promo_pages_split[i] = total_pages - demo_pages_split[i];
    }
    for (int i = 0; i < 10; i++)
    {
        fprintf(stderr, "demo: %d, promo: %d\n", demo_pages_split[i], promo_pages_split[i]);
    }
    fprintf(stderr, "\n");
    // find the first bucket index that demo_size + free_dram will accomodate promo_size
    int found = 0;
    for (int i = 0; i < 10; i++)
    {
        if (demo_pages_split[i] + free_dram_pages >= promo_pages_split[i]) // find the first bucket idx that can take all promo pages
        {
            fprintf(stderr, "demo_pages_split[%d]: %d, free_pages: %d\n", i, demo_pages_split[i], free_dram_pages);
            return i;
        }
        found = i;
    }
    return found;
}

extern "C" void populate_mig_pages_eager(void **pages, int *size, int *free_dram_pages, int bkt_split, bool is_promo)
{
    if (!is_promo)
    {
        for (auto &it : page_bkt_pair)
        {
            short bkt_idx = get_bkt_idx(it.second.first);
            if (bkt_idx <= bkt_split && !it.second.second.first) // is cold && in DRAM
            // if (bkt_idx <= bkt_split) // is cold
            {
                *pages = (void *)it.first;
                pages++;
                (*size)++;
            }
        }
        // *free_dram_pages += *demo_size; // no need, re-calculate later for promo
    }
    else
    {
        int total_avail_pages = *free_dram_pages;
        fprintf(stderr, "total_avail_pages: %d\n", total_avail_pages);
        for (int i = 10; i >= 0; i--)
        {
            total_avail_pages -= bkt_page_num_pair[i];
            if (total_avail_pages < 0)
            {
                hot_bkt_idx_position[0] = i;
                hot_bkt_idx_position[1] = total_avail_pages + bkt_page_num_pair[i];
                break;
            }
        }
        fprintf(stderr, "trying to promote bkt idx larger than: %d\n", hot_bkt_idx_position[0]);
        // Promote pages from CXL based on hottest bucket first
        for (auto &it : page_bkt_pair)
        {
            if ((*free_dram_pages) <= 0)
                break;
            short bkt_idx = get_bkt_idx(it.second.first);
            // Promote from buckets hotter than the determined hot bucket index
            if (bkt_idx > hot_bkt_idx_position[0] && it.second.second.first)
            // if (bkt_idx > hot_bkt_idx_position[0])
            {
                *pages = (void *)it.first;
                pages++;
                (*size)++;
                it.second.second.second = false;
                (*free_dram_pages)--;
            }
        }
        // Promote pages from the current "hot bucket" until free DRAM pages are exhausted
        if (*free_dram_pages > 0)
        {
            for (auto &it : page_bkt_pair)
            {
                short bkt_idx = get_bkt_idx(it.second.first);

                if (bkt_idx == hot_bkt_idx_position[0] && it.second.second.first && *free_dram_pages > 0)
                // if (bkt_idx == hot_bkt_idx_position[0] && *free_dram_pages > 0)
                {
                    *pages = (void *)it.first;
                    pages++;
                    (*size)++;
                    it.second.second.second = false;
                    (*free_dram_pages)--;
                }

                if (*free_dram_pages <= 0)
                    break;
            }
        }
    }
}

extern "C" void populate_mig_pages_lazy(void **pages, int *size, int *free_dram_pages, int bkt_split, bool is_promo)
{
    if (first_demo)
    {
        populate_mig_pages_eager(pages, size, free_dram_pages, bkt_split, is_promo);
        first_demo = false;
        return;
    }
    if (!is_promo) // Demote cold pages from DRAM
    {
        for (auto &it : page_bkt_pair)
        {
            short bkt_idx = get_bkt_idx(it.second.first);
            if (bkt_idx <= bkt_split && !it.second.second.first) // is cold && in DRAM
            // if (bkt_idx <= bkt_split) // is cold
            {
                if (it.second.second.second) // if hit again
                {
                    *pages = (void *)it.first;
                    pages++;
                    (*size)++;
                    it.second.second.second = false;
                }
                else
                {
                    it.second.second.second = true;
                }
            }
        }
        // *free_dram_pages += *size; // no need
    }
    else
    {
        // Determine how many pages can be promoted based on available DRAM pages
        int total_avail_pages = *free_dram_pages;
        fprintf(stderr, "total_avail_pages: %d\n", total_avail_pages);
        for (int i = 10; i >= 0; i--)
        {
            total_avail_pages -= bkt_page_num_pair[i];
            if (total_avail_pages < 0)
            {
                hot_bkt_idx_position[0] = i;
                hot_bkt_idx_position[1] = total_avail_pages + bkt_page_num_pair[i];
                break;
            }
        }
        // Promote pages from CXL based on hottest bucket first
        for (auto &it : page_bkt_pair)
        {
            short bkt_idx = get_bkt_idx(it.second.first);
            if (*free_dram_pages <= 0)
                break;
            // Promote from buckets hotter than the determined hot bucket index
            if (bkt_idx > hot_bkt_idx_position[0] && it.second.second.first)
            // if (bkt_idx > hot_bkt_idx_position[0])
            {
                *pages = (void *)it.first;
                pages++;
                (*size)++;
                it.second.second.second = false;
                (*free_dram_pages)--;
            }
        }
        // Promote pages from the current "hot bucket" until free DRAM pages are exhausted
        if (*free_dram_pages > 0)
        {
            for (auto &it : page_bkt_pair)
            {
                short bkt_idx = get_bkt_idx(it.second.first);

                if (bkt_idx == hot_bkt_idx_position[0] && it.second.second.first && *free_dram_pages > 0)
                // if (bkt_idx == hot_bkt_idx_position[0] && *free_dram_pages > 0)
                {
                    *pages = (void *)it.first;
                    pages++;
                    (*size)++;
                    it.second.second.second = false;
                    (*free_dram_pages)--;
                }

                if (*free_dram_pages <= 0)
                    break;
            }
        }
    }
}

extern "C" void free_pages_bkt()
{
    page_bkt_pair.clear();
}

extern "C" unsigned int get_pages_bkt_size()
{
    return page_bkt_pair.size();
}

extern "C" void reset_pages_bkt_hotness()
{
    fprintf(stderr, "resetting hotness\n");
    for (auto it = page_bkt_pair.begin(); it != page_bkt_pair.end(); ++it)
    {
        it->second.first = 0;
    }
}

extern "C" void page_bkt_cooling(float cooling_weight)
{
    fprintf(stderr, "page bkt cooling\n");
    for (auto it = page_bkt_pair.begin(); it != page_bkt_pair.end(); ++it)
    {
        short bkt_idx_before = get_bkt_idx(it->second.first);
        it->second.first *= cooling_weight;
        short bkt_idx_after = get_bkt_idx(it->second.first);
        if (bkt_idx_before != bkt_idx_after)
        {
            bkt_page_num_pair[bkt_idx_before]--;
            bkt_page_num_pair[bkt_idx_after]++;
        }
    }
}

extern "C" void set_location_pages_bkt(uintptr_t page, bool location)
{
    auto it = page_bkt_pair.find(page);
    if (it != page_bkt_pair.end())
    {
        if (location)
            it->second.second.first = 1;
        else
            it->second.second.first = 0;
        // // clear hotness
        // it->second.first = 0;
    }
}

extern "C" void print_bucket_stat()
{
    fprintf(stderr, "bucket stat:\n");
    int total = 0;
    for (int i = 0; i < 11; i++)
    {
        total += bkt_page_num_pair[i];
        fprintf(stderr, "%d ", bkt_page_num_pair[i]);
    }
    fprintf(stderr, "\ntotal: %d\n", total);
}
