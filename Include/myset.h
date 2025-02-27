#pragma once
#ifndef MYSET_H
#define MYSET_H
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C"
{
#endif
    // global_unordered_set
    void insert_into_global(uintptr_t value);
    int check_in_global(uintptr_t value);
    int check_in_global_safe(uintptr_t value);
    void free_global();
    int valid_global_set();
    unsigned int get_global_size();
    void erase_from_global(uintptr_t value);
    void erase_from_global_safe(uintptr_t value);
    void print_global_addr(FILE *fd, int round);

    void reset_all_temps_func();

    // global_unordered_map
    void insert_into_map(uintptr_t key, bool val);
    int check_in_map(uintptr_t value);
    void erase_from_map(uintptr_t value);
    void free_map();
    unsigned int get_map_size();

    // pages_loc_hotness
    // void insert_into_pages(uintptr_t page_addr, short hotness);
    void insert_into_pages(uintptr_t page_addr, short hotness, bool location);
    void insert_into_pages_only_exists(uintptr_t page_addr, short hotness);
    int check_in_pages(uintptr_t page);
    void erase_from_pages(uintptr_t page);
    void free_pages();
    unsigned int get_pages_size();
    // bool get_location_pages(void *page);
    void populate_mig_pages(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, short split);
    void populate_mig_pages_wo_hit_again(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, short split);
    void get_page_hotness_bound(short *min, short *max);
    void print_all_pages_hotness();
    void reset_pages_hotness();
    void page_temp_cooling(float cooling_weight);
    void set_location_pages(uintptr_t page, bool location);

    void populate_hotness_vec();
    short get_avg_hotness();
    short get_median_hotness();
    short get_mode_hotness();
    short get_2nd_mode_hotness();
    void clear_hotness_vec();
    void dump_page_hotness(FILE *fd);

    void reset_bkt_page_num_pair();
    short get_bkt_idx(short hotness);
    void insert_into_bucket(uintptr_t page_addr, short hotness, bool location, bool insert_if_exists);
    // not used
    void insert_into_bucket_only_exists(uintptr_t page_addr, short hotness);
    // void populate_mig_pages_eager(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, int *free_dram_pages, int bkt_split);
    // void populate_mig_pages_lazy(void **demote_pages, void **promote_pages, int *demo_size, int *promo_size, int *free_dram_pages, int bkt_split);
    void populate_mig_pages_eager(void **pages, int *size, int *free_dram_pages, int bkt_split, bool is_promo);
    void populate_mig_pages_lazy(void **pages, int *size, int *free_dram_pages, int bkt_split, bool is_promo);
    void free_pages_bkt();
    unsigned int get_pages_bkt_size();
    void reset_pages_bkt_hotness();
    void page_bkt_cooling(float cooling_weight);
    void set_location_pages_bkt(uintptr_t page, bool location);
    void print_bucket_stat();
    int determine_split_eager(bool check_lazy, int free_dram_pages);

#ifdef __cplusplus
}
#endif

#endif // MYSET_H
