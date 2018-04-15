#pragma once

#include <bitset>
#include <array>
#include <cstdio>
#include "../sat_interface.hpp"
#include "../spec.hpp"
#include "../misc.hpp"

#define MAX_STEPS 20 // The maximum number of steps we'll synthesize

namespace percy
{
    template<long unsigned N>
    static inline void
    clear_assignment(std::bitset<N>& fanin_asgn)
    {
        fanin_asgn.reset();
    }

    template<long unsigned N>
    static inline void
    next_assignment(std::bitset<N>& fanin_asgn)
    {
        for (int i = 0; i < N; i++) {
            if (fanin_asgn.test(i)) {
                fanin_asgn.set(i, false);
            } else {
                fanin_asgn.set(i);
                return;
            }
        }
    }

    template<long unsigned N>
    static inline bool
    is_zero(const std::bitset<N>& fanin_asgn)
    {
        return fanin_asgn.none();
    }

    template<long unsigned FI>
    void
    fanin_init(std::array<int, FI>& fanins, int max_fanin_id)
    {
        fanins[FI-1] = max_fanin_id--;
        for (int i = FI-2; i >= 0; i--) {
            fanins[i] = max_fanin_id--;
        }
    }

    template<long unsigned FI>
    void
    fanin_init(std::array<int, FI>& fanins, int max_fanin_id, int start_idx)
    {
        fanins[start_idx] = max_fanin_id--;
        for (int i = start_idx-1; i >= 0; i--) {
            fanins[i] = max_fanin_id--;
        }
    }

    template<long unsigned FI>
    bool
    fanin_inc(std::array<int, FI>& fanins, const int max_fanin_id)
    {
        int inc_idx = 0;

        for (int i = 0; i < FI; i++) {
            if (i < FI - 1) {
                if (fanins[i] < fanins[i + 1] - 1) {
                    fanins[i]++;
                    if (i > 0) {
                        fanin_init(fanins, i - 1, i - 1);
                    }
                    return true;
                }
            } else {
                if (fanins[i] < max_fanin_id) {
                    fanins[i]++;
                    fanin_init(fanins, i - 1, i - 1);
                    return true;
                }
            }
        }

        return false;
    }

    template<long unsigned FI>
    void
    print_fanin(const std::array<int, FI>& fanins)
    {
        for (int i = 0; i < FI; i++) {
            printf("%d ", fanins[i] + 1);
        }
    }

    template<long unsigned FI>
    void
    print_fanin(const typename dag<FI>::fanin* const fanins)
    {
        for (int i = 0; i < FI; i++) {
            printf("%d ", fanins[i] + 1);
        }
    }

}

