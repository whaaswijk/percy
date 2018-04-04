#pragma once

#include <bitset>
#include <array>
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
    bool
    fanin_inc(std::array<int, FI>& fanins, int top_idx, int max_fanin_id)
    {
        if (fanins[top_idx] < max_fanin_id) {
            fanins[top_idx]++;
            return true;
        }
        return false;
    }

    template<long unsigned FI>
    bool
    fanin_inc(std::array<int, FI>& fanins, int max_fanin_id)
    {
        auto top_idx = FI - 1;

        while (top_idx >= 0) {
            if (fanin_inc<FI>(fanins, top_idx, max_fanin_id)) {
                return true;
            }
            max_fanin_id--;
            top_idx--;
        }

        return false;
    }

}

