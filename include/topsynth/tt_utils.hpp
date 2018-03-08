#pragma once

namespace topsynth
{
    
    template<typename TT>
    static inline bool is_normal(const TT& tt)
    {
        return !kitty::get_bit(tt, 0);
    }

}
