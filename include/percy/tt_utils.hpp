#pragma once

namespace percy
{
    
    template<typename TT>
    static inline bool is_normal(const TT& tt)
    {
        return !kitty::get_bit(tt, 0);
    }

}
