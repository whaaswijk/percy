#pragma once

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-pedantic"
#include <kitty/kitty.hpp>
#pragma GCC diagnostic pop

namespace percy
{
    
    template<typename TT>
    static inline bool is_normal(const TT& tt)
    {
        return !kitty::get_bit(tt, 0);
    }

}
