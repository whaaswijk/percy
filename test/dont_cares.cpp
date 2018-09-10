#include <cstdio>
#include <percy/percy.hpp>
#include <cstdlib>

using namespace percy;

bool verify_simulated_dc_tt(
    const kitty::dynamic_truth_table& tt,
    const kitty::dynamic_truth_table& dc_tt,
    const kitty::dynamic_truth_table& dc_mask)
{
    for (int i = 0; i < tt.num_bits(); i++) {
        if (kitty::get_bit(dc_mask, i)) {
            continue;
        }
        assert(kitty::get_bit(dc_tt, i) == kitty::get_bit(tt, i));
    }

    return true;
}

void verify_dc(const kitty::dynamic_truth_table& tt, const kitty::dynamic_truth_table& dc_mask)
{
    assert(tt.num_vars() == dc_mask.num_vars());

    //printf("got truth table\t %s\n", kitty::to_binary(tt).c_str());
    //printf("got DC mask\t %s\n", kitty::to_binary(dc_mask).c_str());

    chain chain;
    spec spec;
    bmcg_wrapper solver;
    ssv_encoder encoder(solver);
    spec[0] = tt;

    const auto res = synthesize(spec, chain, solver, encoder);
    assert(res == success);
    //printf("found a %d-step chain\n", chain.get_nr_steps());
    const auto full_tt = chain.simulate()[0];
    assert(full_tt == tt);

    spec.set_dont_care(0, dc_mask);
    const auto dc_res = synthesize(spec, chain, solver, encoder);
    assert(dc_res == success);
    //printf("found a %d-step DC chain\n", chain.get_nr_steps());
    const auto dc_tt = chain.simulate()[0];
    //printf("DC simulation tt\t %s\n", kitty::to_binary(dc_tt).c_str());
    assert(verify_simulated_dc_tt(tt, dc_tt, dc_mask));
}

int
main(void)
{
    {
        kitty::dynamic_truth_table tt(3), dc(3);
        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt, &i, &i + 1);

            kitty::clear(dc);
            for (int i = 0; i < 8; i++) {
                const auto number = rand() % 100 + 1; // Random number between 1 and 100
                if (number <= 25) {
                    kitty::set_bit(dc, i);
                }
            }

            verify_dc(tt, dc);
        }
    }
    {
        kitty::dynamic_truth_table a(4), b(4), c(4), x(4), y(4), dc;

        kitty::create_nth_var(a, 0);
        kitty::create_nth_var(b, 1);
        kitty::create_nth_var(c, 2);
        kitty::create_nth_var(x, 3);

        y = (a & b & x) | (~a & c & x);
        dc = a & ~b & x | ~a & ~x;
        verify_dc(y, dc);
    }

    {
        // Even a random 6-input function can be made trivial by
        // using a don't care mask
        spec spec;
        chain c;
        bsat_wrapper solver;
        ssv_encoder encoder(solver);
        kitty::dynamic_truth_table tt(6), dc_mask(6);
        kitty::create_random(tt);
        dc_mask = ~dc_mask;
        spec[0] = tt;
        spec.set_dont_care(0, dc_mask);

        printf("got truth table\t %s\n", kitty::to_binary(tt).c_str());
        printf("got DC mask\t %s\n", kitty::to_binary(dc_mask).c_str());

        const auto result = synthesize(spec, c, solver, encoder);
        assert(result == success);
        const auto dc_tt = c.simulate()[0];
        printf("found a %d-step DC chain\n", c.get_nr_steps());
        printf("DC simulation tt\t %s\n", kitty::to_binary(dc_tt).c_str());
        verify_simulated_dc_tt(tt, dc_tt, dc_mask);
    }   
    return 0;
}

