#!/usr/bin/env python3
"""Certify private integer rounding for the fixed KeyBreak 2.154631 grid.

Here n is the bit length of the arithmetic input. The certificate requires
n.bit_length() >= MIN_N_BITS and never constructs n or the arithmetic input.
It checks the same integer group construction as check_integer_schedule.
The analytic supply of primes in the allocated bands is a separate input.

Let q=(n/mb)^(1/3), mb=n.bit_length(). The degree rounding gives
delta*q <= d < delta*q+2 <= 2*q. Since kappa*delta > 1, k0 >= q.
The inequalities n >= 8*d+12 and k0 <= d give e0 >= n/(4*d).
Consequently t/e0 <= 16/q and e0 >= q^2/8. The lower bound on
2^(mb-1)/mb proves all these envelopes without materializing the powers.

Exactly Lx = k0*(e0+1)+r with 0 <= r < k0. For group allocation A_i
and exponent E_i, count_base=ceil(A_i/E_i), count=count_base+
ceil(count_base/count_bits). Writing shortfall=count*E_i-A_i, the
width is floor(2*(shortfall+count)/count). The added count ensures
shortfall >= count_base*E_i/count_bits, so 2*count_bits*(width+1)
is greater than 4*count_base*E_i/count, and count <= 2*count_base.
Flooring also gives shortfall <= floor(count*width/2) <= shortfall+count.
The upper width bound used below is width+1 <= E_i*(2/m+4/K)+3 whenever
count_bits >= m and count_base >= K. It follows from the two ceilings in
the count and count_base*E_i-A_i < E_i.
"""

from fractions import Fraction as F


GROUPS = 262_144
COUNT_BITS = 263_000
Q_EXPONENT = COUNT_BITS + 20
MIN_N_BITS = 3 * Q_EXPONENT + 22
COUNT_FLOOR = 1 << 40
E0_FLOOR = 1 << 60
T_OVER_E0 = F(1, 1 << 40)

delta, kappa, beta, alpha, gamma = map(F, "1.36252214 .79430825 .66779525506 .500000001 .68401159399".split())
top_slope, height, start, first_floor = map(F, ".78 .6441958804 .002 .00000399".split())
h, slack, target = map(F, ".7848525113 .000000002 2.154631".split())


def check_size_envelope():
    # The ratio 2^(mb-1)/mb increases with mb.
    assert MIN_N_BITS - 1 - MIN_N_BITS.bit_length() >= 3 * Q_EXPONENT
    assert 1 < delta < F(3, 2) and kappa * delta > 1 and kappa < 1
    assert Q_EXPONENT >= 44 and 2 * Q_EXPONENT - 3 >= E0_FLOOR.bit_length() - 1
    assert T_OVER_E0 == F(1, 1 << 40)


def check_grid():
    step = (1 - start) / (GROUPS - 1)
    loss = 2 * kappa * delta / 3
    weight = h * step
    length = GROUPS - 1
    squares = (length * start**2 + start * step * length * (length - 1)
               + step**2 * length * (length - 1) * (2*length - 1) / 6)
    last_fraction = (loss - weight * squares) / loss
    regular_ratio = weight / loss
    factor_ratio = length * regular_ratio + last_fraction
    assert last_fraction > 0 and min(regular_ratio, last_fraction) > F(1, 1 << 18)

    lowest_scale = start**2
    e0_round = F(1, E0_FLOOR)
    # Before flooring, A_i >= scale*r_i*k0*e0. This exceeds two,
    # so A_i/E_i > k0*r_i-1, including the terminal allocation.
    assert lowest_scale * min(regular_ratio, last_fraction) * COUNT_FLOOR * E0_FLOOR > 2
    assert lowest_scale * E0_FLOOR >= 1
    assert Q_EXPONENT - 18 > COUNT_BITS > COUNT_FLOOR.bit_length()

    base_bound = beta * T_OVER_E0 + e0_round
    height_bound = height * T_OVER_E0
    assert base_bound < first_floor
    width_rate = F(2, COUNT_BITS) + F(4, COUNT_FLOOR)

    checks = (
        "disjoint dyadic bands",
        "band above local box",
        "local box above capped child",
        "local box above base",
        "global top child",
        "local curve budget",
    )
    margins = [None] * len(checks)
    previous = first_floor
    for i in range(GROUPS):
        scale = (start + i * step)**2
        ratio = 1 + top_slope * scale
        raw_upper = alpha * scale + gamma * base_bound
        raw_lower = alpha * (scale - e0_round)
        child_bound = max(base_bound, (raw_upper + height_bound) / ratio + e0_round)
        curve_budget = target - delta*beta - delta*ratio/3 - 2*slack
        assert curve_budget > 0
        values = (
            scale * (1 - width_rate) - previous - 5 * e0_round,
            scale * (1 - width_rate) - raw_upper - 5 * e0_round,
            raw_lower - child_bound - 6 * e0_round,
            raw_lower - base_bound - e0_round,
            # The unrounded local child is bounded by the global child
            # precisely when alpha*e0 >= top_slope*(gamma*base+th/d).
            alpha - top_slope * (gamma * base_bound + height_bound),
            curve_budget**2 - h**2 * child_bound,
        )
        for j, value in enumerate(values):
            assert value > 0, (i, checks[j], value)
            if margins[j] is None or value < margins[j]:
                margins[j] = value
        previous = scale
    assert previous == 1 and 2*alpha > 1

    # E_i loses at most the same relative fraction at every group.
    # Only the terminal allocation gains from the size floors. Its gain
    # is less than GROUPS/e0 < 1 after dividing by its exponent E_i=e0.
    # Allow one ceiling per group at each of the two count roundings.
    denominator = 1 - e0_round / lowest_scale
    rounded_base = factor_ratio * (1 + 2 * e0_round) / denominator
    rounded_base += F(GROUPS + 1, COUNT_FLOOR)
    rounded_cap = (1 + F(1, COUNT_BITS)) * rounded_base + F(GROUPS, COUNT_FLOOR)
    assert F(GROUPS, E0_FLOOR) < 1 and rounded_cap < 2

    print(f"{GROUPS} groups certified for n.bit_length() >= {MIN_N_BITS}")
    for label, margin in zip(checks, margins, strict=True):
        print(f"{label}: minimum normalized slack {float(margin):.10g}")
    print(f"Rounded factor count is at most {float(rounded_cap):.9f} * k0 (cap 2 * k0)")


if __name__ == "__main__":
    check_size_envelope()
    check_grid()
