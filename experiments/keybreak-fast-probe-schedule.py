#!/usr/bin/env python3
"""Check two strict KeyBreak schedules with exact rational inequalities."""

from fractions import Fraction
from math import ceil, floor


def check_schedule(values):
    (
        degree, top_ratio, cutoff, slope, offset, smooth_ratio, height,
        floor_ratio, first_stage, curve_bound, target,
    ) = map(Fraction, values.split())
    epsilon = Fraction(1, 100)
    slack = Fraction(1, 20_000)
    stages = 128
    half = Fraction(1, 2)

    log_radix = degree ** -3
    top = top_ratio * log_radix
    top_box = slope * top
    first_child = top_box / smooth_ratio
    first_internal_box = slope * first_child
    gaussian_height = log_radix + 2 * top_box
    bottom_box = (slope + offset) * cutoff

    assert height > gaussian_height
    assert (smooth_ratio - slope - offset) * cutoff > height
    assert top_box < log_radix
    assert top < log_radix
    assert 2 * top_box > top
    assert 2 * top_box > 3 * first_child
    assert degree**3 * top_box < half
    assert slope > half
    assert bottom_box > cutoff
    assert bottom_box * (smooth_ratio - 1) > height
    assert first_child < log_radix
    assert floor_ratio > slope / smooth_ratio
    assert floor_ratio > slope - slope**2 / smooth_ratio

    rational_loss_at_bottom = log_radix / (3 * cutoff)
    bottom_geometry = 2 * bottom_box - cutoff
    assert bottom_geometry - rational_loss_at_bottom - smooth_ratio / 3 > Fraction(1, 50)
    assert bottom_geometry > rational_loss_at_bottom

    internal_error = (1 + epsilon) * first_child - (half - epsilon) * (log_radix + first_internal_box)
    top_error = (1 + epsilon) * first_child - (half - epsilon) * (log_radix + top_box - top)
    assert internal_error < -log_radix / 4
    assert top_error < -log_radix / 4
    endpoint_error = (1 + epsilon) * log_radix - (half - epsilon) * (gaussian_height + bottom_box)
    assert endpoint_error < -Fraction(1, 25)

    grid = [first_stage + (1 - first_stage) * i / (stages - 1) for i in range(stages)]
    squared_grid = [point**2 for point in grid]
    assert squared_grid[0] > floor_ratio
    assert all(point != slope for point in squared_grid)
    curve_actual_sq = Fraction(20_001, 10_000)**2 * 2 * top_ratio / (3 * degree)
    assert curve_actual_sq < curve_bound**2

    shape_loss = degree / (3 * top_ratio)
    weights = [curve_bound * (grid[i + 1] - grid[i]) for i in range(stages - 1)]
    weights.append(shape_loss - sum(weight * point for weight, point in zip(weights, squared_grid)))
    fractions = [weight * point / shape_loss for weight, point in zip(weights, squared_grid)]
    assert all(weight > 0 for weight in weights)
    assert sum(fractions) == 1
    assert sum(weights) < 2 * shape_loss

    base = degree * cutoff
    algebraic_loss = degree * smooth_ratio / 3
    rational_loss = degree * (log_radix + first_internal_box) / (3 * cutoff)
    private_cost = max(
        base + sum(weights[i:]) + slack + curve_bound * grid[i]
        for i in range(stages)
    )
    raw_descent_cost = base + algebraic_loss + rational_loss + 2 * slack
    algebraic_cost_base = base + algebraic_loss + 2 * slack
    assert algebraic_cost_base < target
    assert curve_bound**2 * slope / smooth_ratio < (target - algebraic_cost_base)**2
    assert max(private_cost, raw_descent_cost, 2 * degree,
               base + 4 * degree / 3, Fraction(13, 5) * base, 2 * base) < target
    print(f"{float(target):.3f} schedule: private {float(private_cost):.9f}, "
          f"raw {float(raw_descent_cost):.9f}, bottom margin "
          f"{float(bottom_geometry - rational_loss_at_bottom - smooth_ratio / 3):.9f}")

    for bit_length in (2**12_000, 2**16_000):
        bit_length_bits = bit_length.bit_length()
        low, high = 0, bit_length
        target_cube = degree**3 * bit_length / bit_length_bits
        while high - low > 1:
            mid = (low + high) // 2
            if mid**3 >= target_cube:
                high = mid
            else:
                low = mid
        d = high + (high % 2 == 0)
        t = d * bit_length_bits
        k0 = ceil(d / (2 * top_ratio))
        e0 = (bit_length - 5) // (2 * k0) - 1
        ebase = ceil(cutoff * t)
        target_height = floor(height * d * t)
        e = e0
        while e > ebase:
            raw_box = slope * e + offset * ebase
            child = max(ebase, ceil((raw_box + Fraction(target_height, d)) / smooth_ratio))
            assert child < e
            assert ceil(raw_box) - child >= 6
            e = child

        lower_denom = ceil(slope * e0 + offset * ebase) - 1
        upper_denom = lower_denom + 1
        target_bits = (bit_length - 1) // 2 - 2
        assigned_bits = [floor(fraction * target_bits) for fraction in fractions[:-1]]
        assigned_bits.append(target_bits - sum(assigned_bits))
        previous_upper = ceil(floor_ratio * e0)
        total_factors = 0
        for size, point in zip(assigned_bits, squared_grid):
            upper = floor(point * e0)
            kbase = ceil(Fraction(size, upper))
            kbits = kbase.bit_length()
            count = kbase + ceil(Fraction(kbase, kbits))
            shortfall = count * upper - size
            width = 2 * (shortfall + count) // count
            lower = upper - width - 1
            assert lower >= previous_upper
            assert upper <= lower_denom or lower >= upper_denom
            assert shortfall <= count * width // 2 <= shortfall + count
            assert 2 * kbits * (width + 1) >= upper
            previous_upper = upper
            total_factors += count
        assert total_factors <= 2 * k0


check_schedule("1.093 .48 .682 .501 1.09 3.258 1.136 .502 .709 1.0823 2.357")
check_schedule("1.086 .468 .693 .5005 1.059 3.218 1.148 .423 .651 1.0722 2.341")
