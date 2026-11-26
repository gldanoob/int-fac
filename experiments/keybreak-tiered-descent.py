#!/usr/bin/env python3
"""Check strict arithmetic margins for the tiered single-input KeyBreak schedule."""

from fractions import Fraction as F
from math import ceil, floor, isqrt


delta, kappa, beta, alpha, gamma = map(F, "1.133 .93 .715 .5005 .914".split())
top_ratio, high_ratio, low_ratio, height = map(F, "2.534 2.4 2.895 1.058".split())
epsilon, slack, target = map(F, ".01 .0001 2.268".split())
h = F(9, 8)
stages = 128
grid = [F(".1") + F(".9") * i / (stages - 1) for i in range(stages)]
scales = [z**2 for z in grid]
shape_loss = 2 * kappa * delta / 3
weights = [h * (right - left) for left, right in zip(grid, grid[1:])]
weights.append(shape_loss - sum(a * w for a, w in zip(scales, weights)))
fractions = [a * w / shape_loss for a, w in zip(scales, weights)]

b, radix = delta * beta, delta**-3
y0 = 1 / (2 * kappa)
v0 = alpha * y0
y1 = v0 / top_ratio
v1 = alpha * y1
y2 = v1 / high_ratio
slope_sum = alpha + gamma
gaussian_height = radix * (1 + 2 * v0)


def check_margins():
    assert F("1.057") < gaussian_height < height and 2 * v0 < 1 and y0 < 1
    assert radix < F(".69")
    assert (low_ratio - slope_sum) * beta > height
    assert (low_ratio - 1) * slope_sum * beta > height
    assert low_ratio > top_ratio > high_ratio > F(3, 2)
    assert 2 * alpha > 1 and slope_sum > 1

    lower = F(1, 2) - epsilon
    upper = 1 + epsilon
    g12_upper = upper * y1 - lower
    assert g12_upper < -F(1, 4)
    g17_error = []
    for scale in scales:
        parent, box, child = scale * y0, scale * v0, scale * y1
        g17_error.append(upper * child - lower * (1 + box - parent))
        assert 0 < child < box < parent < 1
        assert 3 * child < 2 * box and 2 * box > parent
    assert max(g17_error) < -F(1, 4)

    bottom_geometry = (2 * slope_sum - 1) * beta
    bottom_mean = bottom_geometry - low_ratio / 3 - radix / (3 * beta)
    period_margin = lower * (F("1.057") + slope_sum * beta) - upper * F(".69")
    assert bottom_mean > F(1, 50)
    assert period_margin > F(1, 25)
    print(f"height {float(gaussian_height):.9f}, bottom mean {float(bottom_mean):.9f}, "
          f"period margin {float(period_margin):.9f}")
    print(f"G.12 error coefficient <= {float(g12_upper):.9f}, "
          f"G.17 error coefficient <= {float(max(g17_error)):.9f}")


def check_costs():
    assert F("2.0001")**2 * 2 * y0 / (3 * delta) < h**2
    count_ratio = sum(weights) / shape_loss
    assert min(weights) > 0 and sum(fractions) == 1 and count_ratio < 2
    private = [b + sum(weights[i:]) + h * grid[i] + slack for i in range(stages)]
    assert min(private) == max(private)

    rational_top = (1 - (1 - alpha) * scales[0] * y0) / (3 * delta * b)
    rational_high = (1 + v1) / (3 * delta * b)
    rational_low = 1 / (3 * delta * b)
    top = b + delta * top_ratio / 3 + 2 * slack
    high = b + delta * high_ratio / 3 + 2 * slack
    low = b + delta * low_ratio / 3 + 2 * slack
    costs = {
        "private": max(private),
        "top raw": top + rational_top,
        "high raw": high + rational_high,
        "low raw": low + rational_low,
        "low algebraic": low,
        "probe setup": 2 * delta,
        "retained characters": b + 2 * delta / 3,
        "elimination": F("2.6") * b,
        "extraction": 2 * b,
    }
    assert max(costs.values()) < target
    for label, cost in costs.items():
        print(f"{label}: {float(cost):.9f}")
    for label, base, child in (("top algebraic", top, y1), ("high algebraic", high, y2)):
        curve_squared = h**2 * child / y0
        assert base < target and curve_squared < (target - base)**2
        print(f"{label}: {float(base) + float(curve_squared)**.5:.9f}")
    print(f"private factor-count ratio: {float(count_ratio):.9f} of the 2 limit")


def first_degree(n, mb, delta):
    degree_cube = delta**3 * n / mb
    radicand = floor(degree_cube)
    d = 1 << ((radicand.bit_length() + 2) // 3)
    while True:
        step = (2 * d + radicand // d**2) // 3
        if step >= d:
            break
        d = step
    if d**3 < degree_cube:
        d += 1
    return max(3, d | 1)


def check_integer_schedule(
    n, *, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
    top_ratio=top_ratio, high_ratio=high_ratio, low_ratio=low_ratio, height=height,
    h=h, target=target, scales=scales, fractions=fractions, top_ratio_slope=F(0),
    factor_cap=2, first_scale=F(0),
):
    mb = n.bit_length()
    d = first_degree(n, mb, delta)
    assert (d - 2)**3 * mb < delta**3 * n <= d**3 * mb
    t = d * mb
    k0 = ceil(kappa * d)
    e0 = (n - 5) // (2 * k0) - 1
    base = ceil(beta * t)
    th = floor(height * d * t)
    assert e0 > base and d >= 3

    def descent(parent, ratio):
        raw_box = alpha * parent + gamma * base
        box = ceil(raw_box)
        child = max(base, ceil((raw_box + F(th, d)) / ratio))
        assert child < parent and box >= child + 6 and box > base + 1 and 2 * box >= parent
        assert ratio * d * child >= th + d * raw_box
        curve_budget = target - delta * beta - delta * ratio / 3 - 2 * slack
        assert curve_budget > 0 and h**2 * child / e0 < curve_budget**2
        return box, child

    top_box, global_child = descent(e0, top_ratio)
    assert 2 * (th + d * top_box) <= n - 1
    assert max(top_box, e0) + 3 < (n - 1) // d - 1
    # Bound the source's height and conditioning guards without materializing large powers.
    assert ceil(F(n, d)) + 2 * top_box + 23 * mb + d + 11 < th
    cutoffs = [e0, global_child]
    high_count = low_count = 0
    while cutoffs[-1] > base:
        parent = cutoffs[-1]
        high = parent**2 > d * t**2
        _, child = descent(parent, high_ratio if high else low_ratio)
        high_count += high
        low_count += not high
        cutoffs.append(child)
    assert high_count > 0 and low_count > 0 and len(cutoffs) < n + 10
    assert cutoffs[1 + high_count] <= isqrt(d * t**2) < cutoffs[high_count]
    assert 2 * top_box > 3 * global_child + 20 * (len(cutoffs) + 10)**6 * t

    target_bits = (n - 1) // 2 - 2
    remaining = target_bits
    previous_upper = max(base, ceil(first_scale * e0))
    total_factors = 0
    passed_levels = set()
    for i, (a, fraction) in enumerate(zip(scales, fractions)):
        upper = floor(a * e0)
        size = remaining if i == len(scales) - 1 else floor(fraction * target_bits)
        remaining -= size
        count_base = ceil(F(size, upper))
        count_bits = count_base.bit_length()
        count = count_base + ceil(F(count_base, count_bits))
        shortfall = count * upper - size
        width = 2 * (shortfall + count) // count
        lower = upper - width - 1
        local_ratio = top_ratio - top_ratio_slope * (1 - a)
        local_box, local_child = descent(upper, local_ratio)
        assert lower >= previous_upper and lower >= local_box
        assert local_child <= global_child and local_child < lower
        assert shortfall <= count * width // 2 <= shortfall + count
        assert 2 * count_bits * (width + 1) >= upper
        previous_upper = upper
        total_factors += count

        # The largest local child can pass through each fitting global box unchanged.
        level = 1
        while level + 1 < len(cutoffs) and local_child <= cutoffs[level + 1]:
            level += 1
        passed_levels.add(level - 1)
        assert local_child <= cutoffs[level]
        assert local_child == base or local_child > cutoffs[level + 1]

    assert remaining == 0 and total_factors <= factor_cap * k0
    assert min(passed_levels) == 0 and max(passed_levels) > 0
    print(f"rounded schedule: {high_count} high, {low_count} low, {len(scales)} private allocations, "
          f"up to {max(passed_levels)} identity levels for a band maximum")


if __name__ == "__main__":
    check_margins()
    check_costs()
    for exponent in (12_000, 16_000):
        check_integer_schedule(2**exponent)
