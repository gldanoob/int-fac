#!/usr/bin/env python3
"""Check arithmetic for the 2.159 schedule conditional on the private ECM bound."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path


def check_schedule(
    *,
    field="1.3032 .8786 .678 .5001 .7222",
    descent=".5005 2.15 2.2684 .70904",
    recognition=".7631 1.07918 .0001 2.159",
    period_bounds=".7089 .452",
    algebraic_exponent="2.0001", private_exponent="1.4143",
    stages=128, first_knot=".0662", first_floor=".0043", minimum_mean=".001",
    matrix_exponent="2.4", rounded_exponents=(12_000, 16_000),
):
    delta, kappa, beta, alpha, gamma = map(F, field.split())
    top_slope, high_ratio, low_ratio, height = map(F, descent.split())
    h_private, h_algebraic, slack, target = map(F, recognition.split())
    height_lower, radix_upper = map(F, period_bounds.split())
    top_ratio = 1 + top_slope
    start = F(first_knot)
    grid = [start + (1 - start) * i / (stages - 1) for i in range(stages)]
    scales = [z**2 for z in grid]
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top_ratio
    v1 = alpha * y1
    y2 = v1 / high_ratio
    slope_sum = alpha + gamma
    gaussian_height = radix * (1 + 2 * v0)

    assert height_lower < gaussian_height < height and radix < radix_upper
    assert 2 * v0 < 1 and y0 < 1
    fixed_point_margin = (low_ratio - slope_sum) * beta - height
    assert fixed_point_margin > 0 and (low_ratio - 1) * slope_sum * beta > height
    assert low_ratio > high_ratio > top_ratio > F(3, 2)
    assert 2 * alpha > 1 and slope_sum > 1

    g12 = F("1.01") * y1 - F(".49")
    assert g12 < -F(".1")
    g17 = []
    for scale in scales:
        parent, box = scale * y0, scale * v0
        child = box / (1 + top_slope * scale)
        g17.append(F("1.01") * child - F(".49") * (1 + box - parent))
        assert 0 < child < box < parent < 1
        assert child <= y1 and 3 * child < 2 * v0 and 2 * box > parent
    assert max(g17) < -F(".1")
    mean = (2 * slope_sum - 1) * beta - low_ratio / 3 - radix / (3 * beta)
    period = F(".49") * (height_lower + slope_sum * beta) - F("1.01") * radix_upper
    assert mean > F(minimum_mean) and period > F(".04")
    print(f"height {float(gaussian_height):.9f}, fixed-point margin {float(fixed_point_margin):.9f}, "
          f"bottom mean {float(mean):.9f}, period margin {float(period):.9f}")
    print(f"G.12 error coefficient <= {float(g12):.9f}, G.17 error coefficient <= {float(max(g17)):.9f}")

    shape_loss = 2 * kappa * delta / 3
    weights = [h_private * (right - left) for left, right in zip(grid, grid[1:])]
    weights.append(shape_loss - sum(a * w for a, w in zip(scales, weights)))
    fractions = [a * w / shape_loss for a, w in zip(scales, weights)]
    assert F(private_exponent)**2 > 2
    assert F(private_exponent)**2 * 2 * y0 / (3 * delta) < h_private**2
    assert F(algebraic_exponent)**2 * 2 * y0 / (3 * delta) < h_algebraic**2
    count_ratio = sum(weights) / shape_loss
    assert min(weights) > 0 and sum(fractions) == 1 and count_ratio < 2
    tail = F(0)
    private = []
    for weight, knot in zip(reversed(weights), reversed(grid), strict=True):
        tail += weight
        private.append(b + tail + h_private * knot + slack)
    assert max(private) == min(private)

    top, high, low = (b + delta * ratio / 3 + 2 * slack for ratio in (top_ratio, high_ratio, low_ratio))
    rational_scale = 3 * delta * b
    costs = {
        "private": max(private),
        "top raw": top + (1 - (1 - alpha) * scales[0] * y0) / rational_scale,
        "high raw": high + (1 + v1) / rational_scale,
        "low raw": low + 1 / rational_scale,
        "low algebraic": low,
        "probe setup": 2 * delta / 3,
        "retained characters": b + 2 * delta / 3,
        "elimination": F(matrix_exponent) * b,
        "extraction": 2 * b,
    }
    assert max(costs.values()) < target
    for label, cost in costs.items():
        print(f"{label}: {float(cost):.9f}")
    for label, base, child in (("top algebraic", top, y1), ("high algebraic", high, y2)):
        curve_sq = h_algebraic**2 * child / y0
        assert base < target and curve_sq < (target - base)**2
        print(f"{label}: {float(base) + float(curve_sq)**.5:.9f}")
    print(f"private factor-count ratio: {float(count_ratio):.9f} of the 2 limit")

    replay = run_path(str(Path(__file__).with_name("keybreak-tiered-descent.py")))["check_integer_schedule"]
    for exponent in rounded_exponents:
        replay(
            2**exponent, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
            top_ratio=top_ratio, high_ratio=high_ratio, low_ratio=low_ratio, height=height,
            h=h_algebraic, target=target, scales=scales, fractions=fractions, top_ratio_slope=top_slope,
            factor_cap=2, first_scale=F(first_floor), cap_slack=slack,
        )


if __name__ == "__main__":
    check_schedule()
