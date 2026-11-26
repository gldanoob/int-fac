#!/usr/bin/env python3
"""Check the strict margins for the 2.250 single-input descent schedule."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path


def check_schedule():
    delta, kappa, beta, alpha, gamma = map(F, "1.33226 .74246 .61135 .5001 .88185".split())
    top_slope, high_ratio, low_ratio, height = map(F, ".86 2.4 2.54 .7078".split())
    h, slack, target = map(F, "1.16108 .0001 2.250".split())
    top_ratio = 1 + top_slope
    stages = 320
    grid = [F(".041") + F(".959") * i / (stages - 1) for i in range(stages)]
    scales = [z**2 for z in grid]
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top_ratio
    v1 = alpha * y1
    y2 = v1 / high_ratio
    slope_sum = alpha + gamma
    gaussian_height = radix * (1 + 2 * v0)

    assert F(".7077") < gaussian_height < height and radix < F(".423")
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
    period = F(".49") * (F(".7077") + slope_sum * beta) - F("1.01") * F(".423")
    assert mean > F(".001") and period > F(".04")
    print(f"height {float(gaussian_height):.9f}, fixed-point margin {float(fixed_point_margin):.9f}, "
          f"bottom mean {float(mean):.9f}, period margin {float(period):.9f}")
    print(f"G.12 error coefficient <= {float(g12):.9f}, G.17 error coefficient <= {float(max(g17)):.9f}")

    shape_loss = 2 * kappa * delta / 3
    weights = [h * (right - left) for left, right in zip(grid, grid[1:])]
    weights.append(shape_loss - sum(a * w for a, w in zip(scales, weights)))
    fractions = [a * w / shape_loss for a, w in zip(scales, weights)]
    assert F("2.0001")**2 * 2 * y0 / (3 * delta) < h**2
    count_ratio = sum(weights) / shape_loss
    assert min(weights) > 0 and sum(fractions) == 1 and count_ratio < 4
    private = [b + sum(weights[i:]) + h * grid[i] + slack for i in range(stages)]
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
        "elimination": F("2.6") * b,
        "extraction": 2 * b,
    }
    assert max(costs.values()) < target
    for label, cost in costs.items():
        print(f"{label}: {float(cost):.9f}")
    for label, base, child in (("top algebraic", top, y1), ("high algebraic", high, y2)):
        curve_sq = h**2 * child / y0
        assert base < target and curve_sq < (target - base)**2
        print(f"{label}: {float(base) + float(curve_sq)**.5:.9f}")
    print(f"private factor-count ratio: {float(count_ratio):.9f} of the 4 limit")

    replay = run_path(str(Path(__file__).with_name("keybreak-tiered-descent.py")))["check_integer_schedule"]
    for exponent in (12_000, 16_000):
        replay(
            2**exponent, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
            top_ratio=top_ratio, high_ratio=high_ratio, low_ratio=low_ratio, height=height,
            h=h, target=target, scales=scales, fractions=fractions, top_ratio_slope=top_slope,
            factor_cap=4, first_scale=F(".0016"),
        )


if __name__ == "__main__":
    check_schedule()
