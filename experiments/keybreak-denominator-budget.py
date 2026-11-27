"""Replay conditional one-coordinate KeyBreak budgets at seven window widths.

The width theta is the logarithmic size of the rational coordinate relative
to log N. The replay assumes the one-coordinate supply, prefix and split
hypotheses. It checks the charged ledger and sample integer roundings.
"""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path


# delta, kappa, beta, gamma, top, high, low, height, curve, ceiling
SCHEDULES = {
    ".810": "1.3771523 .9589197 .6694669 .643770 1.76100 1.97000 2.01395 .5825135 .710515 2.1091",
    ".805": "1.3775504 .9644071 .6695202 .642688 1.75920 1.96820 2.01035 .5808738 .708389 2.1079",
    ".801": "1.3778692 .9688511 .6695631 .641820 1.75770 1.96550 2.00747 .5795615 .706681 2.1069",
    ".751": "1.3818837 1.0288041 .6701163 .630964 1.73987 1.93183 1.97138 .5631284 .684784 2.0947",
    ".670": "1.3884914 1.1470267 .6710557 .613333 1.71448 1.87644 1.91276 .5364142 .646990 2.0748",
    ".668": "1.3886560 1.1503468 .6710791 .612898 1.71391 1.87506 1.91131 .5357536 .646018 2.0743",
    ".667": "1.3887384 1.1520151 .6710908 .612681 1.71363 1.87437 1.91059 .5354232 .645530 2.0741",
}


def check(theta, schedule, grid, replay):
    delta, kappa, beta, gamma, top, high, low, height, curve, ceiling = schedule
    alpha, factor_cost, slack = map(F, ".500005 1.414215 .000005".split())
    first_knot, first_floor, knot_count = F(".026"), F(".00067"), 1536
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top
    v1 = alpha * y1
    y2 = v1 / high
    slope = alpha + gamma
    actual_height = radix * (1 + 2 * v0)

    assert 0 < theta < 1
    assert factor_cost**2 > 2 and curve**2 > factor_cost**2 * 2 * y0 / (3 * delta)
    assert actual_height < height and 2 * alpha > 1 and 0 < 2 * v0 < 1
    assert 3 * y1 < 2 * v0 and low > high > top > F(3, 2)
    assert slope > 1 and (low - slope) * beta > height and (low - 1) * slope * beta > height
    bottom_mean = (2 * slope - 1) * beta - low / 3 - radix / (3 * beta)
    assert bottom_mean > F(".000015")
    assert F(".49") * (actual_height + slope * beta) - F("1.01") * radix > F(".04")
    assert F("1.01") * y1 - F(".49") < -F(".1")

    moment = theta * 2 * kappa * delta / 3
    scales, fractions, tail, gate = grid(moment, curve, first_knot, knot_count)
    assert first_floor < scales[0]
    factor_ratio = 2 * theta * tail / moment
    assert factor_ratio < 4
    for scale in scales:
        parent, box = scale * y0, scale * v0
        child = box / (1 + (top - 1) * scale)
        assert 0 < child < box < parent < 1 and 2 * box > parent
        assert child <= y1 and 3 * child < 2 * v0
        assert F("1.01") * child - F(".49") * (1 + box - parent) < -F(".1")

    rational = 3 * delta * b
    costs = {
        "raw slot sampling": b + tail + slack,
        "staged recognition": b + gate + slack,
        "top raw and rational": b + delta * top / 3 + 1 / rational + 2 * slack,
        "high raw and rational": b + delta * high / 3 + (1 + v1) / rational + 2 * slack,
        "low raw and rational": b + delta * low / 3 + 1 / rational + 2 * slack,
        "low algebraic tests": b + delta * low / 3 + 2 * slack,
        "character setup and evaluation": b + 2 * delta / 3,
        "sparse solve and exact comparison": 2 * b,
    }
    assert max(costs.values()) < ceiling

    print(f"width {float(theta):.3f}, conditional ceiling {float(ceiling):.4f}")
    for label, ratio, child in (("top", top, y1), ("high", high, y2)):
        base = b + delta * ratio / 3 + 2 * slack
        extra = ceiling - base
        elliptic_squared = curve**2 * child / y0
        assert extra > 0 and extra**2 > elliptic_squared
        print(f"{label} algebraic tests: {float(base) + float(elliptic_squared)**.5:.9f}")
    for name, cost in costs.items():
        print(f"{name}: {float(cost):.9f}")
    print(f"bottom mean margin: {float(bottom_mean):.9f}")
    print(f"total factor-count ratio: {float(factor_ratio):.9f} < 4")

    # Use one coordinate at the full sampled width with a four-k0 factor cap.
    for exponent in (12_000, 16_000):
        replay(
            2**exponent, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
            top_ratio=top, high_ratio=high, low_ratio=low, height=height, h=curve,
            target=ceiling, scales=scales, fractions=fractions, top_ratio_slope=top-1,
            factor_cap=4, first_scale=first_floor, cap_slack=slack, row_exponent=b,
            coordinate_fraction=theta,
        )


if __name__ == "__main__":
    here = Path(__file__).parent
    grid = run_path(str(here / "keybreak-public-quadratic-budget.py"))["grid"]
    replay = run_path(str(here / "keybreak-tiered-descent.py"))["check_integer_schedule"]
    for width, parameters in SCHEDULES.items():
        check(F(width), tuple(map(F, parameters.split())), grid, replay)
