"""Certify a strict half-width one-coordinate cost schedule below 2.033."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path


def check_schedule():
    here = Path(__file__).parent
    half_width = run_path(str(here / "keybreak-public-quadratic-budget.py"))
    half_width["stationary_limit"]()
    grid = half_width["grid"]
    replay = run_path(str(here / "keybreak-tiered-descent.py"))["check_integer_schedule"]

    theta, delta, kappa, beta, alpha = map(F, ".5 1.40272978 1.53600607 .672864055 .50000001".split())
    height, curve, factor_cost = map(F, ".48024639 .55625114 1.41421357".split())
    top, high, eta, slack, ceiling = map(F, "1.63 1.72 .00000001 .0000001 2.03297".split())
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top
    v1 = alpha * y1
    y2 = v1 / high
    actual_height = radix * (1 + 2 * v0)
    low = (beta + 2 * height + radix / (3 * beta) + 4 * eta) / (2 * beta - F(1, 3))
    slope = low - (height + eta) / beta

    assert 2 * beta > F(1, 3)
    assert actual_height < height and 0 < y0 < 1 and 0 < 2 * v0 < 1
    assert 2 * alpha > 1 and 3 * y1 < 2 * v0
    assert low > high > top > F(3, 2) and slope > 1
    assert (low - 1) * slope * beta > height
    assert (low - slope) * beta - height == eta
    assert (2 * slope - 1) * beta - low / 3 - radix / (3 * beta) == 2 * eta
    assert F(".49") * (actual_height + slope * beta) - F("1.01") * radix > F(".04")
    assert factor_cost**2 > 2 and curve**2 > factor_cost**2 * 2 * y0 / (3 * delta)

    moment = 2 * theta * kappa * delta / 3
    scales, fractions, tail, gate = grid(moment, curve, F(".002"), 4096)
    assert 2 * theta * tail / moment < 2
    for scale in scales:
        parent, box = scale * y0, scale * v0
        child = box / (1 + (top - 1) * scale)
        assert 0 < child < box < parent < 1 and 2 * box > parent
        assert child <= y1 and 3 * child < 2 * v0
        assert F("1.01") * child - F(".49") * (1 + box - parent) < -F(".1")

    rational = 3 * delta * b
    charges = {
        "raw root slots": b + tail + slack,
        "staged screening": b + gate + slack,
        "top raw": b + delta * top / 3 + 1 / rational + 2 * slack,
        "high raw": b + delta * high / 3 + (1 + v1) / rational + 2 * slack,
        "low raw": b + delta * low / 3 + 1 / rational + 2 * slack,
        "low algebraic": b + delta * low / 3 + 2 * slack,
        "character setup and tests": b + 2 * delta / 3,
        "sparse solve and exact extraction": 2 * b,
    }
    assert max(charges.values()) < ceiling
    for ratio, child in ((top, y1), (high, y2)):
        room = ceiling - (b + delta * ratio / 3 + 2 * slack)
        assert room > 0 and room**2 > curve**2 * child / y0

    replay(
        2**20_000, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=slope-alpha,
        top_ratio=top, high_ratio=high, low_ratio=low, height=height, h=curve,
        target=ceiling, scales=scales, fractions=fractions, top_ratio_slope=top-1,
        factor_cap=2, first_scale=F(".0000039"), cap_slack=slack, row_exponent=b,
        coordinate_fraction=theta,
    )
    for label, cost in charges.items():
        print(f"{label}: {float(cost):.12f}")
    print(f"strict half-width ceiling: {float(ceiling):.5f}")


if __name__ == "__main__":
    check_schedule()
