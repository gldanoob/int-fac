"""Certify a strict half-width one-coordinate cost schedule below 2.033."""

from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from runpy import run_path


def rounded_optimal_knots(count):
    # The stationary equation determines the next knot up to a common scale.
    points = [0, 10**15]
    while len(points) <= count:
        left, right = points[-2:]
        points.append(right + (right**2 - left**2) // (2 * right))
    assert len(points) == count + 1 and all(a < b for a, b in zip(points, points[1:]))
    return [F(point, points[-1]) for point in points[1:]]


def root_upper(value):
    scale = 10**12
    return F(isqrt(value.numerator * scale**2 // value.denominator) + 1, scale)


def exclude_shorter_grid():
    # Outward round the best possible 352-interval left sum using the exact recurrence.
    scale = 10**20
    upper = F(0)
    for _ in range(1, 352):
        next_upper = 4 / (27 * (1 - upper)**2)
        upper = F(-(-next_upper.numerator * scale // next_upper.denominator), scale)
    ceiling, u = F("2.033"), F(".55648169")
    linear = 1 - upper
    p = 2 / (9*u**2) + linear*u
    b = ceiling - p
    assert 0 < 2*b < ceiling
    slope = -6*(ceiling - 2*b)*(linear - 4/(9*u**3)) - 3*u
    # Tangents to the concave terminal and convex screening costs, with the
    # exact quadratic remainder from -(3/2)u². Round sqrt(C) downward.
    root_lower = root_upper(ceiling) - F(1, 10**12)
    surplus = 6*b*(ceiling-b) - 3*u**2/2 - 4*root_lower + slope**2/6
    assert surplus < F("-.00000043")
    print(f"352-stage upper bound on terminal surplus at 2.033: {float(surplus):.12f}")


def check_schedule(count, delta, kappa, beta, ceiling):
    here = Path(__file__).parent
    grid = run_path(str(here / "keybreak-public-quadratic-budget.py"))["grid_from_knots"]
    replay = run_path(str(here / "keybreak-tiered-descent.py"))["check_integer_schedule"]
    delta, kappa, beta, ceiling = map(F, (delta, kappa, beta, ceiling))
    theta, alpha = F(1, 2), F(".500000000001")
    top, high, eta, slack = map(F, "1.63 1.72 .00000000001 .00000000001".split())
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top
    v1 = alpha * y1
    y2 = v1 / high
    actual_height = radix * (1 + 2 * v0)
    height = actual_height + eta
    factor_cost = root_upper(F(2))
    curve = root_upper(factor_cost**2 * 2*y0 / (3*delta))
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
    scales, fractions, tail, gate = grid(moment, curve, rounded_optimal_knots(count))
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
        factor_cap=2, first_scale=scales[0]*F(".98"), cap_slack=slack, row_exponent=b,
        coordinate_fraction=theta,
    )
    for label, cost in charges.items():
        print(f"{label}: {float(cost):.12f}")
    print(f"{count}-stage strict half-width ceiling: {float(ceiling):.8f}")


if __name__ == "__main__":
    run_path(str(Path(__file__).with_name("keybreak-public-quadratic-budget.py")))["stationary_limit"]()
    exclude_shorter_grid()
    check_schedule(353, "1.402688813", "1.534781893", ".6727839471", "2.033")
    check_schedule(4096, "1.402726234", "1.535900278", ".6728571597", "2.03289126")
