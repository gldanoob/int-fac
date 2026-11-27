"""Certify the 2/3-width private and terminal cost infimum and a strict witness."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path

from sage.all import AA, PolynomialRing, QQ


def stationary_polynomial(theta):
    """Eliminate the stationary slope relation and then square the terminal equality."""
    z = PolynomialRing(QQ, "z").gen()
    gate = 4 * theta / 9 + 2 * z / 3
    derivative = QQ(2) / 3 - 8 * theta / (9 * z)
    # gate = u^2 p(u), cap = u^2 C, and z = u^3.
    cap = 2 * gate + z / (2 * derivative)
    poly = ((6 * gate * (cap - gate) - 3 * z**2 / 2)**2 - 16 * z**2 * cap).numerator()
    return poly * poly.denominator()


def check_limit():
    theta = QQ(2) / 3
    poly = stationary_polynomial(theta)
    z = poly.parent().gen()
    assert poly == (332150625*z**6 - 212576400*z**5 + 632375424*z**4 - 235892736*z**3
                    - 143327232*z**2 + 28311552*z + 4194304)
    assert stationary_polynomial(QQ(1)) == (
        455625*z**6 + 1181952*z**4 - 1092096*z**3 - 663552*z**2 + 294912*z + 65536)
    roots = [r for r in poly.roots(AA, multiplicities=False)
             if QQ(F(".26871505639057413116")) < r < QQ(F(".26871505639057413117"))]
    assert len(roots) == 1

    u = roots[0] ** (QQ(1) / 3)
    mass = 4 * theta / (9 * u**2)
    gate = mass + 2 * u / 3
    derivative = QQ(2) / 3 - 8 * theta / (9 * u**3)
    ceiling = 2 * gate + u / (2 * derivative)
    b = ceiling - gate
    assert QQ(F("2.07377842496623257501")) < ceiling < QQ(F("2.07377842496623257502"))
    assert 0 < 2 * b < ceiling and derivative < 0
    assert 6 * b * (ceiling - b) == 3 * u**2 / 2 + 4 * ceiling.sqrt()
    assert 6 * (ceiling - 2 * b) * derivative == -3 * u

    delta = 2 / ceiling.sqrt()
    kappa = 2 / (3 * u**2 * delta)
    beta = b / delta
    alpha = QQ(1) / 2
    radix = delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    height = radix * (1 + 2 * v0)
    assert 2 * beta > QQ(1) / 3
    low = (beta + 2 * height + radix / (3 * beta)) / (2 * beta - QQ(1) / 3)
    slope = low - height / beta
    assert (low - slope) * beta == height
    assert (2 * slope - 1) * beta == low / 3 + radix / (3 * beta)
    assert b + delta * low / 3 + 1 / (3 * delta * b) == ceiling

    top, high = QQ(F("1.70")), QQ(F("1.85"))
    y1 = v0 / top
    v1 = alpha * y1
    y2 = v1 / high
    assert low > high > top > QQ(3) / 2 and 0 < y0 < 1 and 2 * v0 < 1
    assert slope > 1 and (low - 1) * slope * beta > height and 3 * y1 < 2 * v0
    assert mass > u / 3 and gate < 2 * mass and 2 * theta * gate / mass < 4
    assert QQ(F("1.01")) * y1 - QQ(F(".49")) * (1 + v0 - y0) < -QQ(F(".1"))
    assert QQ(F(".49")) * (height + slope * beta) - QQ(F("1.01")) * radix > QQ(F(".04"))

    rational = 3 * delta * b
    for cost in (
        b + delta * top / 3 + 1 / rational,
        b + delta * high / 3 + (1 + v1) / rational,
        b + delta * top / 3 + u * (y1 / y0).sqrt(),
        b + delta * high / 3 + u * (y2 / y0).sqrt(),
        b + delta * low / 3,
        b + 2 * delta / 3,
        2 * b,
    ):
        assert cost < QQ(F("2.07")) < ceiling
    print("2.07377842496623257501 < 2/3-width ledger infimum < 2.07377842496623257502")
    print("Exact unsquared stationary equations and all other limiting cost checks passed.")


def check_strict_schedule():
    here = Path(__file__).parent
    grid = run_path(str(here / "keybreak-public-quadratic-budget.py"))["grid"]
    replay = run_path(str(here / "keybreak-tiered-descent.py"))["check_integer_schedule"]
    theta, delta, kappa, beta, alpha = map(F, ".666667 1.38882914 1.15274148 .67109617 .50000001".split())
    height, curve, factor_cost = map(F, ".53521291 .64530349 1.41421357".split())
    top, high, eta, slack, ceiling = map(F, "1.70 1.85 .00000001 .0000001 2.07387".split())
    b, radix = delta * beta, delta**-3
    y0 = 1 / (2 * kappa)
    v0 = alpha * y0
    y1 = v0 / top
    v1 = alpha * y1
    y2 = v1 / high
    low = (beta + 2 * height + radix / (3 * beta) + 4 * eta) / (2 * beta - F(1, 3))
    slope = low - (height + eta) / beta
    actual_height = radix * (1 + 2 * v0)

    assert F(2, 3) < theta < 1 and 2 * beta > F(1, 3)
    assert actual_height < height and 0 < 2 * v0 < 1 and 2 * alpha > 1
    assert factor_cost**2 > 2 and curve**2 > factor_cost**2 * 2 * y0 / (3 * delta)
    assert low > high > top > F(3, 2) and 0 < y0 < 1 and 3 * y1 < 2 * v0
    assert slope > 1 and (low - 1) * slope * beta > height
    assert (low - slope) * beta - height == eta
    assert (2 * slope - 1) * beta - low / 3 - radix / (3 * beta) == 2 * eta
    assert F(".49") * (actual_height + slope * beta) - F("1.01") * radix > F(".04")

    moment = 2 * theta * kappa * delta / 3
    scales, fractions, tail, gate = grid(moment, curve, F(".002"), 4096)
    assert 2 * theta * tail / moment < 4
    for scale in scales:
        parent, box = scale * y0, scale * v0
        child = box / (1 + (top - 1) * scale)
        assert 0 < child < box < parent < 1 and 2 * box > parent
        assert child <= y1 and 3 * child < 2 * v0
        assert F("1.01") * child - F(".49") * (1 + box - parent) < -F(".1")

    rational = 3 * delta * b
    for cost in (
        b + tail + slack, b + gate + slack,
        b + delta * top / 3 + 1 / rational + 2 * slack,
        b + delta * high / 3 + (1 + v1) / rational + 2 * slack,
        b + delta * low / 3 + 1 / rational + 2 * slack,
        b + delta * low / 3 + 2 * slack,
        b + 2 * delta / 3, 2 * b,
    ):
        assert cost < ceiling
    for ratio, child in ((top, y1), (high, y2)):
        extra = ceiling - (b + delta * ratio / 3 + 2 * slack)
        assert extra > 0 and extra**2 > curve**2 * child / y0

    for exponent in (16_000, 20_000):
        replay(
            2**exponent, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=slope-alpha,
            top_ratio=top, high_ratio=high, low_ratio=low, height=height, h=curve,
            target=ceiling, scales=scales, fractions=fractions, top_ratio_slope=top-1,
            factor_cap=4, first_scale=F(".0000039"), cap_slack=slack, row_exponent=b,
            coordinate_fraction=theta,
        )
    print(f"conditional width {float(theta):.6f}, ceiling {float(ceiling):.5f}")
    print(f"recognition {float(b + gate + slack):.12f}, terminal raw "
          f"{float(b + delta * low / 3 + 1 / rational + 2 * slack):.12f}")


if __name__ == "__main__":
    check_limit()
    check_strict_schedule()
