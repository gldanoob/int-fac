"""Exact cost and rounded checks for the N^(97/100) square window."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path


def check():
    here = Path(__file__).parent
    grid = run_path(str(here / "keybreak-public-quadratic-budget.py"))["grid"]
    replay = run_path(str(here / "keybreak-tiered-descent.py"))["check_integer_schedule"]
    delta, kappa, beta, alpha, gamma = map(F, "1.3647853 .815683 .6680135 .500005 .677805".split())
    top, high, low, height = map(F, "1.78 1.97 2.127694 .634514".split())
    curve, factor_cost, slack, ceiling = map(F, ".773864 1.414215 .000005 2.148".split())
    theta = F(".97")
    b = delta * beta
    radix = delta**-3
    y0 = 1/(2*kappa)
    y1 = alpha*y0/top
    y2 = alpha*y1/high
    slope = alpha + gamma
    actual_height = radix*(1+2*alpha*y0)
    assert factor_cost**2 > 2 and curve**2 > factor_cost**2 * 2*y0/(3*delta)
    assert actual_height < height and 2*alpha > 1 and 2*alpha*y0 < 1
    assert 3*y1 < 2*alpha*y0 and low > high > top > F(3, 2)
    assert slope > 1 and (low-slope)*beta > height and (low-1)*slope*beta > height
    assert (2*slope-1)*beta - low/3 - radix/(3*beta) > F(".00004")
    assert F(".49")*(actual_height+slope*beta) - F("1.01")*radix > F(".04")
    moment = theta * 2*kappa*delta/3
    scales, fractions, tail, gate = grid(moment, curve, F(".026"), 1536)
    factor_ratio = (2*theta) * tail / moment
    assert factor_ratio < 4
    for scale in scales:
        parent, box = scale*y0, scale*alpha*y0
        child = box/(1+(top-1)*scale)
        assert 0 < child < box < parent < 1 and 2*box > parent
        assert child <= y1 and 3*child < 2*alpha*y0
        assert F("1.01")*child - F(".49")*(1+box-parent) < -F(".1")
    denom = 3*delta*b
    costs = {
        "raw slot sampling": b+tail+slack,
        "staged recognition": b+gate+slack,
        "top raw and rational": b+delta*top/3+1/denom+2*slack,
        "high raw and rational": b+delta*high/3+(1+alpha*y1)/denom+2*slack,
        "low raw and rational": b+delta*low/3+1/denom+2*slack,
        "character setup and evaluation": b+2*delta/3,
        "sparse solve and exact comparison": 2*b,
    }
    assert max(costs.values()) < ceiling
    for label, ratio, child in (("top",top,y1), ("high",high,y2)):
        extra = ceiling-b-delta*ratio/3-2*slack
        assert extra > 0 and extra**2 > curve**2*child/y0
        print(f"{label} algebraic tests: {float(b+delta*ratio/3+2*slack) + float(curve**2*child/y0)**.5:.9f}")
    for exponent in (12_000, 16_000):
        replay(
            2**exponent, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
            top_ratio=top, high_ratio=high, low_ratio=low, height=height, h=curve,
            target=ceiling, scales=scales, fractions=fractions, top_ratio_slope=top-1,
            factor_cap=2, first_scale=F(".00067"), cap_slack=slack, row_exponent=b,
            coordinate_fraction=theta/2,
        )
    for name, cost in costs.items():
        print(f"{name}: {float(cost):.9f}")
    print(f"total factor-count ratio: {float(factor_ratio):.9f} < 4")


if __name__ == "__main__":
    check()
