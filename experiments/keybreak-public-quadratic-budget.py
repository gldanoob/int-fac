"""Check the conditional one-coordinate public-row KeyBreak budget."""

from fractions import Fraction as F
from pathlib import Path
from runpy import run_path

from sage.all import AA, PolynomialRing, QQ


def stationary_limit():
    ring = PolynomialRing(QQ, "z")
    z = ring.gen()
    polynomial = (455625*z**6 - 437400*z**5 + 680400*z**4
                  - 136512*z**3 - 82944*z**2 + 9216*z + 1024)
    roots = [root for root in polynomial.roots(AA, multiplicities=False)
             if QQ(172)/1000 < root < QQ(173)/1000]
    assert len(roots) == 1
    u = roots[0] ** (QQ(1)/3)
    public = 2/(9*u*u) + 2*u/3
    private = 4/(9*u*u) + 2*u/3
    derivative = QQ(2)/3 - 4/(9*u**3)
    ceiling = (225*u**6-48*u**3-32)/(36*u*u*(3*u**3-2))
    assert QQ(203288100822533195)/10**17 < ceiling < QQ(203288100822533196)/10**17
    b = ceiling-public
    assert ceiling > 2*b > 0
    assert 6*b*public == 3*u*u/2 + 4*ceiling.sqrt()
    assert 6*(ceiling-2*b)*derivative == -3*u
    assert private + QQ(1)/5 < ceiling
    assert 2/(9*u*u) > 2*u/3
    assert (QQ(64)/9)**(QQ(1)/3) < ceiling < QQ(215463)/100000
    cap = AA(QQ(2034)/1000)
    assert cap**2 - 8*cap.sqrt()/3 < QQ(36)/100
    delta = 2 / ceiling.sqrt()
    beta = b / delta
    radix = delta**-3
    y0 = 3 * u**2 * delta / 4
    v0 = y0 / 2
    height = radix * (1 + 2*v0)
    low = (beta + 2*height + radix/(3*beta)) / (2*beta - QQ(1)/3)
    slope = low - height/beta
    top, high = QQ(163)/100, QQ(172)/100
    y1, y2 = v0/top, v0/(2*top*high)
    assert 2*beta > QQ(1)/3 and low > high > top > QQ(3)/2
    assert 0 < 2*v0 < 1 and 3*y1 < 2*v0 and slope > 1
    assert (low-1)*slope*beta > height
    assert (2*slope-1)*beta == low/3 + radix/(3*beta)
    assert b + delta*low/3 + 1/(3*delta*b) == ceiling
    assert 101*y1 - 49*(1 + v0 - y0) < -10
    assert 49*(height+slope*beta) - 101*radix > 4
    mass = 2/(9*u**2)
    assert mass > u/3 and public/mass < 2
    for cost in (b + delta*top/3 + 1/(3*delta*b),
                 b + delta*high/3 + (1+y1/2)/(3*delta*b),
                 b + delta*top/3 + u*(y1/y0).sqrt(),
                 b + delta*high/3 + u*(y2/y0).sqrt(),
                 b + delta*low/3, b + 2*delta/3, 2*b):
        assert cost < ceiling
    print("2.03288100822533195 < relaxed budget < 2.03288100822533196")


def grid(moment, curve, first, count):
    knots = [first + (1-first)*i/(count-1) for i in range(count)]
    return grid_from_knots(moment, curve, knots)


def grid_from_knots(moment, curve, knots):
    scales = [z*z for z in knots]
    weights = [curve*(right-left) for left, right in zip(knots, knots[1:])]
    weights.append(moment-sum(a*w for a, w in zip(scales, weights)))
    fractions = [a*w/moment for a, w in zip(scales, weights)]
    assert min(weights) > 0
    assert sum(fractions) == 1 and sum(weights) < 2*moment
    tail = F(0)
    gates = []
    for z, weight in zip(reversed(knots), reversed(weights)):
        tail += weight
        gates.append(tail+curve*z)
    assert max(gates) == min(gates)
    return scales, fractions, tail, gates[0]


def finite_schedule():
    delta, kappa, beta, alpha, gamma = map(F, "1.40273 1.536 .67286 .50001 .576970".split())
    height, top, high, low = map(F, ".480269 1.63 1.72 1.790783".split())
    curve, allowance, cap, ceiling = map(F, ".55626 1.414214 .000005 2.034".split())
    b, radix = delta*beta, delta**-3
    y0 = 1/(2*kappa)
    y1 = alpha*y0/top
    y2 = alpha*y1/high
    slope = alpha+gamma
    gaussian = (1+2*alpha*y0)*radix
    assert gaussian < height and 2*alpha > 1
    assert 0 < 2*alpha*y0 < 1 and y0 < 1 and 3*y1 < 2*alpha*y0
    assert low > high > top > F(3, 2) and slope > 1
    assert (low-slope)*beta > height and (low-1)*slope*beta > height
    mean = (2*slope-1)*beta-low/3-radix/(3*beta)
    assert mean > F(".000039")
    assert F(".49")*(gaussian+slope*beta)-F("1.01")*radix > F(".04")
    assert F("1.01")*y1-F(".49") < -F(".1")
    assert allowance**2 > 2 and curve**2 > allowance**2*2*y0/(3*delta)

    moment = kappa*delta/3
    public = grid(moment, curve, F(".021"), 1024)
    private = grid(2*moment, curve, F(".026"), 512)
    for scales in (public[0], private[0]):
        for a in scales:
            parent, box = a*y0, a*alpha*y0
            child = box/(1+(top-1)*a)
            assert 0 < child < box < parent < 1
            assert child <= y1 and 3*child < 2*alpha*y0 and 2*box > parent
            assert F("1.01")*child-F(".49")*(1+box-parent) < -F(".1")

    residual = F(".20")
    rational = 3*delta*b
    charges = {
        "public screening": b+public[3]+cap,
        "private screening": residual+private[3]+cap,
        "public top raw": b+delta*top/3+1/rational+2*cap,
        "public high raw": b+delta*high/3+(1+alpha*y1)/rational+2*cap,
        "public low raw": b+delta*low/3+1/rational+2*cap,
        "setup and character checks": b+2*delta/3,
        "sparse solve and exact extraction": 2*b,
    }
    assert max(charges.values()) < ceiling
    for ratio, child, upper in ((top, y1, F("2.014088")), (high, y2, F("1.914194"))):
        assert upper < ceiling
        remaining = upper-b-delta*ratio/3-2*cap
        assert remaining > 0 and remaining**2 > curve**2*child/y0

    replay = run_path(str(Path(__file__).with_name("keybreak-tiered-descent.py")))["check_integer_schedule"]
    for (scales, fractions, _, _), rows, first_floor in (
        (public, b, F(".00044")), (private, residual, F(".00067")),
    ):
        replay(
            2**16000, delta=delta, kappa=kappa, beta=beta, alpha=alpha, gamma=gamma,
            top_ratio=top, high_ratio=high, low_ratio=low, height=height,
            h=curve, target=ceiling, scales=scales, fractions=fractions,
            top_ratio_slope=top-1, first_scale=first_floor,
            cap_slack=cap, row_exponent=rows,
        )

    for label, cost in charges.items():
        print(f"{label}: {float(cost):.9f}")
    print(f"public root window exponent: {float(b+public[2]+cap):.9f}")


if __name__ == "__main__":
    stationary_limit()
    finite_schedule()
