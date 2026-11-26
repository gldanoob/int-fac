"""Certify the limiting private and terminal budget with exact real algebraic numbers."""

from fractions import Fraction

from sage.all import AA, PolynomialRing, QQ


def check_limit():
    t = PolynomialRing(QQ, "t").gen()
    polynomial = 455625*t**6 + 1181952*t**4 - 1092096*t**3 - 663552*t**2 + 294912*t + 65536
    roots = [r for r in polynomial.roots(AA, multiplicities=False) if QQ(Fraction(".483")) < r < QQ(Fraction(".484"))]
    assert len(roots) == 1
    u = roots[0] ** (QQ(1)/3)
    mass = 4/(9*u**2)
    private = mass + 2*u/3
    slope = QQ(2)/3 - 8/(9*u**3)
    ceiling = 2*private + u/(2*slope)
    b = ceiling - private
    sqrt_ceiling = ceiling.sqrt()
    assert QQ(Fraction("2.15463021529917670")) < ceiling < QQ(Fraction("2.15463021529917672"))
    assert b > 0 and ceiling > 2*b
    assert 6*b*(ceiling-b) == 3*u**2/2 + 4*sqrt_ceiling
    assert 6*(ceiling-2*b)*slope == -3*u

    delta = 2/sqrt_ceiling
    kappa = 2/(3*u**2*delta)
    beta = b/delta
    alpha = QQ(1)/2
    radix = delta**-3
    y0 = 1/(2*kappa)
    height = radix*(1+2*alpha*y0)
    assert 2*beta > QQ(1)/3
    low = (beta+2*height+radix/(3*beta))/(2*beta-QQ(1)/3)
    box_slope = low-height/beta
    assert low*beta == height+box_slope*beta
    assert low/3+radix/(3*beta) == (2*box_slope-1)*beta
    assert b+delta*low/3+1/(3*delta*b) == ceiling

    top, high = QQ(Fraction("1.78")), QQ(Fraction("1.97"))
    y1 = alpha*y0/top
    assert low > high > top > QQ(3)/2 and y0 < 1 and 2*alpha*y0 < 1
    assert box_slope > 1 and (low-1)*box_slope*beta > height
    assert 3*y1 < 2*alpha*y0 and mass > u/3 and private/mass < 2
    assert QQ(Fraction("1.01"))*y1-QQ(Fraction(".49"))*(1+alpha*y0-y0) < -QQ(Fraction(".1"))
    assert QQ(Fraction(".49"))*(height+box_slope*beta)-QQ(Fraction("1.01"))*radix > QQ(Fraction(".04"))
    for work in (
        b+delta*top/3+1/(3*delta*b),
        b+delta*high/3+(1+alpha*y1)/(3*delta*b),
        b+delta*top/3+u*(alpha/top).sqrt(),
        b+delta*high/3+u*alpha/(top*high).sqrt(),
        b+2*delta/3, 2*b,
    ):
        assert work < QQ(Fraction("2.14"))
    print("2.15463021529917670 < limiting coefficient < 2.15463021529917672")
    print("Exact stationary equations, terminal equalities, and slack in other leading rows verified.")


if __name__ == "__main__":
    check_limit()
