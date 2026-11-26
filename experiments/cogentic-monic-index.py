"""Replay the common-root repair and the exact denominator-clearing examples."""

import os
import runpy
import subprocess
from math import gcd
from pathlib import Path


def derivative_at(coefficients, argument):
    return sum(i * c * argument ** (i - 1) for i, c in enumerate(coefficients) if i)


def repair(n, m, f, g):
    derivatives = [derivative_at(p, m) for p in (f, g)]
    for t in range(3):
        gcds = tuple(gcd(d + 4 * t, n) for d in derivatives)
        for divisor in gcds:
            if 1 < divisor < n:
                return divisor
        if gcds == (1, 1):
            return t, tuple((p[0] - 4 * t * m, p[1] + 4 * t, *p[2:]) for p in (f, g))
    raise AssertionError((n, m, derivatives))


def run():
    constructor = runpy.run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))
    monic_pair, scheduled_degree = constructor["monic_pair"], constructor["scheduled_degree"]
    inputs = (*range(9, 8192, 2), (1 << 127) + 1, (1 << 255) - 19, (1 << 1023) + 1)
    outcomes = {}
    for n in inputs:
        m, f, g = monic_pair(n, scheduled_degree(n))
        result = outcomes[n] = repair(n, m, f, g)
        if isinstance(result, int):
            assert 1 < result < n and n % result == 0
            continue
        t, (left, right) = result
        assert 0 <= t <= 2 and right == left[:-1] + (1 - m, 1)
        for before, after in ((f, left), (g, right)):
            assert len(after) == len(before) and after[-1] == 1 and after[0] % 4 == 2
            assert all(c % 2 == 0 for c in after[:-1])
            assert max(map(abs, after)) <= 10 * m
            assert sum(c * m**i for i, c in enumerate(after)) == n
            assert gcd(derivative_at(after, m), n) == 1

    assert monic_pair(2385, scheduled_degree(2385))[:2] == (47, (82, 2, 1))
    assert gcd(9, 2385) == 9 and (47 + 1) % 9 != 0 and outcomes[2385] == 3
    assert outcomes[145][0] == 1
    assert monic_pair(895, scheduled_degree(895))[0::2] == (29, (54, 0, -28, 1))
    assert outcomes[895][0] == 0
    assert monic_pair(11, scheduled_degree(11))[0::2] == (3, (2, 0, -2, 1))
    assert outcomes[11][0] == 0

    script = """
check(ok) = if(!ok, error("denominator-clearing replay failed"));
replay() = {
  my(P=x^3-28*x^2+54, N=895, m=29, D=deriv(P), beta=Mod((x^2-x+3)/15,P));
  check(poldisc(P)==4662900 && poldisc(P)==15^2*nfdisc(P));
  check(gcd(15,N)==5 && subst(D,x,m)==899 && gcd(899,N)==1);
  check(charpoly(beta,y)==y^3-51*y^2+33*y-5);
  my(C=lift(D*beta));
  check(denominator(C,1)==1 && C==51*x^2-22*x-90);
  check(lift(Mod(subst(C,x,m),N)/subst(D,x,m))==472);
  P=x^3-2*x^2+2;
  check(poldisc(P)==-44 && gcd(poldisc(P),11)==11 && gcd(subst(deriv(P),x,3),11)==1);
};
iferr(replay(), err, print(err); quit(1));
"""
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input=script,
                            text=True, capture_output=True, timeout=15, check=True)
    assert not result.stderr, result.stderr
    print(f"Verified common-root repair on {len(inputs)} inputs and four exact fixtures")


if __name__ == "__main__":
    run()
