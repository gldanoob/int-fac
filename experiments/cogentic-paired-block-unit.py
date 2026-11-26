#!/usr/bin/env python3
"""Construct an irreducible polynomial and an explicit unit above an input modulus."""

import argparse
from math import gcd, lcm, prod

from sage.all import NumberField, PolynomialRing, ZZ, prime_range


def construct(n, ell, min_order=0):
    if n < 3 or not ZZ(ell).is_prime() or ell < 5 or min_order < 0:
        raise ValueError("require N >= 3, an odd prime >= 5, and a nonnegative order cutoff")
    h = (ell-1)//2
    step = lcm(*range(1, h+1))*prod(prime_range(h+1))
    offset = int(step * (h * pow(int(step), -1, ell) % ell))
    marks = (*range(1, h+1), *range(offset+1, offset+h+1))
    misses = 2*h + h*min_order*(min_order+1)//2
    for p in prime_range(min(n-1, max(ell, misses))+1):
        if n % p == 0:
            return int(p), None
    if n <= max(ell, misses):
        raise ValueError("the prime input is below the construction cutoff")

    ring = PolynomialRing(ZZ, "x")
    x = ring.gen()
    left = prod(x-i for i in marks[:h])
    right = prod(x-i for i in marks[h:])
    w = left*right
    derivative = w.derivative()
    base_g = x**(2*h-1)
    if int((w*base_g-derivative)(0)) % (ell*ell) == 0:
        base_g += ell
    start = max(offset+h+1, 1 << ((n.bit_length()+2*h-2)//(2*h-1)))
    for m in range(start, start+misses+1):
        divisors = [gcd(n, m-a) for a in marks]
        proper = next((g for g in divisors if 1 < g < n), None)
        if proper is not None:
            return proper, None
        if n in divisors:
            continue
        target = int(left(m))*pow(int(right(m)), -1, n) % n
        power = 1
        for _ in range(min_order):
            power = power*target % n
            divisor = gcd(n, power-1)
            if 1 < divisor < n:
                return divisor, None
            if divisor == n:
                break
        else:
            correction = int(derivative(m)-w(m)*base_g(m))
            correction = correction*pow(int(ell*ell*w(m)), -1, n) % n
            digits = ZZ(correction).digits(m)
            assert len(digits) <= 2*h-1
            f = w*(base_g + ell*ell*ring(digits))-derivative
            assert f.degree() == 4*h-1 and f(m) % n == 0
            return None, (f, left, right, m, target)
    raise AssertionError("the finite-field root bound must leave a chart or a proper gcd")


def replay():
    for n, ell, order in ((251*257, 7, 0), (1009*5003, 5, 5)):
        divisor, chart = construct(n, ell, order)
        assert divisor is None
        f, left, right, m, target = chart
        h = (ell-1)//2
        assert f.is_irreducible() and f.is_monic()
        assert all(c % ell == 0 for c in f.list()[:-1]) and f[0] % (ell*ell) != 0
        field = NumberField(f, "t")
        theta = field.gen()
        unit = left(theta)/right(theta)
        assert unit.is_integral() and (1/unit).is_integral()
        assert unit.norm() == (-1)**h and unit != 1 and unit != -1
        assert int(left(m)-target*right(m)) % n == 0
        for k in range(1, order+1):
            assert gcd(n, pow(target, k, n)-1) == 1
        print(f"N={n}, degree={f.degree()}, m={m}, unit residue={target}, norm={unit.norm()}")
    assert construct(35, 5) == (5, None)
    # The unit is 1 at only one prime on this input, above the trial cutoff.
    assert construct(33109, 5, 5) == (113, None)
    print("A unit-order gcd splits 33109 = 113 * 293 above the trial cutoff.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int)
    parser.add_argument("--prime", type=int, default=7, help="auxiliary prime 2h+1")
    parser.add_argument("--min-order", type=int, default=0, help="exclude local unit orders at most this bound")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        try:
            factor, chart = construct(args.N, args.prime, args.min_order)
        except ValueError as error:
            parser.error(str(error))
        if factor is not None:
            print(f"{args.N} = {factor} * {args.N // factor}")
        else:
            f, left, right, m, target = chart
            print(f"F(x) = {f}\nU = ({left})/({right})\nx = {m} modulo {args.N}, U = {target} modulo {args.N}")
