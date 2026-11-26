"""Check private odd norm valuations on an explicit centered quadratic grid."""

from math import gcd, isqrt
from pathlib import Path
from runpy import run_path

GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))


def main():
    p, q = 2**127-1, 226854911280625642308916404954512141027
    assert p < q < 2*p and GRID["gp"](f"print(isprime({p}) && isprime({q}));\n") == ["1"]
    n, height = p*q, 20
    primes = tuple(GRID["primes_through"](2*height**2))

    def has_private_prime(value):
        value = abs(value)
        if not value:
            return False
        for prime in primes:
            while value % prime == 0:
                value //= prime
        return isqrt(value)**2 != value

    points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
              if gcd(a, b) == 1]
    fields = 0
    for j in range(-2, 3):
        m = isqrt(n)+j
        assert all(gcd(a-b*m, n) == 1 for a, b in points)
        for s in range(-3, 4):
            constant = n-m*m-s*m
            assert gcd(2*m+s, n) == 1 and has_private_prime(s*s-4*constant)
            assert all(has_private_prime(a*a+s*a*b+constant*b*b) for a, b in points)
            fields += 1
    assert fields*len(points) == 17885
    print(f"{n.bit_length()} bits, {fields} centered fields and {fields*len(points)} private mark checks")


if __name__ == "__main__":
    main()
