"""Check private odd norm valuations on a prescribed height-40 raw monic grid."""

from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


def main():
    here = Path(__file__).resolve().parent
    degree, height = 5, 40
    slopes = [(a,b) for a in range(-height,height+1) for b in range(1,height+1)
              if a and gcd(a,b) == 1]
    shifts = range(-4, 5)
    def side(s, m, a, b):
        if s == 0:
            return a**degree*(a+(1-m)*b) + 2*b**(degree+1)
        return a**degree + 2*b**degree + 4*s*(a-m*b)*b**(degree-1)

    def admissible(z):
        if (z-1) % degree == 0 or any(z % d == 0 for d in range(2, isqrt(z)+1)):
            return False
        root = pow(-2, pow(degree, -1, z-1), z)
        return (all((a-b*root) % z for a,b in slopes)
                and all(side(s, root, a, b) % z for s in shifts for a,b in slopes)
                and all(side(s, root, 0, 1) % z for s in shifts)
                and all((degree*root**(degree-1) + 4*s - j) % z for s in shifts for j in (0,2)))
    choices = (z for z in range(65537, 70000, 2) if admissible(z))
    p, q = next(choices), next(choices)
    step = 2 * p**2 * q**2
    base = 1
    mod = 2
    for z in (p, q):
        root = pow(-2, pow(degree, -1, z-1), z)
        if (root**degree + 2) % z**2 == 0:
            root += z
        base += mod * ((root - base) * pow(mod, -1, z**2) % z**2)
        mod *= z**2
    assert mod == step
    top = 1 << 275
    low = top - top//(4*degree)
    first = low + (base-low) % step
    primes = tuple(run_path(str(here/"cogentic-monic-large-primes.py"))["primes_through"](2*height**2))
    degree_schedule = run_path(str(here/"cogentic-monic-pair.py"))["scheduled_degree"]
    # The prescribed tests select on small factors and unit reductions only.
    m = next(m for m in range(first, first+1000*step, step)
             if all((pow(m,degree,l)+2) % l for l in primes)
             and all(gcd(a-b*m,m**degree+2) == 1 for a,b in slopes)
             and all(gcd(degree*m**(degree-1)+4*s-j,m**degree+2) == 1
                     for s in shifts for j in (0,2)))
    n = m**degree + 2
    assert degree_schedule(n) == degree and n % p == n % q == 0 and n % p**2 and n % q**2
    assert gcd(degree*m**(degree-1),n) == gcd(m**(degree-1)*(degree+m),n) == 1
    nonzero = 0
    for s in shifts:
        for a, b in (slopes if s == 0 else [(0,1), *slopes]):
            assert gcd(a-b*m,n) == 1
            norm = abs(side(s, m, a, b))
            for l in primes:
                while norm % l == 0:
                    norm //= l
            assert isqrt(norm)**2 != norm
            nonzero += 1
    print(f"{n.bit_length()}-bit scheduled input, height {height}, {len(slopes)} nonzero slopes, "
          f"{nonzero} private valuation checks over {len(shifts)} shifts; cutoff {2*height**2}; "
          f"prescribed divisors {p} and {q}")


if __name__ == "__main__":
    main()
