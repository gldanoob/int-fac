"""Replay the two branch tests for a quartic with colliding linear marks."""
from fractions import Fraction
from math import gcd


def branches(a, b, x, y):
    constant = (b*b-a*a)**2*y*y + 2*(a*b*x)**2
    linear = 2*a*b*(a*a+b*b)*x*y
    return constant-linear, constant+linear


def split(n, a, b, x, y):
    """Return a factor only for a simple chart with opposite local signs."""
    if gcd(2*a*b*x*y*(b**4-a**4)*(x*x-4*y*y), n) != 1:
        return None
    minus, plus = branches(a, b, x, y)
    if minus*plus % n:
        return None
    factor = gcd(minus, n)
    if 1 < factor < n:
        return factor
    return None


def first_divisor(n, a, b, x, y):
    """Keep a divisor from the unit screen or either branch, including partial hits."""
    screen = gcd(2*a*b*x*y*(b**4-a**4)*(x*x-4*y*y), n)
    if screen != 1:
        return screen if screen < n else None
    for branch in branches(a, b, x, y):
        divisor = gcd(branch, n)
        if 1 < divisor < n:
            return divisor
    return None


def signed_counts(n):
    counts = [0, 0, 0]
    for s in range(n):
        if gcd(s*(s**4-1), n) != 1:
            continue
        for u in range(n):
            if gcd(u*(u*u-4), n) != 1:
                continue
            minus, plus = branches(s, 1, u, 1)
            if minus*plus % n:
                continue
            # Lift the shape and compare the actual quartic square root.
            shape = u + n
            scale = 2*shape*(shape**2-4)
            radicand = 4*shape**2*(shape**2-4)**3
            m = scale*pow(1-s*s, -1, n) % n
            z = m*s % n
            gamma = m*(m-scale) % n
            assert gamma == z*z % n and (gamma*gamma+radicand) % n == 0
            c = -pow(scale, -1, n)
            root = (2*m-scale)*pow(shape+c*gamma, -1, n) % n
            assert root*root % n == gamma
            assert gcd(root-z, n) == gcd(minus, n)
            counts[0] += minus % n == 0
            counts[1] += plus % n == 0
            counts[2] += split(n, s, 1, u, 1) is not None
    return counts


def local_count(p):
    squares = {u*u % p for u in range(1, p)}
    count = 0
    for s in range(p):
        if s*(s**4-1) % p == 0:
            continue
        disc = (-s**4 + 6*s*s-1) % p
        count += 1 if disc == 0 else 2 if disc in squares else 0
    return count


def full_search_count(p, q):
    def local_misses(p):
        clean = (p-1-gcd(4, p-1))*(p-3)
        one_sign = local_count(p)
        return p*p-clean, clean-2*one_sign, one_sign

    singular_p, miss_p, hits_p = local_misses(p)
    singular_q, miss_q, hits_q = local_misses(q)
    return (p*q)**2-singular_p*singular_q-miss_p*miss_q-2*hits_p*hits_q


def search(n, height, test=split):
    # Construct every parameter for this input, with no supplied field or root.
    slopes = sorted({Fraction(a, b) for b in range(1, height+1)
                     for a in range(1, b)})
    shapes = sorted({Fraction(x, y) for y in range(1, height+1)
                     for x in range(2*y+1, height+1)})
    attempts = 0
    for slope in slopes:
        for shape in shapes:
            attempts += 1
            factor = test(n, slope.numerator, slope.denominator,
                           shape.numerator, shape.denominator)
            if factor:
                return attempts, factor
    return attempts, None


if __name__ == "__main__":
    assert branches(1, 2, 4, 1) == (57, 217)
    assert split(4123, 1, 2, 4, 1) == 19
    for p, q in [(7, 11), (11, 13), (13, 17), (17, 19), (23, 29)]:
        one_sign = local_count(p)*local_count(q)
        assert signed_counts(p*q) == [one_sign, one_sign, 2*one_sign]
        n = p*q
        full_count = sum(first_divisor(n, s, 1, u, 1) is not None
                         for s in range(n) for u in range(n))
        assert full_count == full_search_count(p, q)
        print(f"N={n}: {2*one_sign} productive square pairs, "
              f"{full_count} gcd splits among {n*n}")
    attempts, factor = search(4123, 4)
    assert factor and 4123 % factor == 0
    print(f"N=4123: divisor {factor} in {attempts} candidate pairs at height 4")
    attempts, factor = search(1009*1013, 4)
    assert (attempts, factor) == (10, None)
    print(f"N={1009*1013}: divisor {factor} in {attempts} candidate pairs at height 4")
    for n in (4123, 1009*1013):
        print(f"N={n}: height-four search retaining all gcds: {search(n, 4, first_divisor)}")

    for n, omega in ((7, 1), (49, 1), (77, 2), (343*11, 2), (17*19, 2), (7*11*13, 3)):
        # Before scaling by D, the quadratic identity is determined by two coefficients.
        u = n+4
        d = u*u*(u*u-20)
        v = Fraction(-u*(u*u-20), 40)
        S = Fraction(1600, d)
        assert u*u-S*v*v == 20 and -2*u*v*S == 80
        verified = mixed = 0
        for residue in range(n):
            u = residue + 2*n
            d = u*u*(u*u-20)
            if gcd(d, n) != 1 or (25*d**4+1600*d**3) % n:
                continue
            denominator = (u-u*(u*u-20)*pow(8, -1, n)) % n
            root = 6*d*pow(denominator, -1, n) % n
            assert gcd(60*d**3, n) == 1 and (root*root-d*d) % n == 0
            divisor = gcd(root-d, n)
            assert divisor == gcd((u-2)*(u-4), n)
            if residue == 4:
                assert root == d % n
            verified += 1
            mixed += 1 < divisor < n
        assert (verified, mixed) == (4**omega, 4**omega-2**(omega+1))
        print(f"N={n}: class 5 has {verified} valid residues, {mixed} mixed signs")
