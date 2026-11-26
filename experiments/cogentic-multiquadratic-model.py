"""Construct and check a multiquadratic model from one odd composite input."""

from math import gcd, isqrt, prod

from sage.all import PolynomialRing, ZZ, next_prime, prime_range


def radical_model(n, rank):
    primes = []
    q = 2
    for _ in range(rank):
        q = int(next_prime(q))
        if n % q == 0:
            return q
        primes.append(q)

    modulus = prod(q*q for q in primes)
    k = n % modulus
    start = isqrt(k*n) + modulus
    roots = []
    radicands = []
    for q in primes:
        other = modulus // (q*q)
        residue = (n+q)*other*pow(other, -1, q*q) % modulus
        root = start + (residue-start) % modulus
        divisor = gcd(root, n)
        if 1 < divisor < n:
            return divisor
        if divisor == n:
            root += modulus
            assert gcd(root, n) == 1
        roots.append(root)
        radicands.append(root*root-k*n)
    return primes, roots, radicands


def monic_model(n, roots, radicands):
    rank = len(roots)
    degree = 2**rank
    candidates = (degree-1)*(rank-1)+1
    for p in prime_range(2, candidates+1):
        if n % p == 0:
            return int(p)

    for base in range(5, 5+candidates):
        values = [base**i*root for i, root in enumerate(roots)]
        subset_sums = [0]
        for value in values:
            subset_sums += [(x+value) % n for x in subset_sums]
        derivative = 1
        for value in subset_sums[1:]:
            derivative = derivative*(2*value) % n
        divisor = gcd(derivative, n)
        if divisor == n:
            continue
        if divisor != 1:
            return divisor

        ring = PolynomialRing(ZZ, "x")
        polynomial = ring.gen()
        radical_ring = PolynomialRing(ZZ, "w")
        w = radical_ring.gen()
        for i, radicand in enumerate(radicands):
            quadratic = radical_ring.quotient(w*w-radicand, "w")
            extension = PolynomialRing(quadratic, "x")
            x = extension.gen()
            shift = base**i * quadratic.gen()
            f = extension(polynomial)
            shifted = f(x-shift)*f(x+shift)
            coefficients = [c.lift() for c in shifted.list()]
            assert all(c.degree() <= 0 for c in coefficients)
            polynomial = ring([c[0] for c in coefficients])
        return base, polynomial, sum(values) % n, derivative

    raise AssertionError("the derivative root bound guarantees a unit or a factor")


def check(n, rank):
    model = radical_model(n, rank)
    if isinstance(model, int):
        assert 1 < model < n and n % model == 0
        return model
    primes, roots, radicands = model
    for i, (root, radicand) in enumerate(zip(roots, radicands)):
        assert radicand > 0 and (root*root-radicand) % n == 0 and gcd(root, n) == 1
        for j, q in enumerate(primes):
            if i == j:
                assert radicand % q == 0 and radicand % (q*q) != 0
            else:
                assert radicand % q != 0
    model = monic_model(n, roots, radicands)
    if isinstance(model, int):
        assert 1 < model < n and n % model == 0
        return model
    base, polynomial, root, derivative = model
    assert polynomial.degree() == 2**rank and polynomial.is_irreducible()
    assert polynomial(root) % n == 0 and polynomial.derivative()(root) % n == derivative
    assert gcd(derivative, n) == 1
    assert max(radicands)*64 <= min(radicands)*((base-1)*7)**2
    return polynomial.degree(), base


if __name__ == "__main__":
    for n, rank in [(77, 3), (10403, 4), (101**2*103, 4), (10007**2*10009, 5)]:
        print(n, rank, check(n, rank))
