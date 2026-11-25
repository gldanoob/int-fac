"""Check dyadic centered-floor parities against mixed roots and literal floor sums."""

from math import gcd, isqrt


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def outer(a, n):
    return int(4 * min(a % n, -a % n) < n)


def mixed_root(p, q):
    return (2 * q * pow(q, -1, p) - 1) % (p * q)


def centered_floor_bit(n, c):
    a = c * c * n
    denominator = a * n + 1
    center = c * n * c
    radius = n // 4
    value = sum(a * t * t // denominator for t in range(center - radius, center + radius + 1))
    return (value - a * center * center // denominator) % 2


def grid_and_congruence_checks():
    constant_moduli = {1, 2, 3, 6}
    for d in range(1, 2001):
        bits = {outer(a, d) for a in range(d) if gcd(a, d) == 1}
        if d == 4:
            assert bits == {0}  # The perturbation of the quarter boundary decides the actual bit.
        else:
            assert (len(bits) == 1) == (d in constant_moduli)

    witnesses = strata = 0
    for h in range(1, 81):
        expected = 1 if h // gcd(h, 2) in constant_moduli else 2
        for modulus in ([1, 8*h] if expected == 2 and h <= 40 else [1]):
            outcomes = set()
            for p in range(max(17, h + 1) | 1, 20000, 2):
                if gcd(p, h*modulus) != 1 or not prime(p):
                    continue
                # Solve p(kp+h) = 1 mod modulus.
                k0 = ((pow(p, -1, modulus) - h) * pow(p, -1, modulus)) % modulus
                for j in range(1, 100):
                    q = (k0 + modulus*j) * p + h
                    if not prime(q):
                        continue
                    assert (p*q - 1) % modulus == 0 and q > p
                    outcomes.add(outer(mixed_root(p, q), p*q))
                    break
                if len(outcomes) == expected:
                    break
            assert len(outcomes) == expected, (h, modulus, outcomes)
            if modulus == 1:
                witnesses += len(outcomes)
            else:
                strata += 1
    print('unit grids', 2000, 'prime-pair witnesses', witnesses, 'public strata', strata)


def dyadic_table_checks():
    checks = literal = 0
    for s in range(3, 12):
        scale = 1 << s
        for odd in (1, 3):
            h = odd * scale
            p = next(p for p in range(h + 17, h + 10000, 2) if prime(p))
            for sign in (-1, 1):
                q = next(k*p + sign*h for k in range(2, 1000)
                         if k*p + sign*h > p and prime(k*p + sign*h))
                for c in (scale//4, scale//2, scale):
                    d = h // gcd(h, 2*c)
                    bit = int(d in (1, 6))
                    assert p*q*4 >= h*h and outer(c*mixed_root(p, q), p*q) == bit
                    if s <= 4:
                        assert centered_floor_bit(p*q, c) == 1 ^ bit
                        literal += 1
                    checks += 1
    print('unbounded table checks', checks, 'literal floor sums', literal)


def square_roots_power2(a, exponent):
    roots = [0]
    modulus = 1
    for _ in range(exponent):
        roots = [x for r in roots for x in (r, r + modulus) if (x*x - a) % (2*modulus) == 0]
        modulus *= 2
        assert len(roots) <= 4
    return roots


def branch_checks():
    instances = bits = literal = 0
    for s in range(4, 11):
        h = 1 << s
        p = next(p for p in range(h + 17, h + 1000, 2) if prime(p))
        for e_max in range(3, min(5, s-1) + 1):
            modulus = 1 << (e_max+1)
            for sign in (-1, 1):
                start = 1 if s <= 5 else 1000000
                k = next(1 + j*modulus for j in range(start, start + 1000)
                         if prime((1 + j*modulus)*p + sign*h))
                q = k*p + sign*h
                n = p*q
                roots = square_roots_power2(n % modulus, e_max+1)
                assert {r % (modulus//2) for r in roots} == {p % (modulus//2), -p % (modulus//2)}
                for e in range(3, e_max + 1):
                    d = 1 << e
                    c = h // (2*d)
                    predicted = outer(pow(roots[0], -1, d), d)
                    assert predicted == outer(c*mixed_root(p, q), n)
                    if start == 1:
                        assert centered_floor_bit(n, c) == 1 ^ predicted
                        literal += 1
                    else:
                        bits += 1
                if start > 1:
                    assert k >= 16000001
                    instances += 1
    print('large multiplier fixtures', instances, 'bits', bits, 'additional literal floor sums', literal)


if __name__ == '__main__':
    grid_and_congruence_checks()
    dyadic_table_checks()
    branch_checks()
