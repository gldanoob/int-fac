"""Reduced quadratic forms and their modular comparison roots, discriminants -4N and -8N."""
from collections import Counter, defaultdict
from math import gcd, isqrt


def centered(value, modulus):
    """Unique lift in (-modulus/2, modulus/2]."""
    return (value + (modulus-1)//2) % modulus - (modulus-1)//2


def reduce_form(a, b, c):
    """Properly reduce [a,2b,c], retaining the first transformation column."""
    x, y, other_x, other_y = 1, 0, 0, 1
    while True:
        shift = (centered(b, a) - b) // a
        other_x, other_y = other_x + shift*x, other_y + shift*y
        c, b = c + 2*shift*b + shift*shift*a, b + shift*a
        if a < c or (a == c and b >= 0):
            return (a, b, c), (x, y)
        a, b, c = c, -b, a
        x, y, other_x, other_y = other_x, other_y, -x, -y


def oriented_square(params, n, *, radicand=None):
    """Square a primitive ideal coprime to N and return the reduced ideal and root."""
    radicand = n if radicand is None else radicand
    assert radicand in (n, 2*n) and n > 1 and n % 2
    a, b, c = params
    assert a*c == b*b + radicand and gcd(a, n) == gcd(a, gcd(2*b, c)) == 1
    content = gcd(a, 2*b)
    t, slope = a // content, 2*b // content
    modulus = t*t
    v = pow(slope, -1, t) if t > 1 else 0
    u = (1 - v*slope) // t
    lift = (u * t*b + v*((b*b - radicand)//content)) % modulus
    assert (lift*lift + radicand) % modulus == 0
    reduced, (x, y) = reduce_form(modulus, lift, (lift*lift + radicand)//modulus)
    root = (modulus*x + lift*y) * pow(t, -1, n) % n
    assert root*root % n == reduced[0] % n
    return reduced, root


def canonical_forms(radicand):
    """Enumerate small fixtures; the large-input proposal samples A with its factors."""
    for a in range(1, isqrt(4*radicand//3) + 1):
        for b in range(-((a-1)//2), a//2 + 1):
            c, rem = divmod(b*b+radicand, a)
            if not rem and (a < c or (a == c and b >= 0)) and gcd(a, gcd(2*b, c)) == 1:
                yield a, b, c


def prime_to_input(form, n):
    """Find an equivalent test representative whose norm is prime to n."""
    a, b, c = form
    if gcd(a,n) == 1:
        return form
    for x in range(2*n):
        candidate = a*x*x + 2*b*x + c
        if gcd(candidate, n) == 1:
            # Columns (x,1),(-1,0) have determinant one.
            return candidate, -a*x-b, a
    raise AssertionError("no primitive representative in fixture search")


def check(n, *, radicand=None):
    radicand = n if radicand is None else radicand
    distribution = defaultdict(Counter)
    for form in canonical_forms(radicand):
        reduced, root = oriented_square(prime_to_input(form, n), n, radicand=radicand)
        if gcd(reduced[0], n) == 1:
            distribution[reduced][root] += 1
            distribution[reduced][-root % n] += 1
    for form, fiber in distribution.items():
        exact = {z for z in range(n) if z*z % n == form[0] % n}
        assert set(fiber) == exact and len(set(fiber.values())) == 1
    return len(distribution)


if __name__ == "__main__":
    inputs = list(range(3, 602, 2))
    for multiplier in (1, 2):
        count = sum(check(n, radicand=multiplier*n) for n in inputs)
        print(f"-{4*multiplier}N: {len(inputs)} odd moduli, {count} uniform reduced-form fibers")
