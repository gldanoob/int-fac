"""Exact convergents, mixed-root resonances and public square-root schedules."""

from itertools import combinations, product
from math import gcd, isqrt


def convergents(radicand, bound):
    root = isqrt(radicand)
    if root*root == radicand:
        return
    shift, den, a = 0, 1, root
    h0, h1, q0, q1 = 0, 1, 1, 0
    while True:
        h0, h1 = h1, a*h1+h0
        q0, q1 = q1, a*q1+q0
        if q1 > bound:
            return
        yield h1, q1
        shift = a*den-shift
        den = (radicand-shift*shift)//den
        a = (root+shift)//den


def squarefree_part(j):
    d = 2
    while d*d <= j:
        while j % (d*d) == 0:
            j //= d*d
        d += 1
    return j


def split(n, multipliers):
    for j in sorted(set(map(squarefree_part, multipliers))):
        if 1 < gcd(n, j) < n:
            return gcd(n,j), None
        for x, y in convergents(j*n, isqrt(isqrt(n))):
            norm = x*x - j*n*y*y
            if norm <= 0:
                continue
            k = isqrt(norm)
            if k*k == norm:
                for z in (x-k,x+k):
                    shared = gcd(z,n)
                    if 1 < shared < n:
                        return shared, (j,x,y,k)
    return None, None


def check_convergents():
    checked = 0
    for radicand in range(2, 800):
        if isqrt(radicand)**2 == radicand:
            continue
        observed = set(convergents(radicand, 24))
        for y in range(1,25):
            x = 1 + isqrt(radicand*y*y)
            if 2*(x*x-radicand*y*y) >= isqrt(radicand):
                continue
            g = gcd(x, y)
            assert (x//g,y//g) in observed
            checked += 1
    print(f'{checked} exact small-norm rational approximations recognized as convergents')


def census():
    primes = [p for p in range(1001,2001,2) if all(p%d for d in range(3,isqrt(p)+1,2))]
    fermat = one = several = total = 0
    for p, q in combinations(primes,2):
        n = p*q
        x = isqrt(n)+1
        immediate = isqrt(x*x-n)**2 == x*x-n
        f1, _ = split(n,[1]); fs, _ = split(n,[1,2,3,5,6])
        if f1 is not None:
            assert f1 in (p,q) and fs is not None
        if fs is not None:
            assert fs in (p,q)
        fermat += immediate; one += f1 is not None; several += fs is not None; total += 1
    print(f'{total} balanced prime pairs, first Fermat {fermat}, '
          f'short convergents j=1 {one}, five multipliers {several}')


def planted(p, q):
    n = p*q
    js = (1,2,8,3)
    slopes = [isqrt(j*n) for j in js]
    assert 49*p-25*q == 2
    x = (49*p+25*q)//2
    assert x*x-35**2*n == 1
    assert (x,35) in set(convergents(n,isqrt(isqrt(n))))
    found, proof = split(n,js)
    assert found in (p,q)
    assert isqrt((slopes[0]+1)**2-n)**2 != (slopes[0]+1)**2-n
    mixed = x % n
    assert {mixed % p, mixed % q} != {1} and gcd(mixed-1,n) in (p,q)
    mset = list(product(range(-2,3), repeat=len(js))) + [(35,0,0,0),(35,2,-1,0)]
    total = hits = 0
    for ms in mset:
        base = sum(m*a for m,a in zip(ms,slopes))
        classes = [ms[0],ms[1]+2*ms[2],ms[3]]
        for l in range(-45,46):
            center = base+l
            for k in range(1,4):
                total += 1
                if (center-k*mixed)%n and (center+k*mixed)%n:
                    continue
                hits += 1
                assert sum(v!=0 for v in classes)==1
                j,c = next((j,v) for j,v in zip((1,2,3),classes) if v)
                assert center**2-k*k == j*c*c*n
                g = gcd(abs(center),abs(c))
                assert (abs(center)//g,abs(c)//g) in set(convergents(j*n,isqrt(isqrt(n))))
    assert hits >= 2
    print(f'n={n}, {hits} of {total} tested coefficient triples resonated, '
          f'continued-fraction witness {proof}, factor {found}')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to check the identities')
    check_convergents()
    census()
    planted(1_001_173,1_962_299)
    planted(1000000000000000000000000000000380373,1960000000000000000000000000000745531)
