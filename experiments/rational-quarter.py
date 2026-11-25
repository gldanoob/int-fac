"""Complete finite grids for quadratic predictors and small combinations of slopes."""

from cmath import exp
from itertools import product
from math import gcd, isqrt, tau


def sign(t, n):
    return 1 if 4 * min(t % n, -t % n) < n else -1


def mixed_root(d, e):
    return (1 - 2*d*pow(d, -1, e)) % (d*e)


def gauss_sums():
    count = 0
    for n in range(3, 28, 2):
        roots = [exp(1j*tau*t/n) for t in range(n)]
        for m, k in product(range(n), repeat=2):
            g = gcd(m, n)
            raw = sum(roots[(m*(t*t+3*t+1)+k*t) % n] for t in range(n))
            assert abs(abs(raw)**2 - (n*g if k%g == 0 else 0)) < 1e-8
            count += 1
    print(f'{count} complete quadratic sums, including nonunit Fourier indices')


def best_interval(hist):
    high = low = top = bottom = 0
    for v in hist:
        high = max(0, high+v)
        low = min(0, low+v)
        top = max(top, high)
        bottom = min(bottom, low)
    total = sum(hist)
    return 2*max(top, total-bottom) - total


def quadratic_menu(d, e):
    n, r = d*e, mixed_root(d, e)
    labels = [sign(r*t, n) for t in range(n)]
    best = cases = 0
    for a in range(1, n):
        if gcd(a, n) != 1:
            continue
        squares = [a*t*t % n for t in range(n)]
        for b in range(n):
            hist = [0]*n
            for t, bit in enumerate(labels):
                hist[(squares[t]+b*t)%n] += bit
            observed = best_interval(hist)
            if n == 15:
                brute = max(abs(2*sum((hist*2)[i:i+j])-sum(hist))
                            for i in range(n) for j in range(n+1))
                assert brute == observed
            best = max(best, observed)
            cases += 1
    print(f'n={n}, {cases} unit-leading quadratics, best signed interval correlation {best}/{n}')


def jacobi(a, n):
    value = 1
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                value = -value
        if a % 4 == n % 4 == 3:
            value = -value
        a, n = n % a, a
    return value if n == 1 else 0


def slope_gcd(n, slopes, bound):
    for coeffs in product(range(-bound, bound+1), repeat=len(slopes)):
        a = sum(m*x for m, x in zip(coeffs, slopes))
        for k in range(1, bound+1):
            for v in (a-k, a+k):
                shared = gcd(v, n)
                if 1 < shared < n:
                    return shared
    return None


def predictors(d, e):
    n, r = d*e, mixed_root(d, e)
    slope = isqrt(n)
    counts, positive = {}, [0, 0]
    units = 0
    for t in range(n):
        if gcd(t, n) != 1:
            continue
        units += 1
        label = sign(r*t, n)
        inv = pow(t, -1, n)
        menu = (sign(t, n), sign(t*t+t, n), sign(inv, n), sign(slope*t, n),
                jacobi(t+3, n), jacobi(t*t+1, n))
        counts[menu] = counts.get(menu, 0) + label
        # Nonlinear terms cancel in one small combination for the planted tests.
        for i, nonlinear in enumerate((t*t, inv)):
            guess = sign(nonlinear+slope*t,n)*sign(nonlinear+(slope-r)*t,n)
            positive[i] += guess == label
    assert slope_gcd(n, [slope, slope-r], 1) in (d, e)
    public_split = slope_gcd(n, [1, slope], 2)
    if public_split is not None:
        assert n % public_split == 0 and 1 < public_split < n
    accuracy = (units+sum(map(abs,counts.values()))) // 2
    assert units//2 <= accuracy <= units
    assert min(positive)*3 > 2*units
    print(f'n={n}, {units} units, best public-menu score {accuracy}, '
          f'public small combination gcd {public_split}, planted scores {positive}, '
          f'recovered {slope_gcd(n,[slope,slope-r],1)}')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O so the checks are enabled')
    gauss_sums()
    for blocks in ((3,5),(5,7),(9,5),(7,11),(9,11),(11,13)):
        quadratic_menu(*blocks)
    for blocks in ((101,103),(101,149),(101**2,103),(503,1009)):
        predictors(*blocks)
