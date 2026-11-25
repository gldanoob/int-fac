"""Check the fixed-schedule proof's pole, divided class and linear-Gaussian contour."""

import cmath
from itertools import combinations
from math import ceil, exp, expm1, gcd, log, pi, prod, sin


def simpson(function, start, end, parts):
    assert parts % 2 == 0
    step = (end-start)/parts
    return step/3 * (function(start) + function(end) + sum(
        (4 if j % 2 else 2)*function(start + j*step) for j in range(1, parts)))


def exponential_ratio(w):
    if abs(w) < 1e-4:
        return 1 + w*(1/2 + w*(1/6 + w*(1/24 + w/120)))
    return (cmath.exp(w)-1)/w


def check_residues():
    x, y = 10.5, 29.5
    def difference(w):
        return cmath.exp(w * log(x)) * log(y/x) * exponential_ratio(w*log(y/x))
    rectangle = [-0.4-1j, 0.45-1j, 0.45+1j, -0.4+1j]
    cases = (0, 1e-14+2e-15j, 0.13-0.67j, -0.36+0.84j, 0.12+1.23j, -0.6-0.38j)
    mismatch = 0
    for pole in cases:
        contour = 0
        for first, second in zip(rectangle, rectangle[1:]+rectangle[:1]):
            direction = second-first
            contour += simpson(lambda z: direction*difference(first+z*direction)
                              / (first+z*direction-pole), 0, 1, 4096)
        residue = difference(pole) if -0.4 < pole.real < 0.45 and abs(pole.imag) < 1 else 0
        mismatch = max(mismatch, abs(contour/(2j*pi)-residue))
    assert mismatch < 2e-11
    return len(cases), mismatch


def squarefree_products(primes):
    return {prod(subset) for size in range(len(primes)+1) for subset in combinations(primes, size)}


def check_nonunits():
    count = nonempty = repeated = ineligible = 0
    for allowed in ((3, 5, 7, 11, 13), (5, 7, 11, 13), (3, 7, 13)):
        values = squarefree_products(allowed)
        for q in (9, 15, 21, 27, 35, 45, 63, 75, 105, 165, 225, 385):
            for residue in range(q):
                g = gcd(q, residue)
                if g == 1:
                    continue
                actual = {n for n in values if n % q == residue}
                if g not in values:
                    reduced = set()
                    ineligible += 1
                else:
                    assert gcd(residue//g, q//g) == 1
                    available = [p for p in allowed if q % p != 0]
                    reduced = {g*m for m in squarefree_products(available) if (m-residue//g) % (q//g) == 0}
                    if gcd(g, q//g) > 1:
                        repeated += 1
                assert actual == reduced
                count += 1
                nonempty += bool(actual)
                y, s = 199.5, 17.25
                left = sum(q/s * exp(-pi*((n-y)/s)**2) for n in actual)
                right = sum((q//g)/(s/g) * exp(-pi*((n//g-y/g)/(s/g))**2) for n in reduced)
                assert abs(left-right) < 2e-12
    return count, nonempty, repeated, ineligible


def gaussian_contours(primes, y, ratio, character):
    # The true compact cutoff is identically one for |log(x/Y)| <= 0.29.
    # Restrict to 0.28. The omitted finite-transform segment has absolute mass
    # bounded by O(T R exp(-pi*R^2*(1-exp(-0.28))^2)) times these finite factors.
    values = [(n, character(n)) for n in squarefree_products(primes) if character(n)]
    lower, alpha, upper_t = 0.54, 0.88, 28*ratio
    corner = max(primes)**(alpha-lower)
    limit, parts = 0.28*ratio, 1400
    step = 2*limit/parts
    nodes = []
    for j in range(parts+1):
        u = -limit+j*step
        v = u/ratio
        weight = (1 if j in (0, parts) else 4 if j % 2 else 2)*step/3
        nodes.append((v, weight*exp(-pi*(ratio*expm1(v))**2)/y))

    def segment_const(sigma, t0, t1):
        total = 0.
        for n, chi in values:
            base = log(y/n)
            for v, wt in nodes:
                phase = base+v
                sineint = (sin(t1*phase) - sin(t0*phase))/phase if abs(phase) > 1e-10 else t1-t0
                total += wt*chi*exp(sigma*phase)*sineint/pi
        return total

    def segment_bent(t):
        sigma = alpha - log(t)/log(max(primes))
        s = sigma+1j*t
        derivative = -1/(t*log(max(primes)))
        transform = sum(wt*cmath.exp(s*v) for v, wt in nodes)
        dirichlet = sum(chi*cmath.exp(s*log(y/n)) for n, chi in values)
        return ((1-1j*derivative)*transform*dirichlet).real/pi

    def horizontal(t, start, end):
        total = 0.
        for n, chi in values:
            for v, wt in nodes:
                phase = log(y/n) + v
                if phase:
                    total += wt*chi*exp(start*phase)*expm1((end-start)*phase)*sin(t*phase)/(phase*pi)
        return total

    direct = sum(chi*ratio/y*exp(-pi*(ratio*(n/y-1))**2) for n, chi in values)
    straight = segment_const(lower, 0, upper_t)
    bent = segment_const(alpha, 0, 1) + simpson(segment_bent, 1, corner, 200)
    bent += segment_const(lower, corner, upper_t)
    middle = (alpha+lower)/2
    stepped = (segment_const(alpha, 0, 1) + horizontal(1, alpha, middle)
               + segment_const(middle, 1, corner) + horizontal(corner, middle, lower)
               + segment_const(lower, corner, upper_t))
    return max(abs(straight-direct), abs(bent-direct), abs(stepped-direct)), abs(bent-straight), abs(stepped-straight)


def check_gaussian():
    cases = (((5, 7, 11, 13, 17), 80.0, 32), ((5, 7, 11, 13, 19), 142.0, 37))
    characters = (lambda n: 1, lambda n: (0, 1, 0, -1)[n % 4])
    error = bend_error = step_error = 0.
    for p, y, ratio in cases:
        for chi in characters:
            delta, bend, stepped = gaussian_contours(p, y, ratio, chi)
            error = max(error, delta)
            bend_error = max(bend_error, bend)
            step_error = max(step_error, stepped)
    assert max(error, bend_error, step_error) < 1e-9
    return len(cases)*len(characters), error, bend_error, step_error


if __name__ == '__main__':
    print('pole contours, maximum residue discrepancy:', *check_residues())
    print('nonunit classes, nonempty, retained prime powers, incompatible:', *check_nonunits())
    print('linear-Gaussian comparisons, maximum enumeration, bend and rectangular discrepancies:', *check_gaussian())
