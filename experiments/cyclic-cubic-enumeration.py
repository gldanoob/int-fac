"""Exact angular enumeration of monic cubics of positive square discriminant."""

from fractions import Fraction
from itertools import groupby, product
from math import gcd, isqrt
from bisect import bisect_left, bisect_right
from sys import argv

UNITS = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]


def mul(z, w):
    u, v = z
    x, y = w
    return u*x - v*y, u*y + v*x - v*y


def conjugate(z):
    u, v = z
    return u-v, -v


def power(z, exponent):
    result = (1, 0)
    for _ in range(exponent):
        result = mul(result, z)
    return result


def norm_points(limit):
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for v in range(p*p, limit + 1, p):
                if spf[v] == v:
                    spf[v] = p
    split = {}
    radius = isqrt(2*limit)
    for u, v in product(range(-radius, radius + 1), repeat=2):
        num = u*u - u*v + v*v
        if 1 < num <= limit and num % 3 == 1 and spf[num] == num:
            split.setdefault(num, (u, v))

    def points(num):
        choices = []
        while num > 1:
            p, exponent = spf[num], 0
            while num % p == 0:
                num //= p
                exponent += 3
            if p == 3:
                choices.append([power((1, -1), exponent)])
            elif p % 3 == 2:
                if exponent % 2:
                    return
                choices.append([(p**(exponent//2), 0)])
            else:
                z = split[p]
                w = conjugate(z)
                choices.append([mul(power(z, j), power(w, exponent-j))
                                for j in range(exponent + 1)])
        for factors in product(UNITS, *choices):
            z = (1, 0)
            for w in factors:
                z = mul(z, w)
            yield z

    return points


def sparse(height, cube_only=True):
    cubes = {-a**3 for a in range(1, height + 1) if a**3 <= height}
    constants = cubes if cube_only else range(-height, height+1)
    points = norm_points(height*height + 3*height)
    for a, b in product(range(-height, height + 1), repeat=2):
        key = a*a - 3*b
        if key <= 0:
            continue
        for u, v in points(key):
            if v <= 0 or v % 3:
                continue
            numerator = 2*u-v - 2*a**3 + 9*a*b
            if numerator % 27 == 0 and numerator//27 in constants:
                yield a, b, numerator//27


def brute(height, cube_only=True):
    limit = 1
    while (limit+1)**3 <= height:
        limit += 1
    constants = (-n**3 for n in range(1, limit+1)) if cube_only else range(-height, height+1)
    for a, b, c in product(range(-height, height+1), range(-height, height+1), constants):
        disc = a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c
        if disc > 0 and isqrt(disc)**2 == disc:
            yield a, b, c


def norm(z):
    u, v = z
    return u*u - u*v + v*v


def upper_farey(x, limit):
    """Least fraction >= x with denominator at most limit."""
    if x.denominator <= limit:
        return x
    n, d = x.numerator, x.denominator
    p0, q0, p1, q1 = 0, 1, 1, 0
    while True:
        a = n // d
        q2 = q0 + a*q1
        if q2 > limit:
            k = (limit-q0)//q1
            bounds = Fraction(p0+k*p1, q0+k*q1), Fraction(p1, q1)
            return max(bounds)
        p0, q0, p1, q1 = p1, q1, p0+a*p1, q2
        n, d = d, n-a*d


def farey_interval(low, high, limit):
    value = upper_farey(low, limit)
    while value <= high:
        n, d = value.numerator, value.denominator
        yield n, d
        next_d = -pow(n, -1, d) % d if d > 1 else 0
        next_d += ((limit-next_d)//d)*d
        value = Fraction((1+n*next_d)//d, next_d)


def coordinates(n, d, chart):
    if chart == 0:
        return n, d
    if chart == 1:
        return n, -d
    if chart == 2:
        return d, n
    return -d, n


def cone_intervals(z_at, width, precision):
    """A rational interval cover of |v| <= width |2u-v| for z(t)=u+vω."""
    if width is None:
        return [(Fraction(-1), Fraction(1))]

    def boundary(t, direction):
        u, v = z_at(t)
        return v*width.denominator + direction*(2*u-v)*width.numerator

    cuts = []
    grid = [Fraction(j, 4) for j in range(-4, 5)]
    for direction in (-1, 1):
        for lo, hi in zip(grid, grid[1:]):
            left = boundary(lo, direction)
            right = boundary(hi, direction)
            if not left:
                cuts.append((lo, lo))
            if not right:
                cuts.append((hi, hi))
            if left*right >= 0:
                continue
            for _ in range(precision):
                mid = (lo+hi)/2
                value = boundary(mid, direction)
                if not value:
                    lo = hi = mid
                    break
                if left*value > 0:
                    lo, left = mid, value
                else:
                    hi = mid
            cuts.append((lo, hi))

    # Cover boundary brackets and test one exact midpoint in each intervening gap.
    intervals = []
    current = Fraction(-1)
    for lo, hi in sorted([*cuts, (Fraction(1), Fraction(1))]):
        if lo > current:
            mid = (current+lo)/2
            if boundary(mid, -1)*boundary(mid, 1) <= 0:
                intervals.append((current, lo))
        if hi >= current:
            intervals.append((max(current, lo), hi))
            current = hi
    return intervals


def primitive_vectors(limit):
    radius = isqrt(2*limit)
    for z in product(range(-radius, radius+1), repeat=2):
        n = norm(z)
        if 0 < n <= limit and gcd(*z) == 1:
            yield z, n


def dyadic(limit):
    value = 1
    while value <= limit:
        yield value
        value *= 2


def gap_le(i, j, upper):
    return 4*i**3 <= (upper+abs(j))**2


def shifts(i, j, height):
    # Polynomial P(a) = a³-3ia is monotone on each integer block.
    s = isqrt(i)
    blocks = [(-height, -s), (max(-s, -height), min(s, height)+1),
              (s+1, height+1)]
    for index, (lo, hi) in enumerate(blocks):
        if lo >= hi:
            continue
        sign = -1 if index == 1 else 1
        candidates = range(lo, hi)
        def key(a):
            return sign*(a*a*a-3*i*a+j)
        first = bisect_left(candidates, -27*height, key=key)
        last = bisect_right(candidates, 27*height, key=key)
        for a in candidates[first:last]:
            b, rem_b = divmod(a*a-i, 3)
            c, rem_c = divmod(a*a*a-3*i*a+j, 27)
            if rem_b == rem_c == 0 and abs(b) <= height:
                yield a, b, c


def width_for(gap, lower_i):
    # A dyadic upper bound for sqrt(gap / lower_i**(3/2)).
    top, bottom = gap, lower_i*isqrt(lower_i)
    if 16*top >= bottom:
        return None
    width = Fraction(1)
    while 4*top <= bottom:
        top *= 4
        width /= 2
    return width


def cubic_candidates(height):
    limit = height*height+3*height
    small = 0
    while (small+1)**3 <= height*height:
        small += 1
    points = norm_points(small)
    for i in range(1, small+1):
        for u, v in points(i):
            if v > 0 and v % 3 == 0:
                yield from shifts(i, 2*u-v, height)

    buckets = {}
    for z, n in primitive_vectors(2*isqrt(limit)):
        buckets.setdefault(1 << (n.bit_length()-1), []).append((z, n))
    precision = 16+6*height.bit_length()
    for content in range(1, isqrt(limit)+1):
        rr = content*content
        for small_bin in dyadic(isqrt(limit//rr)):
            for big_bin in dyadic(limit//(rr*small_bin)):
                if big_bin < small_bin:
                    continue
                lower_i = rr*small_bin*big_bin
                if 4*lower_i <= small:
                    continue
                gap = 64*height
                previous = -1
                gap_limit = min(16*lower_i*(isqrt(lower_i)+1),
                                2048*height*height//isqrt(lower_i)+1)
                while previous < gap_limit:
                    width = width_for(gap, lower_i)
                    for z, small_norm in buckets.get(small_bin, ()):
                        # Roles denote the exponent of the larger Eisenstein factor.
                        for exponent in ((1, 3) if big_bin != small_bin else (3,)):
                            fixed = power(z, 4-exponent)
                            for chart in range(4):
                                def z_at(t):
                                    w = coordinates(t.numerator, t.denominator, chart)
                                    return mul(fixed, power(w, exponent))

                                denominator_limit = isqrt(4*big_bin)
                                for lo, hi in cone_intervals(z_at, width, precision):
                                    for num, den in farey_interval(lo, hi, denominator_limit):
                                        w = coordinates(num, den, chart)
                                        big_norm = norm(w)
                                        if not big_bin <= big_norm < 2*big_bin:
                                            continue
                                        i = rr*small_norm*big_norm
                                        if not small < i <= limit:
                                            continue
                                        eta_norm = small_norm if exponent == 3 else big_norm
                                        u, v = mul(fixed, power(w, exponent))
                                        scale = eta_norm*content**3
                                        if v <= 0 or v*scale % 3:
                                            continue
                                        j = (2*u-v)*scale
                                        if gap_le(i, j, gap) and (previous < 0 or not gap_le(i, j, previous)):
                                            yield from shifts(i, j, height)
                    previous, gap = gap, gap*2


def cubics(height, cube_only=False):
    """Yield each positive-square cubic once, in lexicographic order."""
    if height < 1:
        raise ValueError("height must be positive")
    cubes = []
    a = 1
    while a**3 <= height:
        cubes.append(a**3)
        a += 1
    for f, _ in groupby(sorted(cubic_candidates(height))):
        if not cube_only:
            yield f
        else:
            index = bisect_left(cubes, -f[2])
            if index < len(cubes) and cubes[index] == -f[2]:
                yield f


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O so list checks are enabled")
    if argv[1:2] == ["--list"]:
        for f in cubics(int(argv[2]), cube_only=True):
            print(*f)
        raise SystemExit

    for height in map(int, argv[1:] or ("1", "2", "3", "4", "5", "8", "16", "32", "64")):
        all_found = list(cubics(height))
        assert all_found == sorted(set(sparse(height, cube_only=False))), ("Eisenstein mismatch", height)
        assert all_found == sorted(set(brute(height, cube_only=False))), ("direct mismatch", height)
        cubes = {-a**3 for a in range(1, height+1) if a**3 <= height}
        print(height, len(all_found), sum(f[2] in cubes for f in all_found), flush=True)
