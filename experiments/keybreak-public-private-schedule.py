"""Exact checks for the retuned public boxes and staged private shape tests."""
from fractions import Fraction as F
from math import floor

delta, kappa = F(4, 5), F(7, 5)
beta, lam, height = F(103, 100), F(102, 25), F(133, 50)
alpha, gamma = F(251, 500), F(49, 50)
epsilon, slack = F(1, 100), F(1, 10000)
b, M = delta*beta, delta**-3
y0 = 1/(2*kappa)
v0 = alpha*y0
y1 = v0/lam
v1 = alpha*y1
parent_floor = F(503, 1000)
slope_sum = alpha+gamma
assert alpha < parent_floor and alpha/lam < parent_floor
assert F(265, 100) < M*(1+2*v0) < height < beta*(lam-slope_sum)
assert 2*alpha > 1 and slope_sum > 1 and 2*v0 > y0 and v0 < F(1, 2)
assert (lam-1)*slope_sum*beta-height > 0
assert 2*alpha-3*alpha/lam > 0
assert (1+epsilon)*y1-(F(1, 2)-epsilon)*(1+v1) < -F(1, 4)
assert (1+epsilon)*y1-(F(1, 2)-epsilon)*(1+v0-y0) < -F(1, 4)
assert (1+epsilon)*F(196, 100)-(F(1, 2)-epsilon)*(F(265, 100)+slope_sum*beta) < -F(1, 25)
mean = (2*slope_sum-1)*beta-lam/3-M/(3*beta)
assert mean > F(1, 50)

s_a = delta*lam/3
s_r = (1+v1)/(3*delta*b)
curve = F(20001, 10000)
h = F(21823, 20000)
assert curve**2*2*y0/(3*delta) < h*h
v = [F(71, 100)+F(29, 100)*j/127 for j in range(128)]
a = [x*x for x in v]
assert parent_floor < a[0]
shape_loss = 2*kappa*delta/3
w = [h*(y-x) for x, y in zip(v, v[1:])]
w.append(shape_loss-sum(x*m for x, m in zip(a, w)))
f = [x*m/shape_loss for x, m in zip(a, w)]
assert min(w) > 0 and sum(f) == 1 and sum(w)/shape_loss < 2
private = [b+sum(w[i:])+h*v[i]+slack for i in range(128)]
target = F(243, 100)
assert max(private) == min(private) < target
assert b+s_a+s_r+2*slack < target
alg_base = b+s_a+2*slack
assert 0 < target-alg_base and (target-alg_base)**2 > curve**2*2*y1/(3*delta)
assert max(8*delta/3, b+2*delta, F(26, 10)*b, 2*b) < target
print(f"public height {float(M*(1+2*v0)):.9f}; bottom mean {float(mean):.9f}")
print(f"private coordinates {float(max(private)):.9f}; raw descent {float(b+s_a+s_r+2*slack):.9f}; "
      f"algebraic tests {float(alg_base)+float(curve**2*2*y1/(3*delta))**.5:.9f}; "
      f"retained characters {float(b+2*delta):.9f}")


def ceildiv(numerator, denominator):
    return -(-numerator//denominator)


def first_degree(n, mb):
    lower = (64*n)//(125*mb)
    d = 1 << ceildiv(lower.bit_length(), 3)
    while True:
        step = (2*d+lower//(d*d))//3
        if step >= d:
            break
        d = step
    if 125*d**3*mb < 64*n:
        d += 1
    return max(3, d | 1)


def verify_integer_schedule(n):
    mb = n.bit_length()
    d = first_degree(n, mb)
    assert 125*(d-2)**3*mb < 64*n <= 125*d**3*mb
    t = d*mb
    k0 = ceildiv(7*d, 5)
    e0 = (n-5)//(2*k0)-1
    base = ceildiv(103*t, 100)
    th = 133*d*t//50
    cut = e0
    depth = 0
    while cut > base:
        box_num = 251*cut+490*base
        box = ceildiv(box_num, 500)
        if depth == 0:
            assert 2*(th+d*box) <= n-1
        child = max(base, ceildiv(d*box_num+500*th, 2040*d))
        assert child < cut and box >= child+6 and box > base+1 and 2*box >= cut
        cut = child
        depth += 1
    lx = (n-1)//2-2
    remaining = lx
    left = ceildiv(503*e0, 1000)
    factor_count = 0
    for i, (scale, fraction) in enumerate(zip(a, f)):
        right = floor(scale*e0)
        length = remaining if i == len(f)-1 else floor(fraction*lx)
        remaining -= length
        first = ceildiv(length, right)
        bits = first.bit_length()
        count = first+ceildiv(first, bits)
        offset = count*right-length
        last = 2*(offset+count)//count
        assert right-last-1 >= left and 2*bits*(last+1) >= right
        assert offset <= count*last//2 <= offset+count
        factor_count += count
        left = right
    assert remaining == 0 and factor_count <= 2*k0
    print(f"integer parameter replay: {depth} public transitions and {len(f)} disjoint private bands")


verify_integer_schedule(2**12000)
