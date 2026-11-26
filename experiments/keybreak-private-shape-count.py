"""Finite checks of the private-block overcount and the revised epoch ledger."""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt


def smooth(value, cutoff):
    for divisor in range(2, cutoff+1):
        while value % divisor == 0:
            value //= divisor
    return value == 1


def check_shapes(n, omega, cutoff):
    width = isqrt(2*n)+1
    smooth_coords = {k for k in range(1, width+1) if smooth(k, cutoff)}
    roots = Counter(pow(h, 2, n) for h in range(1, n) if gcd(n, h) == 1)
    assert set(roots.values()) == {2**omega}
    # Exhaust the whole short-vector box rather than assuming a reduction tie rule.
    shortest = {}
    smooth_pairs = set()
    for v in range(1, width+1):
        if gcd(v, n) != 1:
            continue
        inverse_v = pow(v, -1, n)
        for u in range(-width, width+1):
            if not u or gcd(u, n*v) != 1:
                continue
            residue = u*inverse_v % n
            if residue not in roots:
                continue
            key = u*u+v*v, u, v
            if residue not in shortest or key < shortest[residue]:
                shortest[residue] = key
            if abs(u) in smooth_coords and v in smooth_coords:
                smooth_pairs.add((u, v))
    launched = sum(roots[r] for r, (_, u, v) in shortest.items()
                   if abs(u) in smooth_coords and v in smooth_coords)
    assert launched <= 2**omega*len(smooth_pairs) <= 2**(omega+1)*len(smooth_coords)**2
    print(f"N={n}: {launched} smooth-vector private roots, {len(roots)} unit squares")


for n, omega in [(35, 2), (125, 1), (341, 2), (7*11*13, 3), (7**2*11, 2)]:
    check_shapes(n, omega, 3)

F = Fraction
b, private_loss, slack = F(19, 20), F(9, 20), F(3, 40)
assert b+private_loss == F(7, 5)
assert F(237, 80)-private_loss+slack == F(207, 80)
algebraic_invocations = F(62, 25)-private_loss+slack
assert algebraic_invocations == F(421, 200)
h1_squared = F(76313, 322500)
h0_squared = F(4489, 2250)
target = F(2813, 1000)
assert h0_squared < (target-b-private_loss)**2
assert h1_squared < (target-algebraic_invocations)**2
assert 7**9 < 2**26  # Strassen exponent below 26/9.
assert b*F(26, 9) < target
print("private-shape cap and 2.813 terminal ledger passed")

theta = F(993, 1000)
coordinate_budget = F(2804, 1000)-b-private_loss/theta
assert coordinate_budget > 0
per_test_square = F(20001, 10000)**2 * F(40, 81)*theta
assert per_test_square < coordinate_budget**2
print("tightened private band: coefficient", float(b+private_loss/theta)+float(per_test_square)**.5)

# Only the eventual band containment needs a very large synthetic bit length.
for power in (12000, 24000):
    width = 2**power
    k0 = 2**(power//3)
    lx = (width-1)//2-2
    e0 = (width-5)//(2*k0)-1
    es = 993*e0//1000
    ks = (lx+es-1)//es
    ms = ks.bit_length()
    k = ks+(ks+ms-1)//ms
    offset = k*es-lx
    last = 2*(offset+k)//k
    assert es-last-1 >= (127*e0+127)//128
    assert k <= 2*k0 and offset <= k*last//2 <= offset+k and 2*ms*(last+1) >= es
print("eventual private band checks passed")
