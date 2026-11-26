"""Preserve sparse private rows while separating planted real signatures."""

from fractions import Fraction
from math import gcd, prod
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
SPARSE = run_path(str(HERE / "cogentic-short-field-list.py"))
PREFILTER = run_path(str(HERE / "cogentic-monic-square-probes.py"))["prefilter"]
DRIVER = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))
multiply, evaluate = SPARSE["multiply"], SPARSE["evaluate"]


def signatures(n, fixture):
    m, fields, cuts, primes, norms, _ = fixture
    r = len(cuts)
    assert m > 2*r+1
    p = [1]
    for cut in cuts:
        p = multiply(p, [-cut, 1])
    step = multiply([-m, 1], p)
    scale = 4*prod(primes)
    step = [scale*c for c in step]
    bump = multiply(step, [i*c for i, c in enumerate(p) if i])
    limit = 2*r+1
    bound = max(evaluate(list(map(abs, f)), limit) for f in fields)
    bound += 2*evaluate(list(map(abs, step)), limit)
    denominator = (8*r)**r
    amplitude = bound*denominator+1
    for shift in range(3):
        modified = []
        for f in fields:
            f = f.copy()
            for i, c in enumerate(bump):
                f[i] += amplitude*c
            for i, c in enumerate(step):
                f[i] += shift*c
            modified.append(f)
        gcds = [gcd(evaluate([i*c for i, c in enumerate(f) if i], m), n) for f in modified]
        for divisor in gcds:
            if 1 < divisor < n:
                return divisor
        if gcds == [1, 1]:
            break
    else:
        raise AssertionError("no simple common reduction")

    for i, f in enumerate(modified):
        assert f[-1] == 1 and f[0] % 4 == 2 and all(c % 2 == 0 for c in f[:-1])
        assert evaluate(f, m) % n == 0
        for j, cut in enumerate(cuts):
            assert evaluate(f, cut) == norms[i][j] > 0
            assert evaluate(f, cut+Fraction(1, denominator)) < 0
            assert [x for x in range(primes[j]) if evaluate(f, x) % primes[j] == 0] == (
                [cut] if i == j % 2 else [])
            assert all((before-after) % primes[j] == 0 for before, after in zip(fields[i], f))
    return modified


def run():
    for n, h, r in ((50851,4,2), (2**61-1,4,2), (2**127-1,6,3)):
        original = SPARSE["build"](n, h, r)
        assert not isinstance(original, int)
        fields = signatures(n, original)
        if isinstance(fields, int):
            assert 1 < fields < n and n % fields == 0
            print(dict(n=n, construction_divisor=fields))
            continue
        m, _, cuts, _, _, _ = original
        disc = int(DRIVER["gp_value"](f"poldisc(Polrev({fields[0]}))*poldisc(Polrev({fields[1]}))", 5))
        surviving, stats = PREFILTER(fields, [(cut, 1) for cut in cuts], [1 << r], disc)
        assert not surviving
        print(dict(n=n, planted=r, parity_nullity=0, sign_probe_survivors=len(surviving), probes=stats["probes"]))
        if n == 50851:
            assert m == 15
            root = pow(-m, 3, n)
            assert root*root % n == 1 and gcd(root-1,n) == 211
            print(dict(n=n, correction_exponent=6, roots=[root,1], divisor=211))


if __name__ == '__main__':
    run()
