"""Sieve exact complete-parity columns by finite-field root lattices."""

import argparse
from ast import literal_eval
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path
from time import perf_counter


GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))
BASE = GRID["BASE"]
homogeneous = GRID["homogeneous"]
polynomial = GRID["polynomial"]
gp = GRID["gp"]

ROOTS = r'''
split_linear(R,p) = {
  my(d=poldegree(R), H);
  if(d==0, return([]));
  if(d==1, return([lift(-polcoef(R,0)/polcoef(R,1))]));
  for(t=0,p-1,
    H=gcd(R,lift(Mod(x+t,R)^((p-1)/2))-1);
    if(0<poldegree(H) && poldegree(H)<d,
      return(concat(split_linear(H,p),split_linear(R/H,p)));
    );
  );
  error("failed to split the distinct linear factors");
};
sieve_roots(P,p) = {
  if(p==2, return(select(t->subst(P,x,t)%2==0,[0,1])));
  my(F=Mod(1,p)*P, R=gcd(F,lift(Mod(x,F)^p)-x));
  vecsort(split_linear(R,p));
};
emit_roots(fields,primes) = {
  my(P=apply(Polrev,fields));
  for(k=1,#primes,
    my(p=primes[k]);
    for(i=1,#P,
      my(roots=sieve_roots(P[i],p));
      if(#roots, print([i,p,roots]));
    );
  );
};
'''


def lattice_marks(p, r, height):
    """Visit every primitive mark in the box satisfying a = r*b (mod p)."""
    if p <= height:
        for b in range(1, height + 1):
            first = -height + (r*b + height) % p
            for a in range(first, height + 1, p):
                yield a, b
        return
    if r == 0:
        yield 0, 1
        return
    x, y, s, t = p, 0, r, 1
    while True:
        norm = x*x + y*y
        if s*s + t*t < norm:
            x, y, s, t = s, t, x, y
            continue
        q = (2*(x*s + y*t) + norm) // (2*norm)
        if q == 0:
            break
        s, t = s - q*x, t - q*y
    if y < 0:
        x, y = -x, -y
    if x*t - y*s < 0:
        s, t = -s, -t
    # Cramer's rule bounds the coefficient of (s, t) in the rectangle.
    low = min(x, x*height) - y*height
    high = max(x, x*height) + y*height
    for k in range(-(-low // p), high // p + 1):
        if k == 0:
            if abs(x) <= height and y <= height:
                yield x, y
            continue
        j0 = -((k*t - 1) // y)
        j1 = (height - k*t) // y
        if x > 0:
            j0 = max(j0, -((height + k*s) // x))
            j1 = min(j1, (height - k*s) // x)
        else:
            j0 = max(j0, -((height - k*s) // -x))
            j1 = min(j1, (height + k*s) // -x)
        for j in range(j0, j1 + 1):
            yield j*x + k*s, j*y + k*t


def collect(n, m, fields, excluded, cutoff, *, height,
            include_ramified_two=False, mark_local=False):
    """Return the trial collector's rows given the true discriminant product."""
    if height < 1 or cutoff < 2*height**2 or not fields or any(
        len(coeffs) < 2 or coeffs[-1] != 1 for coeffs in fields
    ):
        raise ValueError("require positive height, cutoff >= 2*height**2, and nonconstant monic polynomials")
    if include_ramified_two:
        if not excluded or any(
            len(coeffs) < 3 or coeffs[0] % 4 != 2 or any(c % 2 for c in coeffs[:-1])
            for coeffs in fields
        ):
            raise ValueError("the ramified row requires a nonzero discriminant product and polynomials Eisenstein at two")
        while excluded % 2 == 0:
            excluded //= 2
    if mark_local:
        excluded = gcd(excluded, 2)
    coeff_lists = [list(coeffs) for coeffs in fields]
    # The row at two is handled explicitly for the Eisenstein family.
    skip = excluded * (2 if include_ramified_two else 1)
    primes = [p for p in GRID["primes_through"](cutoff) if skip % p]
    lines = gp(ROOTS + f"iferr(emit_roots({coeff_lists},{primes}),err,print(err);quit(1));\n",
               timeout=None)
    roots = [[] for _ in fields]
    for line in lines:
        i, p, residues = literal_eval(line)
        roots[i-1].append((p, residues))
    size = (2*height + 1)*height
    retained = [None] * size
    for a in range(-height, height + 1):
        for b in range(1, height + 1):
            if gcd(a, b) == 1 and gcd(a-b*m, n) == 1:
                retained[(a+height)*height + b - 1] = ((a, b), [], [], True)
    for i, (coeffs, prime_roots) in enumerate(zip(fields, roots, strict=True), 1):
        derivative = tuple(j*c for j, c in enumerate(coeffs) if j)
        values = [0] * size
        for j, entry in enumerate(retained):
            if entry is None:
                continue
            a, b = entry[0]
            value = abs(homogeneous(coeffs, a, b))
            if value == 0 or gcd(value, excluded) != 1:
                retained[j] = None
                continue
            if include_ramified_two and a % 2 == 0:
                assert b % 2 == 1 and value % 4 == 2
                entry[1].append((i, 2, 0))
                value //= 2
            values[j] = value
        for p, residues in prime_roots:
            for r in residues:
                for a, b in lattice_marks(p, r, height):
                    j = (a+height)*height + b - 1
                    value = values[j]
                    if not value:
                        continue
                    value //= p
                    odd = True
                    if value % p == 0:
                        if mark_local and polynomial(derivative, r, p) == 0:
                            values[j] = 0
                            retained[j] = None
                            continue
                        while value % p == 0:
                            value //= p
                            odd = not odd
                    values[j] = value
                    mark, small, large, smooth = retained[j]
                    if odd:
                        (small if p <= BASE else large).append((i, p, r))
                    if p > BASE and smooth:
                        retained[j] = mark, small, large, False
        for j, tail in enumerate(values):
            if tail <= 1:
                continue
            mark, small, large, _ = retained[j]
            if isqrt(tail)**2 != tail or (
                mark_local and gcd(tail, homogeneous(derivative, *mark)) != 1
            ):
                retained[j] = None
            else:
                retained[j] = mark, small, large, False
    return [entry for entry in retained if entry is not None]


def fixtures():
    for height in (1, 2, 5, 12):
        for p in GRID["primes_through"](2*height**2):
            for r in range(p):
                points = sorted((a, b) for a, b in lattice_marks(p, r, height) if gcd(a, b) == 1)
                expected = [(a, b) for a in range(-height, height + 1) for b in range(1, height + 1)
                            if gcd(a, b) == 1 and (a-r*b) % p == 0]
                assert points == expected, (height, p, r)

    # Force an accepted simple square tail, a rejected multiple square tail,
    # a rejected odd large valuation, and an admitted valuation-one multiple root.
    p = 8209
    for f, height, cutoff, expected in (
        ((2*p*p, p+1, -2, 1), 1, 2, ((0, 1), [(1, 2, 0), (2, 2, 0)], [], False)),
        ((2*p*p, 2*p, 2, 1), 1, 2, None),
        ((2*p*p, 2*p, 2, 1), 1, p, None),
        ((2*p**3, p+1, -2, 1), 1, 2, None),
        ((10, 10, 2, 1), 2, 8, ((0, 1), [(1, 2, 0), (1, 5, 0), (2, 2, 0), (2, 5, 0)], [], True)),
    ):
        m = 3
        g = f[:-1] + (1-m, 1)
        marks = compare(homogeneous(f, m, 1), m, (f, g), height, cutoff,
                        include_ramified_two=True, mark_local=True)[0]
        assert next((entry for entry in marks if entry[0] == (0, 1)), None) == expected
    m, f, g = GRID["CHECK_PAIR"](247, 3)
    for include_ramified_two in (False, True):
        for mark_local in (False, True):
            compare(247, m, (f, g), 16, 512,
                    include_ramified_two=include_ramified_two, mark_local=mark_local)


def compare(n, m, fields, height, cutoff, **options):
    left, right = map(list, fields)
    line, = gp(f"print(poldisc(Polrev({left}))*poldisc(Polrev({right})));\n")
    excluded = int(line)
    start = perf_counter()
    primes = tuple(GRID["primes_through"](cutoff))
    old = GRID["relations"](n, m, fields, excluded, primes, cutoff, True, height=height, **options)
    trial = perf_counter() - start
    start = perf_counter()
    new = collect(n, m, fields, excluded, cutoff, height=height, **options)
    sieve = perf_counter() - start
    assert old == new
    words = GRID["parity_words"]
    assert words([small + large for _, small, large, _ in old]) == words(
        [small + large for _, small, large, _ in new]
    )
    return new, trial, sieve


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, default=GRID["HEIGHT"])
    args = parser.parse_args()
    if args.height < 1:
        parser.error("height must be positive")
    fixtures()
    height = args.height
    cutoff = 2*height**2
    print("N, height, cutoff, columns, trial seconds, lattice seconds", flush=True)
    for n in GRID["INPUTS"]:
        m, f, g = GRID["CHECK_PAIR"](n, 3)
        marks, trial, sieve = compare(n, m, (f, g), height, cutoff)
        print(n, height, cutoff, len(marks), f"{trial:.3f}", f"{sieve:.3f}", flush=True)


if __name__ == "__main__":
    main()
