"""Replay bounded large-prime recombination on the seven monic holdouts."""

import os
import subprocess
from ast import literal_eval
from collections import defaultdict, deque
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


INPUTS = (187, 209, 247, 299, 391, 437, 10403)
BASE = 151
LARGE_BOUND = BASE**2
HEIGHT = 64
CHECK_PAIR = run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))["check_pair"]


def primes_through(limit):
    sieve = bytearray(b"\1") * (limit + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, limit + 1):
        if sieve[p]:
            yield p
            if p * p <= limit:
                size = (limit - p * p) // p + 1
                sieve[p * p::p] = b"\0" * size


def factor_bounded(value, primes, cutoff, allow_square_tail=False):
    residue = abs(value)
    factors = []
    for p in primes:
        if p * p > residue:
            break
        if residue % p == 0:
            e = 0
            while residue % p == 0:
                residue //= p
                e += 1
            factors.append((p, e))
    if 1 < residue <= cutoff:
        factors.append((residue, 1))
        residue = 1
    if residue != 1 and (not allow_square_tail or isqrt(residue)**2 != residue):
        return None
    assert residue * prod(p**e for p, e in factors) == abs(value)
    return factors


def polynomial(values, x, mod):
    result = 0
    for coeff in reversed(values):
        result = (result * x + coeff) % mod
    return result


def homogeneous(values, a, b):
    return sum(c * a**j * b**(len(values)-1-j) for j, c in enumerate(values))


def relations(n, m, fields, excluded, primes, cutoff, complete_parity=False, *,
              height=HEIGHT, include_ramified_two=False, mark_local=False):
    """Collect parity columns using the ordered primes through cutoff."""
    if include_ramified_two:
        if not excluded or any(
            len(coeffs) < 3 or coeffs[-1] != 1 or coeffs[0] % 4 != 2
            or any(c % 2 for c in coeffs[:-1])
            for coeffs in fields
        ):
            raise ValueError("the ramified row requires a nonzero discriminant product and polynomials Eisenstein at two")
        while excluded % 2 == 0:
            excluded //= 2
    if mark_local:
        excluded = gcd(excluded, 2)
    polynomials = [(coeffs, tuple(j*c for j, c in enumerate(coeffs) if j)) for coeffs in fields]
    retained = []
    for a in range(-height, height + 1):
        for b in range(1, height + 1):
            if gcd(a, b) != 1 or gcd(a - b*m, n) != 1:
                continue
            small, large, smooth = [], [], True
            for i, (coeffs, derivative) in enumerate(polynomials, 1):
                value = homogeneous(coeffs, a, b)
                if value == 0 or gcd(value, excluded) != 1:
                    break
                if include_ramified_two and a % 2 == 0:
                    assert b % 2 == 1 and value % 4 == 2
                    small.append((i, 2, 0))
                    value //= 2
                factors = factor_bounded(value, primes, cutoff, complete_parity)
                if factors is None:
                    break
                tail = abs(value) // prod(p**e for p, e in factors)
                if mark_local:
                    local_derivative = homogeneous(derivative, a, b)
                    if gcd(tail, local_derivative) != 1 or any(
                        e > 1 and local_derivative % p == 0 for p, e in factors
                    ):
                        break
                if tail != 1:
                    smooth = False
                for p, e in factors:
                    root = a * pow(b, -1, p) % p
                    assert polynomial(coeffs, root, p) == 0
                    if not mark_local:
                        assert polynomial(derivative, root, p) != 0
                    if p > BASE:
                        smooth = False
                    if e % 2:
                        (small if p <= BASE else large).append((i, p, root))
            else:
                if complete_parity or len(large) <= 2:
                    retained.append(((a, b), small, large, smooth))
    return retained


def parity_words(columns):
    rows = {key: i for i, key in enumerate(sorted({key for column in columns for key in column}))}
    return [sum(1 << rows[key] for key in column) for column in columns]


def eliminate(columns, combinations):
    pivots, kernel = {}, []
    for word, mask in zip(columns, combinations, strict=True):
        while word and (pivot := word.bit_length()) in pivots:
            old_word, old_mask = pivots[pivot]
            word ^= old_word
            mask ^= old_mask
        if word:
            pivots[word.bit_length()] = (word, mask)
        else:
            kernel.append(mask)
    return kernel


def core_indices(columns):
    """Keep the indices of columns left after eliminating singleton rows."""
    rows = defaultdict(set)
    for j, column in enumerate(columns):
        for key in column:
            rows[key].add(j)
    pending = deque(key for key, hits in rows.items() if len(hits) == 1)
    alive = bytearray(b"\1") * len(columns)
    while pending:
        hits = rows[pending.popleft()]
        if len(hits) == 1:
            j, = hits
            alive[j] = 0
            for key in columns[j]:
                rows[key].remove(j)
                if len(rows[key]) == 1:
                    pending.append(key)
    return [j for j, keep in enumerate(alive) if keep]


def parity_basis(columns):
    """Return surviving indices and their compact kernel basis for distinct row keys."""
    core = core_indices(columns)
    words = parity_words([columns[j] for j in core])
    basis = eliminate(words, (1 << j for j in range(len(core))))
    assert all(combine(word, words) == 0 for word in basis)
    return core, basis


def support(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def combine(word, columns):
    result = 0
    for i in support(word):
        result ^= columns[i]
    return result


def cycle_basis(columns):
    forest = defaultdict(list)
    parent = {}
    sentinel = (0, 0, 0)

    def root(vertex):
        while parent[vertex] != vertex:
            vertex = parent[vertex]
        return vertex

    cycles = []
    for i, keys in enumerate(columns):
        endpoints = keys + [sentinel] * (2 - len(keys))
        left, right = endpoints
        parent.setdefault(left, left)
        parent.setdefault(right, right)
        left_root, right_root = root(left), root(right)
        edge = 1 << i
        if left_root != right_root:
            parent[left_root] = right_root
            forest[left].append((right, edge))
            forest[right].append((left, edge))
            continue
        todo = [(left, None, edge)]
        while todo:
            vertex, previous, path = todo.pop()
            if vertex == right:
                cycles.append(path)
                break
            todo.extend((adj, vertex, path ^ old_edge) for adj, old_edge in forest[vertex]
                        if adj != previous)
        else:
            raise AssertionError("missing forest path")
    return cycles


def gp(code, timeout=30):
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input=code,
                            cwd=Path(__file__).resolve().parent, capture_output=True, text=True,
                            timeout=timeout, check=True)
    if result.stderr:
        raise RuntimeError(result.stderr)
    return result.stdout.splitlines()


def square_checks(n, m, fields, supports):
    code = r'''
cogentic_as_library=1;
read("cogentic-quadratic-order.gp");
read("cogentic-monic-pair-relations.gp");
read("cogentic-monic-pair-squares.gp");
monic_large_square(n,m,coefficients,tests,limit) = {
  my(fields=apply(Polrev,coefficients), orders=apply(nfinit,fields));
  my(excluded=poldisc(fields[1])*poldisc(fields[2]), primeset=primes([2,limit]));
  for(k=1,#tests,
    my(points=tests[k]);
    for(i=1,2,for(j=1,#points,
      my(a=points[j][1], b=points[j][2]);
      monic_check_ideals(orders[i],a,b,monic_norm_data(fields[i],a,b,excluded,primeset));
    ));
    my(products=vector(2,i,prod(j=1,#points,Mod(points[j][1]-points[j][2]*x,fields[i]))));
    my(results=vector(2,s,vector(2,i,monic_square_root(n,m,orders[i],(2*s-3)*products[i]))));
    print([apply(f->apply(r->r[1],f),results),results]);
  );
};
'''
    args = (n, m, [list(coeffs) for coeffs in fields], supports, LARGE_BOUND)
    code += "iferr(monic_large_square(" + ",".join(map(str, args)) + "),err,print(err);quit(1));\n"
    return [literal_eval(line) for line in gp(code)]


def main():
    pairs = [CHECK_PAIR(n, 3) for n in INPUTS]
    discs = gp("\n".join(f"print(poldisc(Polrev({list(f)}))*poldisc(Polrev({list(g)})));"
                         for _, f, g in pairs) + "\n")
    primes = tuple(primes_through(LARGE_BOUND))
    outside = next(p for p in primes_through(2 * LARGE_BOUND) if p > LARGE_BOUND)
    assert factor_bounded(outside**2, primes, LARGE_BOUND) is None
    assert factor_bounded(17 * outside**2, primes, LARGE_BOUND, True) == [(17, 1)]
    assert factor_bounded(17 * outside**3, primes, LARGE_BOUND, True) is None
    assert factor_bounded(2**3 * 173**2 * 179, primes, LARGE_BOUND) == [(2, 3), (173, 2), (179, 1)]
    sample = [(1, 157, 0), (1, 157, 1), (2, 157, 0)]
    graph = [[], sample[:1], sample[:2], sample[1:2], sample[:1], sample[2:]]
    assert cycle_basis(graph) == [1, 14, 18]
    certificates = []
    parity_cutoff = max(BASE, 2 * HEIGHT**2)
    parity_primes = tuple(primes_through(parity_cutoff))
    print("N, full columns, full nullity, retained columns, leaf columns, cycle dimension,"
          " multi-edge cycles, total nullity, square-tail columns, square-tail nullity")
    for n, (m, f, g), excluded in zip(INPUTS, pairs, map(int, discs), strict=True):
        marks = relations(n, m, (f, g), excluded, primes, LARGE_BOUND)
        small = parity_words([entry[1] for entry in marks])
        large = parity_words([entry[2] for entry in marks])
        words = [1 << i for i in range(len(marks))]
        cycles = cycle_basis([entry[2] for entry in marks])
        leaf_columns = sum(words[i] for i, entry in enumerate(marks)
                           if any(p > 2 * HEIGHT**2 for _, p, _ in entry[2]))
        assert all(mask & leaf_columns == 0 for mask in cycles)
        assert all(combine(mask, large) == 0 for mask in cycles)
        assert len(cycles) == len(eliminate(large, words))
        kernel = eliminate([combine(mask, small) for mask in cycles], cycles)
        offset = max(map(int.bit_length, small), default=0)
        direct = eliminate([s | (l << offset) for s, l in zip(small, large)], words)
        assert len(kernel) == len(direct)
        assert all(combine(mask, small) == combine(mask, large) == 0 for mask in kernel)
        full = [i for i, entry in enumerate(marks) if entry[3]]
        baseline = eliminate([small[i] for i in full], [words[i] for i in full])
        assert not baseline
        multi_edge = sum(mask.bit_count() > 1 for mask in cycles)
        all_marks = relations(n, m, (f, g), excluded, parity_primes, parity_cutoff, True)
        all_parities = parity_words([small_keys + large_keys for _, small_keys, large_keys, _ in all_marks])
        all_kernel = eliminate(all_parities, (1 << i for i in range(len(all_marks))))
        assert len(all_kernel) == len(kernel)
        print(n, len(full), len(baseline), len(marks), leaf_columns.bit_count(),
              len(cycles), multi_edge, len(kernel), len(all_marks), len(all_kernel))
        masks = [combine(i, kernel) for i in range(1, min(1023, (1 << len(kernel)) - 1) + 1)]
        points = [[list(marks[j][0]) for j in support(mask)] for mask in masks]
        results = square_checks(n, m, (f, g), points) if points else []
        for mask, selected, (statuses, roots) in zip(masks, points, results, strict=True):
            common = prod(a-b*m for a, b in selected) % n
            for sign, signs, pair in zip((-1, 1), statuses, roots, strict=True):
                if all(status >= 2 for status in signs):
                    left, right = (root[1] for root in pair)
                    assert left**2 % n == right**2 % n == sign*common % n
                    divisor = gcd(left-right, n)
                    if 1 < divisor < n:
                        assert n % divisor == 0
                        assert all(not marks[j][2] for j in support(mask))
                        certificates.append((n, selected, sign, min(divisor, n // divisor)))
                        print(f"{n} split by {selected}, sign {sign}, residues {left} and {right}, gcd {divisor}")
    assert certificates == [(247, [[-31, 3], [-1, 1]], -1, 13)]


if __name__ == "__main__":
    main()
