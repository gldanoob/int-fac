"""Compare bounded exact ideal parity with the inexpensive mark-local test."""

from ast import literal_eval
from collections import defaultdict
from functools import reduce
from math import gcd, prod
from operator import or_
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
REPAIR = run_path(str(HERE / "cogentic-monic-index.py"))["repair"]
PLANT = run_path(str(HERE / "cogentic-planted-norm-two.py"))["monic_plants"]
NEW_SQUARE = [(-18, 1), (-18, 11), (-14, 3), (-13, 5), (-5, 3), (-3, 1), (-3, 7), (-3, 16),
              (-2, 1), (5, 4), (6, 1), (9, 5), (11, 8), (13, 9), (18, 1)]


def reference(expression):
    code = 'read("cogentic-all-ideal-reference.gp");\n'
    code += f"iferr(print({expression}),err,print(err);quit(1));\n"
    line, = GRID["gp"](code, timeout=30)
    return literal_eval(line)


def kernel(columns, positions):
    return GRID["eliminate"](GRID["parity_words"](columns), (1 << k for k in positions))


def compare(family, n, m, fields, height):
    bound = 2*height**2
    coeffs = [list(p) for p in fields]
    marks = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
             if gcd(a, b) == 1 and gcd(a-b*m, n) == 1]
    labels, parts, even = reference(f"all_ideal_reference({coeffs},{[list(mark) for mark in marks]},{bound})")
    indices = {mark: k for k, mark in enumerate(marks)}
    root_labels = defaultdict(list)
    for i, p, j, root, _, _ in labels:
        if root >= 0:
            root_labels[i, p, root].append((i, p, j))
    columns = [list(map(tuple, part)) for part in parts]
    keep = {k for k, parity in enumerate(even) if all(parity)}
    exact_kernel = kernel([column for k, column in enumerate(columns) if k in keep], sorted(keep))
    full_columns = [column if k in keep else column + [(len(fields)+1, k, 0)]
                    for k, column in enumerate(columns)]
    assert exact_kernel == kernel(full_columns, range(len(marks)))

    line, = GRID["gp"](f"print(prod(i=1,2,poldisc(Polrev({coeffs}[i]))));\n")
    prime_list = tuple(GRID["primes_through"](bound))
    cheap = GRID["relations"](n, m, fields, int(line), prime_list, bound, complete_parity=True,
                             height=height, include_ramified_two=True, mark_local=True)
    cheap_positions = [indices[mark] for mark, _, _, _ in cheap]
    for k, (_, small, large, _) in zip(cheap_positions, cheap, strict=True):
        assert k in keep
        translated = []
        for row in small + large:
            label, = root_labels[row]
            translated.append(label)
        assert sorted(translated) == sorted(columns[k])
    cheap_kernel = kernel([columns[k] for k in cheap_positions], cheap_positions)
    cheap_mask = sum(1 << k for k in cheap_positions)
    gained = len(keep)-len(cheap)
    exact_support = reduce(or_, exact_kernel, 0)
    active = (exact_support & ~cheap_mask).bit_count()
    assert len(exact_kernel) >= len(cheap_kernel)
    print(family, n, height, len(marks), len(cheap), len(cheap_kernel), len(keep), len(exact_kernel),
          gained, active, flush=True)
    return {marks[k] for k in keep}, marks, exact_kernel, even, len(cheap_kernel), active


def check_split(n, m, fields, marks, basis, points, sign, least_factor):
    mask = sum(1 << marks.index(mark) for mark in points)
    assert len(GRID["eliminate"]([*basis, mask], (1 << i for i in range(len(basis)+1)))) == 1
    coeffs, points = [list(p) for p in fields], [list(mark) for mark in points]
    call = f"kernel_roots({n},{m},apply(Polrev,{coeffs}),{points},{sign})"
    code = 'read("cogentic-monic-kernel-driver.gp");\n'
    line, = GRID["gp"](code + f"iferr(print({call}),err,print(err);quit(1));\n")
    left, right = literal_eval(line)
    common = sign*prod(a-b*m for a, b in points) % n
    assert gcd(common, n) == 1 and left**2 % n == right**2 % n == common
    divisor = gcd(left-right, n)
    assert min(divisor, n//divisor) == least_factor
    print(f"split {n} with {len(points)} marks, sign {sign}, residues {left} and {right}, gcd {divisor}", flush=True)


def weight_controls():
    for t in range(3):
        q = (11*19**2)**(2**t)
        report = reference(f"all_ideal_private_control({[q*q,0,1]},0,1,8)")
        assert report == [[11, [2**t], 4, 2 if t == 0 else 4], [19, [2**(t+1)], 4, 4]]

    for t in (1, 2):
        s = (13*19**2)**t
        f, m = (2*s*s, 2*s, 2, 1), 3
        g = f[:-1] + (1-m, 1)
        n = GRID["homogeneous"](f, m, 1)
        keep, marks, _, even, _, _ = compare(f"mixed-{t}", n, m, (f, g), 2)
        assert ((0, 1) in keep) == (t == 2) and even[marks.index((0, 1))] == [t-1, t-1]
        for p in (f, g):
            reports = reference(f"all_ideal_private_control({list(p)},0,1,8)")
            weight = 2*(len(p)-1)
            assert reports == [[13, [t, t], weight, weight-2 if t == 1 else weight],
                               [19, [2*t, 2*t], weight, weight]]


def run():
    print("family N height eligible cheap cheap-nullity exact exact-nullity recovered active", flush=True)
    for n, height in ((143, 16), (247, 32), (323, 16)):
        m, f, g = GRID["CHECK_PAIR"](n, 3)
        _, marks, basis, _, _, _ = compare("raw", n, m, (f, g), height)
        if n == 247:
            check_split(n, m, (f, g), marks, basis, [(-31, 3), (-1, 1)], -1, 13)
    m, f, g = GRID["CHECK_PAIR"](895, 2)
    _, marks, basis, _, cheap_nullity, active = compare("raw", 895, m, (f, g), 20)
    assert cheap_nullity == 0 and len(basis) == 7 and active == 36
    labels, [column], [flags] = reference(f"all_ideal_reference({[list(f),list(g)]},[[-3,1]],8)")
    odd_fives = [label for label in labels if label[:3] in column and label[:2] == [2, 5]]
    assert flags == [1, 1] and len(odd_fives) == 2 and all(label[3:] == [2, 1, 1] for label in odd_fives)
    check_split(895, m, (f, g), marks, basis, NEW_SQUARE, -1, 5)
    search = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))["search"]
    result = search(895, 2, 20, 128, False, True, all_ideals=True)
    assert (result["columns"], result["parity"], result["basis"]) == (151, 7, 5)
    assert {min(case["divisor"], case["cofactor"]) for case in result["factors"]} == {5}
    for n, height in ((145, 16), (67, 20)):
        m, f, g = GRID["CHECK_PAIR"](n, 2)
        shift, fields = REPAIR(n, m, f, g)
        assert shift == 1
        _, _, basis, _, cheap_nullity, active = compare("repaired", n, m, fields, height)
        if n == 67:
            assert cheap_nullity == 2 and len(basis) == 27 and active == 29
            decision = search(n, 2, height, None, False, True, all_ideals=True)
            assert decision["status"] == "basis-exhausted" and decision["basis"] == 25
            assert decision["basis"] == decision["survivors"] and not decision["factors"]
    for n, degree in ((85, 4), (631, 4), (15629, 6)):
        m, _, f, g = PLANT(n, degree)
        compare("planted", n, m, (f, g), 16)
    weight_controls()


if __name__ == "__main__":
    run()
