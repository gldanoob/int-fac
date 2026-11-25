"""Check exact global biquadratic cover minima with the z3-solver package."""

from collections import defaultdict
from itertools import combinations, product
from pathlib import Path
from runpy import run_path
import z3

profiles = run_path(str(Path(__file__).with_name("cubic-resolvent-profiles.py")))

def check(height, branch, optimum):
    classes = profiles["box_classes"](height)
    anchor = frozenset((-1, 3))
    rows = [(tuple(sorted(d ^ anchor if 3 in d else d)), branch * int(3 in d)) for d in classes]
    coordinates = sorted(set().union(*(row for row, _ in rows)))
    signs = {p: z3.Bool(f"chi_{p}") for p in coordinates}
    active = {d: z3.Bool(f"active_{i}") for i, d in enumerate(classes)}
    solver = z3.SolverFor("QF_FD")
    for (scope, shift), enabled in zip(rows, active.values(), strict=True):
        negative = z3.BoolVal(bool(shift))
        for p in scope:
            negative = z3.Xor(negative, signs[p])
        solver.add(enabled == z3.Not(negative))
    indices = {d: i for i, d in enumerate(classes)}
    incident = defaultdict(list)
    triples = []
    for i, j in combinations(range(len(classes)), 2):
        k = indices.get(classes[i] ^ classes[j], -1)
        if k <= j or (branch and anchor in (classes[i], classes[j], classes[k])):
            continue
        chosen = z3.Bool(f"triangle_{len(triples)}")
        triples.append(chosen)
        for d in (classes[i], classes[j], classes[k]):
            solver.add(z3.Implies(chosen, active[d]))
            incident[d].append(chosen)
    for group in incident.values():
        if len(group) > 1:
            solver.add(z3.AtMost(*group, 1))

    # Replace each cost -chosen by (not chosen) minus one.
    cost = [(v, 1) for v in active.values()] + [(z3.Not(v), 1) for v in triples]
    counts = [(scope, {bits: int((sum(bits) + shift) % 2 == 0)
                       for bits in product((0, 1), repeat=len(scope))}) for scope, shift in rows]
    minimum, archive = profiles["eliminate"](counts, coordinates, profiles["merge_counts"])
    solver.add(z3.PbGe([(v, 1) for v in active.values()], sum(minimum)))
    solver.push()
    solver.add(z3.PbLe(cost, optimum - 1 + len(triples)))
    result = solver.check()
    if result != z3.unsat:
        raise RuntimeError(f"objective <= {optimum - 1}: expected unsat, got {result}")
    print(f"H={height} p mod 3={1 + branch} objective <= {optimum - 1}: UNSAT", flush=True)
    solver.pop()
    target = z3.PbLe(cost, optimum + len(triples))
    for assignment in profiles["optimal_profiles"](archive, {}):
        fixed = [signs[p] == bool(value) for p, value in assignment.items()]
        if solver.check(target, *fixed) == z3.sat:
            break
    else:
        if solver.check(target) != z3.sat:
            raise RuntimeError(f"objective <= {optimum} was not satisfiable")
    print(f"H={height} p mod 3={1 + branch} objective <= {optimum}: SAT, "
          f"minimum cover {(optimum + 1) // 2}", flush=True)


if __name__ == "__main__":
    for branch, optimum in ((1, 31), (0, 22)):
        check(5, branch, optimum)
