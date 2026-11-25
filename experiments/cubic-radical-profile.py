"""Optimize the limiting two-prime collision probability using certified Cardano rows."""
import ast
from array import array
from fractions import Fraction
from math import prod
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
squareclass = runpy.run_path(str(HERE / "cubic-resolvent-profiles.py"))["squareclass"]


def block_weights(height):
    run = f'iferr(read("experiments/cubic-radical-ranks.gp");print(cubicRadicalBox({height},1)),E,print(E);quit(1))\n'
    proc = subprocess.run(["gp", "-s", "256M", "--default", "threadsize=128M", "-fq"], cwd=HERE.parent, input=run,
                          capture_output=True, text=True, check=True)
    assert not proc.stderr, proc.stderr
    *rows, summary = map(ast.literal_eval, proc.stdout.splitlines())
    return {d: Fraction(p, q) for d, m, r, p, q in rows}, summary


def projection(scope, remaining):
    # Tabulate addresses with the eliminated sign zero. Its one-bit offset is added later.
    positions = {v: 1 << j for j, v in enumerate(scope)}
    indices = array("I", [0])
    for v in remaining:
        bit = positions.get(v, 0)
        indices += array("I", (i + bit for i in indices))
    return indices


class Profile:
    def __init__(self, weights, conditioned=()):
        self.discs = list(weights)
        self.weights = list(weights.values())
        self.classes = [squareclass(d) for d in self.discs]
        self.conditioned = tuple(conditioned)
        self.fixed_masks = []
        self.scopes = []
        for s in self.classes:
            s = set(s)
            if 3 in s:
                s.remove(3)
                s.symmetric_difference_update([-1])
            self.fixed_masks.append(sum(1 << j for j, v in enumerate(self.conditioned) if v in s))
            self.scopes.append(tuple(sorted(s.difference(self.conditioned))))
        variables = set().union(*self.scopes)
        live = dict(enumerate(self.scopes))
        self.steps = []
        while variables:
            neighbors = {v: set() for v in variables}
            for scope in live.values():
                for v in scope:
                    neighbors[v].update(scope)
            v = min(variables, key=lambda x: (len(neighbors[x]), x))
            outer = sorted(neighbors[v] - {v})
            incident = [i for i, scope in live.items() if v in scope]
            args = []
            for i in incident:
                scope = live.pop(i)
                args.append((i, projection(scope, outer), 1 << scope.index(v)))
            live[len(self.discs) + len(self.steps)] = tuple(outer)
            self.steps.append((v, outer, args))
            variables.remove(v)
        self.final = list(live)
        self.denominator = prod(w.denominator for w in self.weights)

    def optimize(self, branch, forced=frozenset()):
        candidates = (self._optimize(branch, forced, signs)
                      for signs in range(1 << len(self.conditioned)))
        return max(candidates, key=lambda entry: entry[0])

    def _optimize(self, branch, forced, fixed_signs):
        offsets = [(branch * (3 in s) + (mask & fixed_signs).bit_count()) % 2
                   for s, mask in zip(self.classes, self.fixed_masks)]
        tables = []
        for s, scope, weight, off in zip(self.classes, self.scopes, self.weights, offsets):
            split, inert = weight.numerator, weight.denominator
            if s in forced:
                split, inert = weight.denominator, 0
            tables.append([inert if (j.bit_count() + off) % 2 else split
                           for j in range(1 << len(scope))])
        archive = []
        for v, outer, args in self.steps:
            size = 1 << len(outer)
            low, high = [1] * size, [1] * size
            for i, indices, offset in args:
                table = tables[i]
                for j, k in enumerate(indices):
                    low[j] *= table[k]
                    high[j] *= table[k + offset]
                tables[i] = None
            picks = bytearray(y > x for x, y in zip(low, high))
            tables.append([max(x,y) for x,y in zip(low,high)])
            archive.append(picks)
        ans = Fraction(prod(tables[i][0] for i in self.final), self.denominator)
        signs = {}
        for (v, outer, _), picks in reversed(list(zip(self.steps,archive))):
            signs[v] = picks[sum(signs[u] << j for j,u in enumerate(outer))]
        active = [i for i,(scope,off) in enumerate(zip(self.scopes,offsets))
                  if (sum(signs[u] for u in scope) + off) % 2 == 0]
        if ans:
            assert forced.intersection(self.classes) <= {self.classes[i] for i in active}
            assert ans == prod(self.weights[i] for i in active if self.classes[i] not in forced)
        return ans, [self.discs[i] for i in active]


def span(basis):
    members = {frozenset()}
    for s in basis:
        members |= {a ^ s for a in members}
    return frozenset(members)


def best_bases(model, branch, dimension):
    original, active = model.optimize(branch)
    coordinates = {p: 1 << j for j, p in enumerate(sorted({-1,3}.union(*model.classes)))}
    masks = [sum(coordinates[p] for p in s) for s in model.classes]
    by_mask = dict(zip(masks,model.classes))
    weights = dict(zip(masks,model.weights))
    labels = dict(zip(masks,model.discs))
    forbidden = coordinates[-1] ^ coordinates[3] if branch else 0

    # Integer upper bounds for 256 times each log2 gain and a lower bound for the incumbent.
    def log_floor_bound(q):
        return (q.numerator**256).bit_length() - (q.denominator**256).bit_length() - 1

    upper = {m: log_floor_bound(1/w) + 2 for m,w in weights.items()}
    ordered = sorted(masks,key=lambda m: (-upper[m],weights[m],labels[m]))
    position = {m: i for i,m in enumerate(ordered)}
    active_masks = {m for m,d in labels.items() if d in active}
    basis, members = [], {0}
    for _ in range(dimension):
        candidates = active_masks - members
        if not candidates:
            break
        def score(m):
            return prod(weights.get(m ^ s,1) for s in members)
        v = min(candidates, key=lambda m: (score(m),labels[m]))
        basis.append(v)
        members |= {v ^ s for s in members}
    best = original / prod(weights.get(m,1) for m in members)
    witness = tuple(basis)
    limit = log_floor_bound(best/original)
    tested = 0

    def visit(next_i, members, basis, paid):
        nonlocal best, witness, limit, tested
        capacity = (1 << dimension) - len(members)
        for i in range(next_i,len(ordered)):
            v = ordered[i]
            if paid + capacity*upper[v] < limit:
                break
            if v in members:
                continue
            extra = [v ^ s for s in members]
            if forbidden and forbidden in extra:
                continue
            # The first eligible independent column fixes a canonical basis for this span.
            if any(position.get(m,i) < i for m in extra):
                continue
            new_paid = paid + sum(upper.get(m,0) for m in extra)
            new_members = members.union(extra)
            if new_paid >= limit:
                bound = original / prod(weights[m] for m in new_members if m in weights)
                if bound > best:
                    forced = {by_mask[m] for m in new_members if m in by_mask}
                    candidate, _ = model.optimize(branch,forced)
                    tested += 1
                    if candidate > best:
                        best, witness, limit = candidate, basis+(v,), log_floor_bound(candidate/original)
            if len(basis) + 1 < dimension:
                visit(i+1,new_members,basis+(v,),new_paid)

    visit(0,{0},(),0)
    assert model.optimize(branch,span([by_mask[v] for v in witness]))[0] == best
    return best, [labels[s] for s in witness], tested


if __name__ == "__main__":
    h = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    max_degree = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    weights, summary = block_weights(h)
    # Keeping the most connected signs outside the tables bounds memory at height 12.
    model = Profile(weights, (-1, 2, 5, 7, 11) if h >= 12 else ())
    print("height, cubic fields, resolvents incl. cyclic block, cyclic rank, total rank, relations, last witness prime", summary[:7], flush=True)
    for branch in (0,1):
        main, active = model.optimize(branch)
        print("branch mod 3, active resolvents, maximum", branch+1, len(active), main, flush=True)
        if h == 6:
            check = HERE.parent / "research/2026-11-25-handoff/height-six" / f"collision-prob-{branch}.txt"
            assert main == Fraction(check.read_text().strip())
        for dim in range(1,max_degree+1):
            score, basis, tested = best_bases(model,branch,dim)
            print("dimension, best, basis, additional optimizations", dim, score, basis, tested, flush=True)
