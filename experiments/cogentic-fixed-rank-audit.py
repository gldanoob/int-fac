"""Replay the retuned Gram proof's norm identity, grid gap and peeling inequalities."""

from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from math import exp, fsum, log, log1p, sqrt
from random import Random


def squarefree_factors(n):
    factors = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return None
            factors.append(p)
        p += 1
    if n > 1:
        factors.append(n)
    return factors


def check_norm_coordinates():
    # The two irreducible real quadratics have actual field norms of a-theta.
    # This check uses their complete squarefree factor rows at the selected marks.
    with localcontext() as context:
        context.prec = 85
        scale = D(160)
        log_x = 2 * scale.ln()
        root2 = D(2).sqrt()
        polys = [(1, -1), (3, 1)]  # X² - tX + c
        data = []
        for a in range(2, 150):
            record = []
            for t, c in polys:
                factors = squarefree_factors(abs(a*a-t*a+c))
                if factors is None:
                    break
                delta = D(t*t-4*c).sqrt()
                roots = ((D(t)-delta)/2, (D(t)+delta)/2)
                logs = [((D(a)-theta)/scale).copy_abs().ln() for theta in roots]
                assert abs(sum(D(p).ln() for p in factors) - log_x - sum(logs)) < D('1e-75')
                record.append(([(p, a % p) for p in factors], logs))
            if len(record) == len(polys):
                data.append(record)
        rows = [sorted({r for rec in data for r in rec[i][0]}) for i in (0, 1)]
        primes = {p for group in rows for p, r in group}
        z = {p: (D(p).ln()*D(15)/32).exp() for p in primes}
        w = {p: D(p).ln()/z[p] for p in primes}
        rng = Random(421)
        dots = 0
        for _ in range(18):
            v0 = D(rng.randrange(-10, 11))
            v_f = [{r: D(rng.randrange(-10, 11)) for r in group} for group in rows]
            v_u = [D(rng.randrange(-10, 11)) for _ in rows]
            t = [-sum(w[p]*v_f[i][(p,r)] for p,r in group)/sum(w[p]**2 for p,r in group)
                 for i, group in enumerate(rows)]
            z0 = v0 - sum(t)*log_x
            z_f = [{(p,r): v_f[i][(p,r)]+t[i]*w[p] for p,r in group} for i,group in enumerate(rows)]
            z_a = [(u/root2 - h, -u/root2 - h) for u,h in zip(v_u,t)]
            for i, group in enumerate(rows):
                assert abs(sum(w[p]*z_f[i][(p,r)] for p,r in group)) < D('1e-75')
                assert abs(sum(v*v for v in z_a[i]) - v_u[i]**2 - 2*t[i]**2) < D('1e-75')
            for rec in data:
                original, transformed = v0, z0
                for i, (factors, logs) in enumerate(rec):
                    original += sum(v_f[i][(p,r)]*z[p] for p,r in factors) + v_u[i]*(logs[0]-logs[1])/root2
                    transformed += sum(z_f[i][(p,r)]*z[p] for p,r in factors) + sum(u*l for u,l in zip(z_a[i],logs))
                assert abs(original-transformed) < D('1e-74')
                dots += 1
        return len(data), dots


def check_grid():
    ratios = []
    for d in (4, 8, 12, 24, 36, 64, 96, 128):
        z = 4*log(d)
        for _ in range(15):
            z -= (z-log(z)-3*log(d))/(1-1/z)
        h = d*z
        logw = -3*h
        w = exp(logw)
        roots = [(j+1)/(4*d) for j in range(2*d)]
        grid_points = (0, .25, .5, .75, 1)
        matrix = []
        for i, center in enumerate(roots):
            row = []
            for j, root in enumerate(roots):
                base = fsum(log(.75-root)+log1p(w*s/(.75-root)) for s in grid_points)/len(grid_points)
                if i == j:
                    avg = logw + fsum(log1p(s) for s in grid_points)/len(grid_points)
                else:
                    avg = fsum(log(abs(center-root))+log1p(w*(1+s)/(center-root)) for s in grid_points)/len(grid_points)
                row.append(avg-base)
            matrix.append(row)
        row_bound = max(fsum(abs(v) for j,v in enumerate(row) if i != j) for i,row in enumerate(matrix))
        col_bound = max(fsum(abs(row[j]) for i,row in enumerate(matrix) if i != j) for j in range(2*d))
        gap = min(abs(row[i]) for i,row in enumerate(matrix))-sqrt(row_bound*col_bound)
        assert gap > 2*h
        ratios.append(gap/h)
    return len(ratios), min(ratios)


def check_peeling():
    rng = Random(1013)
    stages = scalar = induced = sparse_bounds = 0
    for repeat in range(18):
        rows = [(p, r) for p in (11, 13, 17, 19, 23, 29, 31, 37) for r in (0, 1)]
        weights = [1+rng.randrange(4)+(repeat+2 if a % 37 == 0 else 0) for a in range(440)]
        total = sum(weights)
        marks = [{a for a in range(len(weights)) if a % p == r} for p,r in rows]
        mass = lambda subset: F(sum(weights[a] for a in subset), total)
        mu = [F(1,p) for p,r in rows]
        # Aij/sqrt(pi*pj) is the empirical covariance error with model means 1/pi,1/pj.
        error = [[mass(marks[i] & marks[j]) - mu[i]*mu[j] for j in range(len(rows))] for i in range(len(rows))]
        deleted = {len(rows)-2}
        delta = F(4+repeat % 5, 100)
        while True:
            removed = set.union(*(marks[i] for i in deleted))
            mu_d = sum(mu[j] for j in deleted)
            losses = {i: rows[i][0]*mass(marks[i] & removed) for i in range(len(rows)) if i not in deleted}
            for i, loss in losses.items():
                p = rows[i][0]
                cross = sum(p*rows[j][0]*error[i][j]**2 for j in deleted if p != rows[j][0])
                assert max(0, loss-2*mu_d)**2 <= mu_d*p*cross
                scalar += 1
            added = {i for i, loss in losses.items() if loss > delta}
            if not added:
                survivors = list(losses)
                b = {i: rng.randrange(-5, 6) for i in survivors}
                degree = max(sum(a in marks[i] for i in survivors) for a in range(len(weights)))
                left = F(sum(weights[a]*sum(b[i] for i in survivors if a in marks[i])**2 for a in removed), total)
                assert left <= degree*delta*sum(mu[i]*b[i]**2 for i in survivors)
                sparse_bounds += 1
                break
            mu_s = sum(mu[i] for i in added)
            weighted = sum(mu[i]*max(0, losses[i]-2*mu_d) for i in added)
            frob = sum(rows[i][0]*rows[j][0]*error[i][j]**2 for i in added for j in deleted if rows[i][0] != rows[j][0])
            assert weighted**2 <= mu_s*mu_d*frob
            induced += 1
            deleted |= added
            stages += 1
    return stages, scalar, induced, sparse_bounds


if __name__ == '__main__':
    print('squarefree marks and norm-direction identities:', *check_norm_coordinates())
    print('archimedean grids and minimum certified gap/H:', *check_grid())
    print('deletion stages, row inequalities, aggregate inequalities, sparse energy bounds:', *check_peeling())
