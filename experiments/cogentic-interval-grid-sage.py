"""Enclose the real-root matrix of the conservative schedule over whole grid cells."""

from sage.all import QQ, RealIntervalField


def certify_grid(log2_L):
    field = RealIntervalField(160)
    length = 2**log2_L
    z = field(length).log()
    scale = ((field(length) / z).log() / 3).exp()
    degree = int(scale.lower().floor())
    assert degree == scale.upper().floor()
    h = scale * z
    log2_width_inverse = 3 * h / field(2).log()
    width_exponent = int(log2_width_inverse.lower().ceil())
    assert width_exponent == log2_width_inverse.upper().ceil()
    width = field(2)**(-width_exponent)
    mark_offset = width * field(1, 2)
    baseline_offset = width * field(0, 1)
    # For K1=2^ceil(100H/log 2), this enclosure includes K1^(-19/20).
    log2_precision = 100 * h / field(2).log()
    assert 19 * log2_precision.lower().ceil() >= 40 * width_exponent
    root_offset = width**2 * field(-1, 1)
    roots = [QQ(j) / (4 * degree) for j in range(1, 2 * degree + 1)]
    baseline = [(field(QQ(3)/4 - r) + baseline_offset - root_offset).log() for r in roots]
    diagonal = []
    rows = [field(0) for _ in roots]
    cols = [field(0) for _ in roots]
    for i, center in enumerate(roots):
        for j, root in enumerate(roots):
            # Subtract rational centers before enclosing the tiny displacement.
            distance = abs(field(center - root) + mark_offset - root_offset)
            assert distance > 0
            entry = abs(distance.log() - baseline[j])
            if i == j:
                diagonal.append(entry.lower())
            else:
                rows[i] += field(entry.upper())
                cols[j] += field(entry.upper())
    # ||E||_2 <= sqrt(||E||_1 ||E||_infty) for the off-diagonal matrix.
    off = (field(max(r.upper() for r in rows)) * field(max(c.upper() for c in cols))).sqrt()
    gap = (field(min(diagonal)) - off) / h
    assert gap > 2
    return degree, (1000 * gap).lower().floor()


if __name__ == "__main__":
    for power in (14, 16, 18, 20, 24):
        degree, bound = certify_grid(power)
        print(f"log2(L)={power}, d={degree}, certified least singular value >= {bound}H/1000")
