#!/usr/bin/env python3
"""Exact rational enclosure of the short-width shared-table ledger."""

from fractions import Fraction as Q


def interval_product(*intervals):
    lo = hi = Q(1)
    for left, right in intervals:
        corners = lo * left, lo * right, hi * left, hi * right
        lo, hi = min(corners), max(corners)
    return lo, hi


def shared_lower_certificate(cost):
    assert Q(1, 3) < cost < Q(8, 3)

    def radius(u):
        return cost - Q(8, 27) / u**2 - 2 * u / 3

    def radius_derivative(u):
        return Q(16, 27) / u**3 - Q(2, 3)

    def residual(u, a):
        return 6 * a * (cost - a) - 3 * u**2 / 2

    # The proof bounds feasible u by [1/3,C] and a by (0,C/2].
    boxes = [(Q(1, 3), cost, Q(0), cost / 2, 0)]
    inspected = 0
    while boxes:
        ul, uh, al, ah, depth = boxes.pop()
        inspected += 1
        rhi = cost - Q(8, 27) / uh**2 - 2 * ul / 3
        rcap = min(cost / 2, rhi)
        if rcap <= 0 or al > rcap:
            continue
        ah = min(ah, rcap)
        lh = residual(ul, ah)
        if lh < 0 or lh**2 < 8 * cost * (1 + al / rcap):
            continue

        rlo = cost - Q(8, 27) / ul**2 - 2 * uh / 3
        um, am = (ul + uh) / 2, (al + ah) / 2
        if rlo > 0:
            # F uses the uncapped radius, which can only enlarge the surplus.
            # The componentwise derivative intervals bound F on this rectangle.
            lrange = residual(uh, al), lh
            fmid = residual(um, am)**2 - 8 * cost * (1 + am / radius(um))
            a1, a2 = interval_product((Q(12), Q(12)), lrange,
                                      (cost - 2 * ah, cost - 2 * al))
            da = a1 - 8 * cost / rlo, a2 - 8 * cost / rhi
            u1, u2 = interval_product((-6 * uh, -6 * ul), lrange)
            v1, v2 = interval_product((8 * cost * al, 8 * cost * ah),
                                      (radius_derivative(uh), radius_derivative(ul)),
                                      (1 / rhi**2, 1 / rlo**2))
            du = u1 + v1, u2 + v2
            upper = fmid + max(map(abs, da)) * (ah - al) / 2 + max(map(abs, du)) * (uh - ul) / 2
            if upper < 0:
                continue

        assert depth < 80, (ul, uh, al, ah)
        if uh - ul >= ah - al:
            boxes.extend([(ul, um, al, ah, depth + 1), (um, uh, al, ah, depth + 1)])
        else:
            boxes.extend([(ul, uh, al, am, depth + 1), (ul, uh, am, ah, depth + 1)])
    return inspected


def witness():
    cost, u, r, a, delta, v, y = map(Q, (
        "2.07255", ".6625787", ".9559124", ".909207", "1.372166", "1.036274", ".9092075",
    ))
    private = Q(8, 27) / u**2 + 2 * u / 3
    height = 1 / delta + 3 * u**2 / 4
    rational_loss = 1 / (3 * delta * r)
    algebraic_loss = (height + delta * v) / (3 * a)
    f = r - a
    columns = max(r, a + f)
    margins = {
        "private": cost - columns - private,
        "full scan": cost - 2 * v,
        "field tests": cost - (2 * v - rational_loss + f),
        "solve": cost - 2 * columns,
        "fixed algebraic tag": 2 * v - y - rational_loss - algebraic_loss,
        "full flexible supply": 2 * v - rational_loss - algebraic_loss + f - columns,
        "tag above cutoff": y - a,
    }
    assert f > 0 and all(margin > 0 for margin in margins.values())
    return margins


def rational_tag_witness():
    cost, u, a, r, delta, v, y = map(Q, ("1.9", ".823", ".913", ".428", "1.816", ".9495", ".429"))
    private = Q(8, 27) / u**2 + 2 * u / 3
    height = 1 / delta + 3 * u**2 / 4
    rational_loss = 1 / (3 * delta * r)
    algebraic_loss = (height + delta * v) / (3 * a)
    assert cost - a - private > Q(".00088") and cost - 2 * v == Q(".001")
    assert cost > max(2 * a, 2 * v - rational_loss) and y > r
    assert 2 * v - y - rational_loss - algebraic_loss > Q(".025")
    assert a + rational_loss + algebraic_loss - 2 * v > Q(".458")


if __name__ == "__main__":
    print("2.07254 infeasible, rectangles:", shared_lower_certificate(Q("2.07254")))
    print("2.07255 strict margins:")
    for name, margin in witness().items():
        print(f"  {name}: {float(margin):.10g}")
    rational_tag_witness()
    print("Separate rational-tag-only witness at 1.900 verified")
