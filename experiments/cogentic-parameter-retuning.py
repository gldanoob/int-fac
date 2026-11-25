"""Exact scale comparisons for the schedule on pages 38--56 of the pinned paper."""

from fractions import Fraction as F
from math import factorial


def check_schedule():
    degree, base, precision = F(".30"), F(".36"), F(".35")
    evaluation, perturbation = F(".42"), F(".72")
    interval_width, brun_depth, brun_prime = F(".31"), F(".06"), F(".36")
    damping, zero_width = F(".355"), F(".355")
    field_base = 1 - degree
    smooth_u = perturbation - base
    distortion = field_base - base
    medium_count, high_count = base - zero_width, field_base - zero_width
    projection_norm = perturbation + base
    checks = {}

    def record(label, statement):
        assert statement, label
        checks[label] = 1

    # Positive series for log(2) using atanh(1/3).
    terms = 8
    log2_lower = sum(2 * F(1, 3)**(2*k+1)/(2*k+1) for k in range(terms))
    log2_upper = log2_lower + 2*F(1, 3)**(2*terms+1)/((2*terms+1)*(1-F(1, 9)))
    record("rational log(2) brackets", F(".69314") < log2_lower < log2_upper < F(".69315"))
    record("base m", field_base == F(".70"))
    record("leading coefficient logarithm", degree + evaluation == perturbation and 1000 > 4)
    record("degree and smoothing exponents below input size", perturbation < F(".76") < 1)
    record("perturbations dominate the base", perturbation > field_base)
    record("polynomial heights and guard", max(evaluation, degree, precision, base) < field_base)
    record("coefficient perturbation small and roots separated", precision > interval_width > degree)
    record("sieve truncation tied exponent", brun_depth + brun_prime == evaluation)
    record("sieve truncation coefficient", 4 * log2_lower > 2)
    record("sieve exponent absorbs other costs", evaluation > max(brun_prime, base, interval_width, F(".10")))
    record("pure Brun error", brun_prime > brun_depth)
    record("saddle exponent", smooth_u == F(".36"))
    record("character damping", smooth_u > damping > precision)
    record("all conductor loss absorbed", damping > distortion)
    record("prime Perron saving", medium_count == F(".005") and medium_count > 0)
    record("conductor counts", high_count == F(".345") and base > high_count)
    record("two prime blocks", field_base < perturbation)
    record("greedy-Rankin coefficient", smooth_u < F(".57")*log2_lower)
    record("all character blocks, worst endpoint", F(".01")*1000 > 2*log2_upper)
    record("two-list exponential error", smooth_u > max(precision, distortion))
    record("Gram diagonal", evaluation > F(".39") > max(smooth_u, base, precision, interval_width))
    record("progression and Gaussian costs", evaluation > max(precision, base))
    record("Gram vector norm", projection_norm == F("1.08"))
    record("two lower bounds for transformed vectors",
           degree-projection_norm > -F(".81") and degree-2*perturbation > -F("1.20"))
    record("positive model retained", degree+smooth_u <= F(".69"))
    record("emitted exponent height", 1-base == F(".64") < F(".65") < perturbation)
    record("final order splitting", perturbation > F(".50"))
    record("single exact root test",
           max(degree, evaluation, base, F(".65")) < perturbation)
    return checks


def check_logarithmic_schedule():
    # A pair (j,k) represents X^j t^k, with X=(log N)^(1/3) and t=log log N.
    # Ordinary lexicographic comparison is the asymptotic dominance order.
    def weight(x, t=0):
        return F(x), F(t)

    def times(left, right):
        return left[0] + right[0], left[1] + right[1]

    def ratio(left, right):
        return left[0] - right[0], left[1] - right[1]

    def power(left, exponent):
        return left[0]*F(exponent), left[1]*F(exponent)

    log_l, l = weight(0, 1), weight(3)
    degree = weight(1, "-3/4")
    log_b, log_a, log_u = weight(1, "3/2"), weight(1, 4), weight(2, 4)
    log_k, minus_log_w = weight(1, "3/8"), weight(1, "1/3")
    log_m = ratio(l, degree)
    smooth_u = ratio(log_u, log_b)
    local_saddle = ratio(smooth_u, power(log_l, 2))
    rankin = ratio(times(log_m, log_l), log_b)
    clean_decay = weight(1, "7/16")
    log_landau = ratio(log_b, log_l)
    nu = weight(-1, "-1/4")
    medium, high = times(nu, log_b), times(nu, log_m)
    vector_square = times(smooth_u, power(log_b, 2))
    checks = {
        "input root degree": log_m == weight(2, "3/4"),
        "target polynomial height": times(degree, log_a) < log_u,
        "base below target height": log_m < log_u,
        "base above evaluation": log_a < log_m,
        "bracket stability": times(degree, log_l) < minus_log_w < log_k,
        "fraction of root-order spread": minus_log_w < log_b,
        "smoothness exponent": smooth_u == weight(1, "5/2"),
        "Brun modulus, factorial and endpoint costs": max(log_b, weight(0, 3)) < log_a,
        "medium exponent": medium == weight(0, "5/4") > log_l,
        "high exception count": high == weight(1, "1/2") < log_b,
        "high divisor estimate": power(log_m, "1/2") < log_b,
        "medium divisor estimate": power(log_b, "1/2") < log_landau,
        "height below small-conductor zero cutoff": log_k < log_landau,
        "Perron power saving": times(nu, log_b) > log_l,
        "Rankin distortion": rankin == weight(1, "1/4"),
        "clean transform decay": max(log_k, rankin) < clean_decay < local_saddle,
        "two-block modulus bound": max(log_b, log_m) < log_u,
        "all-character cost": max(log_b, rankin, log_k) < smooth_u,
        "medium dirty pairs": max(medium, rankin, power(log_b, "1/2")) < log_landau,
        "high dirty pairs": max(high, rankin, power(log_m, "1/2")) < log_b,
        "old diagonal loss": max(log_b, times(smooth_u, log_l), minus_log_w) < log_a,
        "close pairs": minus_log_w < log_k,
        "protected vector sizes": vector_square == weight(3, "11/2"),
        "transformed vector lower bound 1": ratio(degree, vector_square) > power(l, "-.81"),
        "transformed vector lower bound 2": ratio(degree, power(log_u, 2)) > power(l, "-1.20"),
        "positive centered limit": times(degree, smooth_u) < power(l, ".69"),
        "saturation": times(ratio(l, log_b), log_l) == weight(2, "-1/2"),
        "output guard and terminal work": max(log_b, times(ratio(l, log_b), log_l)) < weight(2) < log_u,
    }
    for label, valid in checks.items():
        assert valid, label
    return checks


def check_saturation():
    # Recount the multiset products used in Lemma 11.1 on actual finite alphabets.
    from itertools import combinations_with_replacement
    from math import prod
    total = 0
    for p in (101, 127, 251, 509, 1009, 2039):
        for bound in (7, 11, 17, 19):
            generators = [q for q in (5, 7, 11, 13, 17, 19) if bound//2 < q <= bound]
            k = 0
            while bound**(k+1) < p:
                k += 1
            products = [prod(v) for v in combinations_with_replacement(generators, k)]
            distinct = len({v % p for v in products})
            assert distinct == len(products) and max(products) < p
            assert distinct * factorial(k) >= len(generators)**k
            total += 1
    return total


if __name__ == "__main__":
    print("exact parameter comparisons", len(check_schedule()))
    print("logarithmic schedule comparisons", len(check_logarithmic_schedule()))
    print("finite subgroup-index multiset checks", check_saturation())
