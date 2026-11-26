"""Check a strict rational schedule for the variable-multiple factoring ledger."""

from fractions import Fraction


x, b, c, s = map(Fraction, ("0.7211248", "0.9614997", "1.9229994271", "6"))
norm = x * c + 1 / x

assert c - 2 * b == Fraction("0.0000000271")
assert c - b - norm / (3 * b) > Fraction("0.0000000000175")
assert s - 2 * c - 2 * b > Fraction("0.23")

sieve = 2 * c
lift = 4 * b
columns = 2 * c + 2 * b - 2 * norm / (3 * b)
assert sieve == Fraction("3.8459988542")
assert lift == Fraction("3.8459988")
assert Fraction("3.84599880003") < columns < Fraction("3.84599880004")
assert max(lift, columns) < sieve < Fraction("3.84599885421")

infimum_cubed = Fraction(512, 9)
assert Fraction("3.84599885415308") ** 3 < infimum_cubed < Fraction("3.84599885415310") ** 3
assert (sieve - Fraction("0.00000000005")) ** 3 < infimum_cubed < sieve ** 3
print("Exact strict schedule verified. Time coefficient 3.8459988542.")
