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

# Trace order k needs a positive margin in n/B beyond B^(2/k).
for k, c_text, b_text, x_text, reported in [
    (38, "1.48496", ".74247", ".82062", "2.96992"),
    (44, "1.4826", ".74129", ".82127", "2.9652"),
]:
    c, b, x = map(Fraction, (c_text, b_text, x_text))
    density_loss = 2 * (x*c + 1/x) / (3*b)
    assert c > 2*b and k * (2*c - density_loss - b) > 2*b
    assert max(2*c, 4*b, 2*c + 2*b - density_loss) == Fraction(reported)
    print(f"Full-grid trace order {k}: coefficient {reported}.")

k = 24
c, b, x, eta = map(Fraction, ("1.8714", ".93569", ".731", ".078"))
density_loss = 2 * (x*c + 1/x) / (3*b)
grid = b + density_loss + eta
assert c > 2*b and c < grid < 2*c and k * eta > 2*b
assert max(grid, 3*b + 2*eta) == Fraction("2.96307")
print("Thin-grid candidate ledger at trace order 24: coefficient 2.96307.")

# Counterfactual full-grid ledger: the needed residue bound is still open.
c, b, x = map(Fraction, ("1.35", ".88", ".86066"))
density_loss = 2 * (x*c + 1/x) / (3*b)
assert b < c < 2*b and 32 * (2*c - b - density_loss) > 2*b
assert max(2*c, 3*b, 2*c + 2*b - density_loss + Fraction(".0001")) == Fraction("2.70")
print("Relaxed full-grid ledger: coefficient 2.70 if averaged residue bounds transfer.")
