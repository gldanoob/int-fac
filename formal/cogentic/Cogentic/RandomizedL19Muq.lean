import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedTopStripMoments

/-!
# L19.5: the divided-strip density ratio `μ_q ≤ D^{cq} μ`

The L19.5 field `IdealZeroModeInputs.muq_le` of
`Cogentic.RandomizedL19SecondMoment` is the divided-strip comparison

  `μ_q n ≤ exp (cq * scale n) * μ n`

of `research/keybreak-balanced-strip-transfer.md` (equation (1)) and
`research/keybreak-mixed-strip-moment.md` (`μ_q = |S_q|/(X_*/q) ≤ D^{O(1)} μ`).

This file instantiates the two densities with the actual geometric quantities

  `μ n  = stripDensity S (X n)`,
  `μ_q n = stripDensity (dividedStrip S (q n)) (X n / q n)`,

where `S = primeBinPatternProducts A B patterns` is a disjoint prime-bin
pattern strip, and discharges the comparison from the existing counting theorem
`primeBinPatternProducts_dividedStrip_ratio_le`.  That theorem gives

  `μ_q / μ ≤ (d * log y) / c`

from the single population hypothesis

  `c * q / (d * log y) ≤ #(primeBin (A j) (B j))`

for a prescribed prime `q` in bin `j`.  The remaining work is the arithmetic

  `(d * log y) / c ≤ exp (cq * scale n)`,

which the paper obtains from its scale choices

* `d ≍ D = exp (scale n)`, i.e. `d ≤ exp (cd * scale n)`;
* `log y = (c + o(1)) log V` with `log V = D^{O(1)} = exp (O(scale n))`,
  i.e. `log y ≤ exp (cy * scale n)`;
* `c` a fixed positive constant, so `1 / c = exp (o(scale n))`, i.e.
  `1 / c ≤ exp (cc * scale n)`.

Combining the three exponents gives `cq = cd + cy + cc`, exactly the shape of
`IdealZeroModeInputs.muq_le`.  No density is set to zero, and the population and
scale hypotheses are the only assumptions left.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL19Muq

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## 1. The arithmetic `(d log y) / c ≤ exp (cq · scale)` -/

/-- **Exponent arithmetic for the divided-strip ratio.**  If

* `d ≤ exp (cd * scale n)`,
* `log y ≤ exp (cy * scale n)`,
* `1 / c ≤ exp (cc * scale n)`

with `d, log y ≥ 0` and `c > 0`, then

  `(d * log y) / c ≤ exp ((cd + cy + cc) * scale n)`.

These are the paper's scale choices: `d = D^{1+o(1)}`, `log y = D^{O(1)}`,
and `c` fixed, all written on the ledger scale `D = exp (scale n)`. -/
theorem ratio_le_exp_scale {d L c cd cy cc : ℝ} {n : ℕ}
    (_hd : 0 ≤ d) (hL : 0 ≤ L) (hc : 0 < c)
    (hd_bound : d ≤ exp (cd * scale n))
    (hL_bound : L ≤ exp (cy * scale n))
    (hc_bound : 1 / c ≤ exp (cc * scale n)) :
    d * L / c ≤ exp ((cd + cy + cc) * scale n) := by
  have hL_exp : (0 : ℝ) ≤ exp (cy * scale n) := (exp_pos _).le
  have hd_exp : (0 : ℝ) ≤ exp (cd * scale n) := (exp_pos _).le
  have hinv : (0 : ℝ) ≤ 1 / c := (one_div_pos.mpr hc).le
  have hdL : d * L ≤ exp (cd * scale n) * exp (cy * scale n) :=
    mul_le_mul hd_bound hL_bound hL hd_exp
  have hmain : d * L * (1 / c) ≤
      (exp (cd * scale n) * exp (cy * scale n)) * exp (cc * scale n) :=
    mul_le_mul hdL hc_bound hinv (mul_nonneg hd_exp hL_exp)
  have heq : d * L / c = d * L * (1 / c) := by ring
  rw [heq]
  calc
    d * L * (1 / c) ≤
        (exp (cd * scale n) * exp (cy * scale n)) * exp (cc * scale n) := hmain
    _ = exp ((cd + cy + cc) * scale n) := by
      rw [← exp_add, ← exp_add]
      congr 1
      ring

/-! ## 2. The strip data and the explicit population/scale hypotheses -/

/-- Explicit data for one divided prime-bin strip.  The strip itself is the
disjoint prime-bin pattern union `S = primeBinPatternProducts A B patterns`; `q n`
is the prescribed prime consumed by the divided test, `c, d` are the population
and bin-width parameters of `primeBinPatternProducts_dividedStrip_ratio_le`, and
`y, X` are the smoothness cutoff and the ambient strip scale.

The only hypotheses are the paper's positivity conditions, the membership of
`q n` in its bin, the disjointness of the bins, the population lower bound, and
the three scale comparisons on `d`, `log y`, and `1 / c`. -/
structure DividedStripRatioInputs (ι : Type) [DecidableEq ι] where
  /-- Lower bin endpoints. -/
  A : ι → ℕ
  /-- Upper bin endpoints. -/
  B : ι → ℕ
  /-- The family of occupied-bin patterns. -/
  patterns : Finset (Finset ι)
  /-- The bin in which the prescribed child prime `q n` lies. -/
  j : ι
  /-- The prescribed child prime at each ledger index. -/
  q : ℕ → ℕ
  /-- Population lower-bound constant of the prescribed bin. -/
  c : ℕ → ℝ
  /-- Bin relative-width parameter. -/
  d : ℕ → ℝ
  /-- Smoothness cutoff `y`. -/
  y : ℕ → ℝ
  /-- Ambient strip scale `X`. -/
  X : ℕ → ℝ
  /-- `c` is positive. -/
  hc : ∀ n, 0 < c n
  /-- `d` is positive. -/
  hd : ∀ n, 0 < d n
  /-- `y` is above one. -/
  hy : ∀ n, 1 < y n
  /-- The strip scale is positive. -/
  hX : ∀ n, 0 < X n
  /-- The prescribed prime lies in the target bin. -/
  hq : ∀ n, q n ∈ primeBin (A j) (B j)
  /-- The prime bins are pairwise disjoint. -/
  hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))
  /-- **Population lower bound**: the target bin has at least
  `c * q / (d * log y)` primes. -/
  hpop : ∀ n, c n * (q n : ℝ) / (d n * Real.log (y n)) ≤
    ((primeBin (A j) (B j)).card : ℝ)
  /-- Exponent of `d` on the ledger scale: `d ≍ D = exp (scale n)`. -/
  cd : ℝ
  /-- Exponent of `log y`: `log y = D^{O(1)}`. -/
  cy : ℝ
  /-- Exponent of `1 / c`: `c` is fixed, so this is `o(scale)`. -/
  cc : ℝ
  /-- Paper scale choice for `d`. -/
  d_le_exp : ∀ n, d n ≤ exp (cd * scale n)
  /-- Paper scale choice for `log y`. -/
  logy_le_exp : ∀ n, Real.log (y n) ≤ exp (cy * scale n)
  /-- Paper scale choice for `1 / c`. -/
  invc_le_exp : ∀ n, 1 / c n ≤ exp (cc * scale n)

namespace DividedStripRatioInputs

variable {ι : Type} [DecidableEq ι] (D : DividedStripRatioInputs ι)

/-- The prime-bin pattern strip underlying the two densities. -/
noncomputable def S : Finset ℕ :=
  primeBinPatternProducts D.A D.B D.patterns

/-- The ordinary strip density `μ = |S| / X`. -/
noncomputable def mu (n : ℕ) : ℝ :=
  stripDensity D.S (D.X n)

/-- The divided strip density `μ_q = |S_q| / (X / q)`. -/
noncomputable def muq (n : ℕ) : ℝ :=
  stripDensity (dividedStrip D.S (D.q n)) (D.X n / (D.q n : ℝ))

/-- The exponent `cq = cd + cy + cc` in `μ_q ≤ D^{cq} μ`. -/
def cq : ℝ := D.cd + D.cy + D.cc

/-- **The arithmetic part of L19.5.**  The divided-strip ratio envelope
`(d * log y) / c` is at most `D^{cq}` with `cq = cd + cy + cc`. -/
theorem ratio_envelope_le (n : ℕ) :
    D.d n * Real.log (D.y n) / D.c n ≤ exp (D.cq * scale n) := by
  have h := ratio_le_exp_scale (n := n) (d := D.d n) (L := Real.log (D.y n))
    (c := D.c n) (cd := D.cd) (cy := D.cy) (cc := D.cc)
    (D.hd n).le (Real.log_pos (D.hy n)).le (D.hc n)
    (D.d_le_exp n) (D.logy_le_exp n) (D.invc_le_exp n)
  simpa only [cq] using h

/-- The ratio theorem `primeBinPatternProducts_dividedStrip_ratio_le` in the
notation of this file: `μ_q / μ ≤ (d * log y) / c`. -/
theorem muq_div_mu_le (n : ℕ) :
    D.muq n / D.mu n ≤ D.d n * Real.log (D.y n) / D.c n := by
  have h := (primeBinPatternProducts_dividedStrip_ratio_le
    D.A D.B D.patterns D.j (q := D.q n) (c := D.c n) (d := D.d n) (y := D.y n)
    (X := D.X n)
    (D.hc n) (D.hd n) (D.hy n) (D.hX n) (D.hq n) D.hdisj (D.hpop n)).2
  simpa only [mu, muq, S] using h

/-- **L19.5 divided-strip comparison** (`IdealZeroModeInputs.muq_le`).
With the two densities instantiated as `stripDensity S X` and
`stripDensity (dividedStrip S q) (X/q)`, the paper's divided-strip ratio is

  `μ_q n ≤ exp (cq * scale n) * μ n`,

where `cq = cd + cy + cc` collects the explicit scale exponents of `d`,
`log y`, and `1 / c`.  The only assumptions are the population lower bound
`hpop` and the three scale comparisons. -/
theorem muq_le (n : ℕ) :
    D.muq n ≤ exp (D.cq * scale n) * D.mu n := by
  have hratio := D.muq_div_mu_le n
  have harith := D.ratio_envelope_le n
  by_cases hcard : D.S.card = 0
  · have hle : (dividedStrip D.S (D.q n)).card ≤ D.S.card := by
      rw [dividedStrip_card]
      exact Finset.card_filter_le _ _
    have hdiv : (dividedStrip D.S (D.q n)).card = 0 :=
      Nat.eq_zero_of_le_zero (hle.trans_eq hcard)
    simp [mu, muq, stripDensity, hdiv, hcard]
  · have hSpos : (0 : ℝ) < (D.S.card : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    have hmu : 0 < D.mu n := by
      unfold mu stripDensity
      exact div_pos hSpos (D.hX n)
    have hstep : D.mu n * (D.muq n / D.mu n) ≤
        D.mu n * (D.d n * Real.log (D.y n) / D.c n) :=
      mul_le_mul_of_nonneg_left hratio hmu.le
    have heq : D.mu n * (D.muq n / D.mu n) = D.muq n := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hmu.ne'
    have hfin : D.muq n ≤ D.mu n * exp (D.cq * scale n) := by
      rw [← heq]
      exact hstep.trans (mul_le_mul_of_nonneg_left harith hmu.le)
    rwa [mul_comm] at hfin

/-- The comparison packaged as the exact `IdealZeroModeInputs.muq_le` field,
together with the positivity of the ordinary strip density in the nonempty
case.  This is the form consumed by L19.5. -/
theorem muq_le_and_pos (hcard : 0 < D.S.card) (n : ℕ) :
    0 < D.mu n ∧ D.muq n ≤ exp (D.cq * scale n) * D.mu n := by
  have hSpos : (0 : ℝ) < (D.S.card : ℝ) := Nat.cast_pos.mpr hcard
  have hmu : 0 < D.mu n := by
    unfold mu stripDensity
    exact div_pos hSpos (D.hX n)
  exact ⟨hmu, D.muq_le n⟩

end DividedStripRatioInputs

/-! ## 3. Axiom audit -/

#print axioms ratio_le_exp_scale
#print axioms DividedStripRatioInputs.ratio_envelope_le
#print axioms DividedStripRatioInputs.muq_div_mu_le
#print axioms DividedStripRatioInputs.muq_le
#print axioms DividedStripRatioInputs.muq_le_and_pos

end Cogentic.RandomizedL19Muq
