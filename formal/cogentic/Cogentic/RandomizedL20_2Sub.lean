import Cogentic.RandomizedL20_2
import Cogentic.RandomizedSmoothDensity
import Cogentic.RandomizedTopStripMoments

set_option linter.style.haveILetI false

/-!
# L20.2: reducing the elementary sub-lemmas

`Cogentic.RandomizedL20_2` decomposes the interior concentration
`ε_i ≤ D^{-2A}` (`A = D^{1/48}`) into six named paper-level inputs:

* `SaddlePointScaleLower`, `SaddlePointMeanLower` (Appendix C,
  Hildebrand–Tenenbaum),
* `TruncatedGeometricCRTLaw` (the truncated geometric CRT law),
* `SmoothCharacterSumBound` (Lemma G.2 p.106, GRH smooth-character sums),
* `OnePointProxyComparison` (equation (G.8)),
* `TwoPointOffDiagonalBound` (Proposition G.10).

This file discharges the elementary content of those inputs and leaves only the
genuinely paper-level smooth-character and saddle-point analysis as explicit
`Prop`s.

## What is proved

1. **Truncated geometric CRT arithmetic** (`crtTruncation`,
   `geometricCRTError`, `geometricCRTError_le`).  The truncation of a geometric
   progression at level `⌈2 D log D⌉₊ + 1` has remainder
   `r^N / (1 - r)` with `r = exp (-1)`.  Since `exp 1 ≥ 2`, the geometric
   denominator is at least `1/2`, and the remainder is at most
   `2 exp (-N) ≤ exp (-2 D log D)`.  This proves
   `truncatedGeometricCRTLaw : TruncatedGeometricCRTLaw geometricCRTError 2`
   with no analytic input.
2. **Saddle-point scale/mean arithmetic** (`saddlePointScaleLower_exact`,
   `saddlePointMeanLower_exact`, `saddle_mean_lower_of_scale`).  The exact forms
   `Λ = c D log D` and `μ = exp (η Λ)` satisfy the two lower-bound `Prop`s, and
   the two bounds combine to the explicit mean lower bound
   `exp (η c D log D) ≤ μ` consumed by the diagonal estimate.  The saddle-point
   analysis itself stays an explicit `Prop` field.
3. **One-point proxy comparison** (`onePointProxyComparison_of_error`,
   `onePointProxyComparison_of_ratio`).  If the proxy mean exceeds the actual
   mean by an error dominated by the mean, the proxy mean is at most `2 μ`.
   The second form is the shape produced by
   `Randomized.ratio_expectation_le_of_prob` from `RandomizedTopStripMoments`.
4. **Off-diagonal reduction** (`OffDiagonalCoupledBound`,
   `SmoothCharacterOffDiagonalBudget`, `twoPointOffDiagonalBound_of_coupled`).
   The off-diagonal two-point estimate factors into the coupled-mode
   Cauchy–Schwarz bound (the shape of
   `Randomized.coupled_mode_cauchy_schwarz`) and the smooth-character budget.
   The latter is the only paper-level part left as a `Prop`.
5. **The reduced bundle** (`L20_2SubInputs`, `L20_2SubInputs.toInputs`,
   `L20_2SubInputs.toConcentrationLeaf`).  The bundle replaces the CRT `Prop` by
   the proved geometric tail, replaces the one-point `Prop` by the proxy-error
   comparison, and replaces the two-point `Prop` by the coupled-mode plus
   smooth-character split.  It builds the original `L20_2Inputs`, hence the
   `ConcentrationLeaf` and the `B = 2` ledger slot.

No `sorry`, `admit`, `axiom`, or `native_decide`.  The loss is the actual
normalized mean discrepancy of `RandomizedL20_2`; nothing is set to zero.
-/

namespace Cogentic.RandomizedL20_2Sub

open Filter Real
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.Randomized

/-! ## 1. Truncated geometric CRT arithmetic

The geometric law is the arithmetic model of the CRT refinement: a geometric
progression with ratio `r` is truncated after `N` terms, and the total-variation
defect is the geometric tail `r^N / (1 - r)`.  We use the ratio `r = exp (-1)`
and the truncation level `⌈2 D log D⌉₊ + 1`. -/

/-- The truncation level of the geometric CRT refinement. -/
noncomputable def crtTruncation (n : ℕ) : ℕ :=
  ⌈2 * (paperD n * scale n)⌉₊ + 1

/-- The truncated geometric remainder, i.e. the exact tail `r^N / (1 - r)` of a
geometric series with ratio `r = exp (-1)` after `N = crtTruncation n` terms. -/
noncomputable def geometricCRTError (n : ℕ) : ℝ :=
  (exp (-1 : ℝ)) ^ crtTruncation n / (1 - exp (-1 : ℝ))

/-- The geometric remainder is nonnegative. -/
theorem geometricCRTError_nonneg (n : ℕ) : 0 ≤ geometricCRTError n := by
  unfold geometricCRTError
  have h1 : (0 : ℝ) ≤ exp (-1) := (exp_pos _).le
  have hlt : exp (-1 : ℝ) < 1 := by
    rw [exp_neg]
    exact inv_lt_one_of_one_lt₀ (by linarith [Real.exp_one_gt_two])
  have hden : 0 < 1 - exp (-1) := sub_pos.mpr hlt
  positivity

/-- **The truncated geometric tail is `exp (-2 D log D)`.**  The proof is pure
exponent arithmetic: `exp 1 ≥ 2` gives `1 - exp (-1) ≥ 1/2`, hence
`1/(1 - exp (-1)) ≤ 2`; the truncation at `⌈2 D log D⌉₊ + 1` then leaves
`2 exp (-(⌈2 D log D⌉₊ + 1)) ≤ exp (-2 D log D)`. -/
theorem geometricCRTError_le (n : ℕ) :
    geometricCRTError n ≤ exp (-2 * (paperD n * scale n)) := by
  unfold geometricCRTError
  set x : ℝ := paperD n * scale n with hx
  have hlt : exp (-1 : ℝ) < 1 := by
    rw [exp_neg]
    exact inv_lt_one_of_one_lt₀ (by linarith [Real.exp_one_gt_two])
  have hdenhalf : (1 / 2 : ℝ) ≤ 1 - exp (-1) := by
    have h : exp (-1) ≤ (1 / 2 : ℝ) := by
      rw [exp_neg]
      have h2 : (2 : ℝ) ≤ exp 1 := le_of_lt Real.exp_one_gt_two
      calc
        (exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
        _ = 1 / 2 := by norm_num
    linarith
  have hinv : (1 - exp (-1))⁻¹ ≤ 2 := by
    rw [← one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hdenhalf
    simpa using h
  have hN : ((crtTruncation n : ℝ)) = (⌈2 * x⌉₊ : ℝ) + 1 := by
    unfold crtTruncation
    rw [hx]
    push_cast
    ring
  have hrewrite :
      (exp (-1 : ℝ)) ^ crtTruncation n = exp (-((crtTruncation n : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [div_eq_mul_inv, hrewrite]
  have hstep : exp (-((crtTruncation n : ℝ))) * (1 - exp (-1))⁻¹ ≤
      exp (-((crtTruncation n : ℝ))) * 2 :=
    mul_le_mul_of_nonneg_left hinv (exp_pos _).le
  have hstep2 : exp (-((crtTruncation n : ℝ))) * 2 ≤ exp (-2 * x) := by
    have h2e : (2 : ℝ) ≤ exp 1 := le_of_lt Real.exp_one_gt_two
    calc
      exp (-((crtTruncation n : ℝ))) * 2
          ≤ exp (-((crtTruncation n : ℝ))) * exp 1 :=
            mul_le_mul_of_nonneg_left h2e (exp_pos _).le
      _ = exp (-((crtTruncation n : ℝ)) + 1) := by rw [← exp_add]
      _ = exp (-((⌈2 * x⌉₊ : ℝ))) := by
            rw [hN]
            congr 1
            ring
      _ ≤ exp (-2 * x) := by
            apply exp_le_exp.mpr
            by_cases hx0 : 0 ≤ x
            · have hceil : 2 * x ≤ (⌈2 * x⌉₊ : ℝ) := Nat.le_ceil _
              linarith
            · have hneg : 2 * x ≤ 0 := by linarith
              have hzero : ⌈2 * x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hneg
              rw [hzero]
              push_cast
              have hnonneg : 0 ≤ -2 * x := by linarith
              simpa using one_le_exp hnonneg
  exact hstep.trans hstep2

/-- The geometric tail is the truncated geometric CRT law with constant `2`. -/
theorem truncatedGeometricCRTLaw :
    TruncatedGeometricCRTLaw geometricCRTError 2 := by
  refine ⟨by norm_num, fun n => ⟨geometricCRTError_nonneg n, ?_⟩⟩
  refine (geometricCRTError_le n).trans (le_of_eq ?_)
  congr 1
  ring

/-! ## 2. Saddle-point scale and mean arithmetic -/

/-- The exact saddle scale `Λ = c D log D` satisfies the scale lower bound. -/
theorem saddlePointScaleLower_exact {c : ℝ} (hc : 0 < c) :
    SaddlePointScaleLower (fun n => c * paperD n * scale n) c :=
  ⟨hc, fun _ => le_rfl⟩

/-- The exact saddle mean `μ = exp (η Λ)` satisfies the mean lower bound. -/
theorem saddlePointMeanLower_exact {Λ : ℕ → ℝ} {η : ℝ} (hη : 0 < η) :
    SaddlePointMeanLower (fun n => exp (η * Λ n)) Λ η :=
  ⟨hη, fun _ => le_rfl⟩

/-- The scale lower bound, unfolded. -/
theorem saddle_scale_lower_bound {Λ : ℕ → ℝ} {c : ℝ}
    (h : SaddlePointScaleLower Λ c) (n : ℕ) :
    c * paperD n * scale n ≤ Λ n :=
  h.2 n

/-- The mean lower bound, unfolded. -/
theorem saddle_mean_lower_bound {μ Λ : ℕ → ℝ} {η : ℝ}
    (h : SaddlePointMeanLower μ Λ η) (n : ℕ) :
    exp (η * Λ n) ≤ μ n :=
  h.2 n

/-- **Combining the saddle scale and mean bounds.**  `Λ ≥ c D log D` and
`μ ≥ exp (η Λ)` give the explicit lower bound `exp (η c D log D) ≤ μ` that the
G.10 diagonal estimate consumes. -/
theorem saddle_mean_lower_of_scale {Λ μ : ℕ → ℝ} {c η : ℝ}
    (hscale : SaddlePointScaleLower Λ c) (hmean : SaddlePointMeanLower μ Λ η) :
    ∀ n, exp (η * (c * paperD n * scale n)) ≤ μ n := by
  intro n
  have hdom := hscale.2 n
  have hmul : η * (c * paperD n * scale n) ≤ η * Λ n :=
    mul_le_mul_of_nonneg_left hdom hmean.1.le
  exact (exp_le_exp.mpr hmul).trans (hmean.2 n)

/-- On the nonnegative part of the scale, the geometric CRT error is dominated
by the saddle-point mean.  This is the arithmetic content of the one-point
error bound: the mean is exponentially large in `D log D`, while the CRT defect
decays at the same scale. -/
theorem geometricCRTError_le_mean_of_saddle {Λ μ : ℕ → ℝ} {c η : ℝ}
    (hscale : SaddlePointScaleLower Λ c) (hmean : SaddlePointMeanLower μ Λ η)
    {n : ℕ} (hD : 0 ≤ paperD n * scale n) :
    geometricCRTError n ≤ μ n := by
  refine (geometricCRTError_le n).trans ?_
  have hdom := hscale.2 n
  have hX : 0 ≤ paperD n * scale n := hD
  have hηc : 0 ≤ η * c := mul_nonneg hmean.1.le hscale.1.le
  have hleft : -2 * (paperD n * scale n) ≤ 0 := by nlinarith
  have hright : 0 ≤ η * (c * paperD n * scale n) := by
    apply mul_nonneg hmean.1.le
    have hs : 0 ≤ scale n := nonneg_of_mul_nonneg_right hX (paperD_pos n)
    exact mul_nonneg (mul_nonneg hscale.1.le (paperD_pos n).le) hs
  have hle : -2 * (paperD n * scale n) ≤ η * (c * paperD n * scale n) :=
    hleft.trans hright
  calc
    exp (-2 * (paperD n * scale n)) ≤ exp (η * (c * paperD n * scale n)) :=
      exp_le_exp.mpr hle
    _ ≤ exp (η * Λ n) := by
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hdom hmean.1.le
    _ ≤ μ n := hmean.2 n

/-! ## 3. The one-point proxy comparison (G.8) -/

/-- The proxy mean exceeds the actual mean by an explicit one-point error. -/
def OnePointProxyError (proxyMean μ err : ℕ → ℝ) : Prop :=
  ∀ n, proxyMean n ≤ μ n + err n

/-- The one-point error is dominated by the mean. -/
def OnePointErrorLeMean (err μ : ℕ → ℝ) : Prop :=
  ∀ n, err n ≤ μ n

/-- **G.8 reduced.**  A proxy error dominated by the mean gives the one-point
comparison `proxyMean ≤ 2 μ`. -/
theorem onePointProxyComparison_of_error {proxyMean μ err : ℕ → ℝ}
    (hproxy : OnePointProxyError proxyMean μ err)
    (herr : OnePointErrorLeMean err μ) :
    OnePointProxyComparison proxyMean μ := by
  intro n
  linarith only [hproxy n, herr n]

/-- **The one-point ratio estimate of `RandomizedTopStripMoments`.**  The
existing ratio-expectation bound gives a proxy mean of the form
`(1-δ)⁻¹ (Z + ε)`; the elementary budget `(1-δ)⁻¹ (Z + ε) ≤ 2μ` is exactly the
one-point comparison. -/
theorem onePointProxyComparison_of_ratio
    {ι : Type*} (K : Finset ι) (w Z E A : ι → ℝ) {δ ε μ : ℝ}
    (hw : ∀ k ∈ K, 0 ≤ w k) (hw_sum : ∑ k ∈ K, w k = 1)
    (hZ : ∀ k ∈ K, 0 ≤ Z k) (hA : ∀ k ∈ K, |A k| ≤ δ) (hδ : δ < 1)
    (hE : ∀ k ∈ K, |E k| ≤ ε)
    (hbudget : (1 / (1 - δ)) * ((∑ k ∈ K, w k * Z k) + ε) ≤ 2 * μ) :
    ∑ k ∈ K, w k * ((Z k + E k) / (1 + A k)) ≤ 2 * μ :=
  (ratio_expectation_le_of_prob K w Z E A hw hw_sum hZ hA hδ hE).trans hbudget

/-! ## 4. The off-diagonal reduction (G.10) -/

/-- The coupled-mode Cauchy–Schwarz output: the off-diagonal sum is at most the
product of the two one-coordinate second-moment envelopes.  This is the shape of
`Randomized.coupled_mode_cauchy_schwarz`. -/
def OffDiagonalCoupledBound (cross E₁ E₂ : ℕ → ℝ) : Prop :=
  ∀ n, cross n ≤ E₁ n * E₂ n

/-- The smooth-character budget: the coupled-mode product is within the CRT plus
GRH error budget times `μ²`.  This is the paper-level smooth-character input; it
is the only part of the off-diagonal estimate not reduced here. -/
def SmoothCharacterOffDiagonalBudget (E₁ E₂ μ crtError charError : ℕ → ℝ) : Prop :=
  ∀ n, E₁ n * E₂ n ≤ (crtError n + charError n) * μ n ^ 2

/-- **G.10 off-diagonal reduction.**  Coupled-mode Cauchy–Schwarz plus the
smooth-character budget gives the L20.2 off-diagonal two-point estimate. -/
theorem twoPointOffDiagonalBound_of_coupled
    {cross E₁ E₂ μ crtError charError : ℕ → ℝ}
    (hcoupled : OffDiagonalCoupledBound cross E₁ E₂)
    (hbudget : SmoothCharacterOffDiagonalBudget E₁ E₂ μ crtError charError) :
    TwoPointOffDiagonalBound cross μ crtError charError := by
  intro n
  exact (hcoupled n).trans (hbudget n)

/-- The existing coupled-mode theorem, re-exported in the shape consumed by
`OffDiagonalCoupledBound`.  This records that the first half of the off-diagonal
reduction is an already-proved estimate, not a new paper-level input. -/
theorem offDiagonalCoupledBound_of_coupledMode
    {Ω S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    (phases : Finset Ω) (w : Ω → ℝ) (hw : ∀ o ∈ phases, 0 ≤ w o)
    (i : S ↪ A) (j : S ↪ B) (f : Ω → A → ℝ) (g : Ω → B → ℝ)
    {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ E₂ ^ 2) :
    ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) ≤ E₁ * E₂ :=
  coupled_mode_cauchy_schwarz phases w hw i j f g hE₁ hE₂ hf hg

/-! ## 5. The reduced L20.2 input bundle -/

/-- The L20.2 inputs with the elementary sub-lemmas discharged.  Compared with
`L20_2Inputs`, the CRT law is the proved geometric tail
`truncatedGeometricCRTLaw`, the one-point comparison is reduced to a proxy error
dominated by the mean, and the off-diagonal estimate is reduced to the
coupled-mode bound plus the smooth-character budget.  The saddle-point and
smooth-character analysis remain explicit paper-level fields. -/
structure L20_2SubInputs where
  /-- The saddle-point scale `Λ_d`. -/
  Λ : ℕ → ℝ
  /-- The ideal interior mean `μ`. -/
  μ : ℕ → ℝ
  /-- The proxy score bound `L`. -/
  L : ℕ → ℝ
  /-- The smooth-character error budget. -/
  charError : ℕ → ℝ
  /-- The constant in `Λ ≥ c D log D`. -/
  cLam : ℝ
  /-- The constant in `μ ≥ exp (η Λ)`. -/
  η : ℝ
  /-- The smooth-character decay constant. -/
  cChar : ℝ
  /-- The polynomial exponent constant in `L ≤ exp (cL (log D)^5)`. -/
  cL : ℝ
  /-- Appendix C, scale part (paper-level). -/
  saddle_scale : SaddlePointScaleLower Λ cLam
  /-- Appendix C, mean part (paper-level). -/
  saddle_mean : SaddlePointMeanLower μ Λ η
  /-- `L` is nonnegative. -/
  L_nonneg : ∀ n, 0 ≤ L n
  /-- The polynomial exponent constant is nonnegative. -/
  cL_nonneg : 0 ≤ cL
  /-- The polynomial proxy bound. -/
  L_upper : ∀ n, L n ≤ exp (cL * (scale n) ^ 5)
  /-- The GRH smooth-character sum (paper-level). -/
  char_sum : SmoothCharacterSumBound charError cChar
  /-- The finite interior cell at each ledger index. -/
  cell : ∀ n, CellData n (L n)
  /-- The ideal mean is the actual mean of the cell. -/
  μ_eq : ∀ n, μ n = (cell n).mean (cell n).f
  /-- The proxy mean exceeds the actual mean by the geometric CRT error. -/
  proxy_error : ∀ n, (cell n).mean (cell n).proxy ≤ μ n + geometricCRTError n
  /-- The CRT error is dominated by the mean. -/
  proxy_error_le_mean : ∀ n, geometricCRTError n ≤ μ n
  /-- The first one-coordinate second-moment envelope. -/
  E₁ : ℕ → ℝ
  /-- The second one-coordinate second-moment envelope. -/
  E₂ : ℕ → ℝ
  /-- The coupled-mode Cauchy–Schwarz bound for the off-diagonal sum. -/
  coupled : OffDiagonalCoupledBound (fun n => (cell n).cross) E₁ E₂
  /-- The smooth-character budget for the coupled-mode product. -/
  offdiag_budget :
    SmoothCharacterOffDiagonalBudget E₁ E₂ μ geometricCRTError charError

namespace L20_2SubInputs

/-- The reduced bundle builds the original `L20_2Inputs` with the CRT law proved
and the one-point and two-point fields reduced. -/
noncomputable def toInputs (S : L20_2SubInputs) : L20_2Inputs where
  a := 1 / 48
  a_eq := rfl
  Λ := S.Λ
  μ := S.μ
  L := S.L
  crtError := geometricCRTError
  charError := S.charError
  cLam := S.cLam
  η := S.η
  cCRT := 2
  cChar := S.cChar
  cL := S.cL
  saddle_scale := S.saddle_scale
  saddle_mean := S.saddle_mean
  L_nonneg := S.L_nonneg
  cL_nonneg := S.cL_nonneg
  L_upper := S.L_upper
  crt_law := truncatedGeometricCRTLaw
  char_sum := S.char_sum
  cell := S.cell
  μ_eq := S.μ_eq
  one_point := onePointProxyComparison_of_error S.proxy_error S.proxy_error_le_mean
  two_point := twoPointOffDiagonalBound_of_coupled S.coupled S.offdiag_budget

/-- The concentration leaf built from the reduced inputs. -/
noncomputable def toConcentrationLeaf (S : L20_2SubInputs) : ConcentrationLeaf :=
  S.toInputs.toConcentrationLeaf

/-- The reduced bundle realizes the parent deficit exactly: the loss is still the
actual normalized mean discrepancy, never zero by fiat. -/
theorem toInputs_loss_eq (S : L20_2SubInputs) (n : ℕ) :
    S.toInputs.loss n =
      |(S.cell n).mean (S.cell n).f - (S.cell n).mean (S.cell n).proxy| / S.μ n :=
  rfl

/-- The reduced bundle's deficit is nonnegative. -/
theorem loss_nonneg (S : L20_2SubInputs) (n : ℕ) : 0 ≤ S.toInputs.loss n :=
  S.toInputs.loss_nonneg n

/-- The `B = 2` ledger slot for the reduced inputs. -/
theorem slot_le (S : L20_2SubInputs) :
    ∀ᶠ n : ℕ in atTop,
      (S.toInputs).loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toInputs.slot_le

end L20_2SubInputs

/-! ## Axiom audit -/

#print axioms geometricCRTError_nonneg
#print axioms geometricCRTError_le
#print axioms truncatedGeometricCRTLaw
#print axioms saddlePointScaleLower_exact
#print axioms saddlePointMeanLower_exact
#print axioms saddle_mean_lower_of_scale
#print axioms geometricCRTError_le_mean_of_saddle
#print axioms onePointProxyComparison_of_error
#print axioms onePointProxyComparison_of_ratio
#print axioms twoPointOffDiagonalBound_of_coupled
#print axioms offDiagonalCoupledBound_of_coupledMode
#print axioms L20_2SubInputs.toInputs
#print axioms L20_2SubInputs.toConcentrationLeaf
#print axioms L20_2SubInputs.toInputs_loss_eq
#print axioms L20_2SubInputs.loss_nonneg
#print axioms L20_2SubInputs.slot_le

end Cogentic.RandomizedL20_2Sub
