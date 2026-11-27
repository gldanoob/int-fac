import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedDiagonalTransfer

/-!
# L19.4–L19.6: the narrow-width top second moment

This file decomposes the three `[GAP]` leaves of blueprint §2 C5.a

* **L19.4** — the Poisson quotient for the actual discrete Gaussian two-mark law
  at narrow width `σ = V^{1.01}` (`research/keybreak-narrow-top-moment.md`
  §"One nonthin pair on its exact support", `research/keybreak-mixed-strip-moment.md`
  §"Denominator of the Poisson quotient");
* **L19.5** — the ideal zero-mode bound `D^{O(1)} μ_q² + o(μ²)`
  (`research/keybreak-balanced-ideal-pair-audit.md` §"One-point density and ideal
  Gaussian quadrature", §"Prime factors of the period");
* **L19.6** — thin and small-determinant pairs, a fixed negative power of `V` on
  the rational-good region (`research/keybreak-balanced-class-integration.md` ¶5,
  `research/keybreak-thin-top-pairs.md`),

into explicit sub-lemmas, and proves the reduction from those sub-lemmas to the
`SubexpLeaf` records used by `RandomizedPaperLeafStatements`.

## What is proved and what is assumed

The *analytic* estimates of the manuscript are the `Prop` fields of the three
input structures.  Each field has a docstring naming the blueprint leaf, the
KeyBreak section, and the precise estimate.  What this file proves is the
*arithmetic and probabilistic reduction*:

* the subexponential conversion `D^{O(1)} · V^{-η} ≤ D^{-B}` for every `B`,
  using `log V = D^{O(1)}` (`DominatesScale`);
* the pointwise two-sided Poisson quotient estimate
  `|(ν + E)/(1 + A) - ν| ≤ 2 (|E| + |A|)` at `|A| ≤ 1/2`, and the averaged
  multiplier form via `RandomizedTopStripMoments.ratio_expectation_le_of_prob`
  (L19.7);
* the reduction of the marginal energy bounds to the coupled numerator error via
  `RandomizedTopStripMoments.coupled_mode_cauchy_schwarz` (L19.2), and the
  decay of the product of the two marginal energies;
* the finite Paley–Zygmund inequality and the resulting zero-mode mass lower
  bound, which keeps the `D^{O(1)}` factor explicit (it is *not* claimed to be
  subexponential; it is the polynomial factor charged to L17/L20.1);
* the diagonal residual bound of `RandomizedDiagonalTransfer`, showing that the
  diagonal contributes only to the `D^{O(1)}` zero-mode factor;
* the pruned-prime restoration estimate of
  `RandomizedTopStripMoments.pruned_prime_pair_restoration_weighted` as the
  bookkeeping behind the thin-pair restoration cost.

Nothing is a `sorry`, an `admit`, an `axiom`, or `native_decide`.  The three
losses are genuine positive deficits (absolute Poisson error, zero-mode relative
excess, thin/small-determinant fraction); none is set to zero.
-/

namespace Cogentic.RandomizedL19SecondMoment

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedOneThirdAsymptotic
open scoped BigOperators

/-! ## 1. Subexponential conversion at the `D = exp (scale n)` scale -/

/-- `W` dominates every fixed multiple of the ledger scale.  In the manuscript
`W = log V` and `log V = D^{O(1)}` with `D = exp (scale n)`, so `W` beats
`c · scale n` for every fixed `c`. -/
def DominatesScale (W : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, c * scale n ≤ W n

/-- A sequence eventually bounded by a `SubexpLoss` sequence is a `SubexpLoss`
sequence. -/
theorem subexpLoss_of_eventually_le {f g : ℕ → ℝ}
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) (hg : SubexpLoss g) :
    SubexpLoss f := by
  intro B hB
  filter_upwards [hfg, hg B hB] with n h1 h2
  exact h1.trans h2

/-- `exp (C · scale) · exp (-η W)` is eventually at most `exp (-B · scale)`
whenever `W` dominates every fixed multiple of `scale` and `η > 0`.  This is the
`D^{O(1)} · V^{-η} ≤ D^{-B}` bookkeeping used by all three leaves. -/
theorem eventually_exp_mul_exp_neg_le {W : ℕ → ℝ} (hW : DominatesScale W)
    {C η : ℝ} (hη : 0 < η) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      exp (C * scale n) * exp (-η * W n) ≤ exp (-B * scale n) := by
  have hnum : 0 < B + max C 0 + 1 := by
    have := le_max_right C 0
    linarith
  have hc : 0 < (B + max C 0 + 1) / η := div_pos hnum hη
  filter_upwards [hW ((B + max C 0 + 1) / η) hc,
    scale_grows.eventually_ge_atTop 0] with n hn hs
  have hmul : (B + max C 0 + 1) * scale n ≤ η * W n := by
    have h1le := mul_le_mul_of_nonneg_left hn hη.le
    have heq : η * (((B + max C 0 + 1) / η) * scale n) =
        (B + max C 0 + 1) * scale n := by
      rw [← mul_assoc, mul_div_cancel₀ _ hη.ne']
    calc
      (B + max C 0 + 1) * scale n =
          η * (((B + max C 0 + 1) / η) * scale n) := heq.symm
      _ ≤ η * W n := h1le
  have hC : C * scale n ≤ max C 0 * scale n :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hs
  rw [← exp_add]
  apply exp_le_exp.mpr
  nlinarith

/-- The scalar `SubexpLoss` form of `eventually_exp_mul_exp_neg_le`. -/
theorem subexpLoss_exp_mul_exp_neg {W : ℕ → ℝ} (hW : DominatesScale W)
    {C η : ℝ} (hη : 0 < η) :
    SubexpLoss (fun n => exp (C * scale n) * exp (-η * W n)) :=
  fun B hB => eventually_exp_mul_exp_neg_le (B := B) hW hη hB

/-- A sum of two `SubexpLoss` sequences is a `SubexpLoss` sequence: the harmless
factor `2` is absorbed by `scale n → ∞`. -/
theorem subexpLoss_add {f g : ℕ → ℝ} (hf : SubexpLoss f) (hg : SubexpLoss g) :
    SubexpLoss (fun n => f n + g n) := by
  intro B hB
  filter_upwards [hf (B + 1) (by linarith), hg (B + 1) (by linarith),
    scale_grows.eventually_ge_atTop (Real.log 2)] with n hf' hg' hs
  have h2 : exp (Real.log 2) = (2 : ℝ) := exp_log (by norm_num)
  calc
    f n + g n ≤ exp (-(B + 1) * scale n) + exp (-(B + 1) * scale n) :=
      add_le_add hf' hg'
    _ = 2 * exp (-(B + 1) * scale n) := by ring
    _ = exp (Real.log 2) * exp (-(B + 1) * scale n) := by rw [h2]
    _ = exp (Real.log 2 + -(B + 1) * scale n) := by rw [← exp_add]
    _ ≤ exp (-B * scale n) := by
      apply exp_le_exp.mpr
      nlinarith

/-- A fixed nonnegative multiple of a `SubexpLoss` sequence is a `SubexpLoss`
sequence.  Only the factor `2` is needed below. -/
theorem subexpLoss_two_mul {f : ℕ → ℝ} (hf : SubexpLoss f) :
    SubexpLoss (fun n => 2 * f n) := by
  intro B hB
  filter_upwards [hf (B + 1) (by linarith),
    scale_grows.eventually_ge_atTop (Real.log 2)] with n hf' hs
  have h2 : exp (Real.log 2) = (2 : ℝ) := exp_log (by norm_num)
  calc
    2 * f n ≤ 2 * exp (-(B + 1) * scale n) := by gcongr
    _ = exp (Real.log 2) * exp (-(B + 1) * scale n) := by rw [h2]
    _ = exp (Real.log 2 + -(B + 1) * scale n) := by rw [← exp_add]
    _ ≤ exp (-B * scale n) := by
      apply exp_le_exp.mpr
      nlinarith

/-! ## 2. The L19.2 coupled-mode Cauchy–Schwarz input

The two marginal Parseval/prefix energies are the hypotheses `hf`/`hg` of
`RandomizedTopStripMoments.coupled_mode_cauchy_schwarz`.  The theorems below are
the scalar forms consumed by L19.4: the coupled numerator sum is at most the
product of the two marginal energies, and that product is `SubexpLoss` once the
marginals have the `D^{O(1)} V^{-η}` decay supplied by
`primeBinProducts_gridPrefix_from_critical_line` and
`primeBinProducts_mellin_energy_from_critical_line`. -/

/-- The multiplier-averaged coupled-mode Cauchy–Schwarz bound of L19.2, in the
exact form used for the L19.4 numerator. -/
theorem coupled_mode_pair_bound {Ω S A B : Type*} [Fintype S] [Fintype A]
    [Fintype B] (phases : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ o ∈ phases, 0 ≤ w o) (i : S ↪ A) (j : S ↪ B)
    (f : Ω → A → ℝ) (g : Ω → B → ℝ) {E₁ E₂ : ℝ}
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ E₂ ^ 2) :
    ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) ≤ E₁ * E₂ :=
  Cogentic.Randomized.coupled_mode_cauchy_schwarz phases w hw i j f g hE₁ hE₂ hf hg

/-- Equal marginal energy bounds `M` give the coupled sum bound `M²`. -/
theorem coupled_mode_energy_le {Ω S A B : Type*} [Fintype S] [Fintype A]
    [Fintype B] (phases : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ o ∈ phases, 0 ≤ w o) (i : S ↪ A) (j : S ↪ B)
    (f : Ω → A → ℝ) (g : Ω → B → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ M ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ M ^ 2) :
    ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s) ≤ M * M := by
  simpa only [pow_two] using
    coupled_mode_pair_bound phases w hw i j f g hM hM hf hg

/-- The product of two marginal energies with `D^{O(1)} V^{-η}` decay is
`SubexpLoss`.  This is the scalar L19.2 → L19.4 step. -/
theorem subexpLoss_marginal_product {W : ℕ → ℝ} (hW : DominatesScale W)
    {c₁ c₂ η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    {E₁ E₂ : ℕ → ℝ} (_hE₁ : ∀ n, 0 ≤ E₁ n) (hE₂ : ∀ n, 0 ≤ E₂ n)
    (h₁ : ∀ n, E₁ n ≤ exp (c₁ * scale n) * exp (-η₁ * W n))
    (h₂ : ∀ n, E₂ n ≤ exp (c₂ * scale n) * exp (-η₂ * W n)) :
    SubexpLoss (fun n => E₁ n * E₂ n) := by
  apply subexpLoss_of_eventually_le
    (g := fun n => exp ((c₁ + c₂) * scale n) *
      exp (-(η₁ + η₂) * W n))
  · exact Eventually.of_forall fun n => by
      have hc : exp (c₁ * scale n) * exp (c₂ * scale n) =
          exp ((c₁ + c₂) * scale n) := by
        rw [← exp_add]
        congr 1
        ring
      have hw : exp (-η₁ * W n) * exp (-η₂ * W n) =
          exp (-(η₁ + η₂) * W n) := by
        rw [← exp_add]
        congr 1
        ring
      calc
        E₁ n * E₂ n ≤
            (exp (c₁ * scale n) * exp (-η₁ * W n)) *
              (exp (c₂ * scale n) * exp (-η₂ * W n)) :=
          mul_le_mul (h₁ n) (h₂ n) (hE₂ n) (by positivity)
        _ = (exp (c₁ * scale n) * exp (c₂ * scale n)) *
              (exp (-η₁ * W n) * exp (-η₂ * W n)) := by ring
        _ = exp ((c₁ + c₂) * scale n) * exp (-(η₁ + η₂) * W n) := by
          rw [hc, hw]
  · have hη : 0 < η₁ + η₂ := by linarith
    exact subexpLoss_exp_mul_exp_neg hW hη

/-! ## 3. L19.4: the Poisson quotient at narrow width

The manuscript's narrow-width statement is

`actual pair probability = ν(f) + O(V^{-1/2})`,

obtained by dividing the Poisson numerator `ν(f) + O(V^{-1/2})` by the
denominator `1 + O(V^{-1/2})` uniformly over multipliers.  The fields
`E_bound` and `A_bound` are exactly those two estimates after the marginal
energy assembly; `numerator_energy` states that the numerator error is bounded
by the product of the two marginal energies, whose decay is supplied by
`coupled_mode_cauchy_schwarz`. -/

/-- Averaged multiplier form of the Poisson ratio bound, using
`RandomizedTopStripMoments.ratio_expectation_le_of_prob` (blueprint L19.7).
This keeps the hypothesis `|A k| ≤ δ < 1` and the probability weights explicit;
the actual L19.4 statement below is the pointwise two-mark version. -/
theorem averaged_ratio_upper {ι : Type*} (K : Finset ι) (w Z E A : ι → ℝ)
    {δ ε : ℝ} (hw : ∀ k ∈ K, 0 ≤ w k) (hw_sum : ∑ k ∈ K, w k = 1)
    (hZ : ∀ k ∈ K, 0 ≤ Z k) (hA : ∀ k ∈ K, |A k| ≤ δ) (hδ : δ < 1)
    (hE : ∀ k ∈ K, |E k| ≤ ε) :
    ∑ k ∈ K, w k * ((Z k + E k) / (1 + A k)) ≤
      (1 / (1 - δ)) * ((∑ k ∈ K, w k * Z k) + ε) :=
  Cogentic.Randomized.ratio_expectation_le_of_prob K w Z E A hw hw_sum hZ hA hδ hE

/-- The pointwise two-sided Poisson quotient estimate.  If the ideal normalized
mass `ν` lies in `[0,1]`, the numerator error is at most `εE`, and the
denominator error is at most `εA ≤ 1/2`, then the quotient differs from `ν` by at
most `2 (εE + εA)`. -/
theorem poisson_quotient_error_le {ν E A εE εA : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hE : |E| ≤ εE) (hA : |A| ≤ εA)
    (hAhalf : εA ≤ 1 / 2) (hεE : 0 ≤ εE) (hεA : 0 ≤ εA) :
    |(ν + E) / (1 + A) - ν| ≤ 2 * (εE + εA) := by
  have hA_lower : -(1 / 2 : ℝ) ≤ A := by
    have := (abs_le.mp hA).1
    linarith
  have h1A : (1 / 2 : ℝ) ≤ 1 + A := by linarith
  have h1Apos : 0 < 1 + A := by linarith
  have hden : (1 + A) ≠ 0 := ne_of_gt h1Apos
  have hnum : |E - ν * A| ≤ εE + εA := by
    have hsplit : |E - ν * A| ≤ |E| + |ν * A| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le E (-(ν * A))
    have hmul : |ν * A| = ν * |A| := by
      rw [abs_mul, abs_of_nonneg hν0]
    have hbound : ν * |A| ≤ 1 * εA :=
      mul_le_mul hν1 hA (abs_nonneg A) (by norm_num)
    calc
      |E - ν * A| ≤ |E| + |ν * A| := hsplit
      _ = |E| + ν * |A| := by rw [hmul]
      _ ≤ εE + 1 * εA := add_le_add hE hbound
      _ = εE + εA := by ring
  have hquot : (ν + E) / (1 + A) - ν = (E - ν * A) / (1 + A) := by
    rw [div_sub' hden]
    congr 1
    ring
  calc
    |(ν + E) / (1 + A) - ν| = |(E - ν * A) / (1 + A)| := by rw [hquot]
    _ = |E - ν * A| / |1 + A| := abs_div _ _
    _ = |E - ν * A| / (1 + A) := by rw [abs_of_pos h1Apos]
    _ ≤ (εE + εA) / (1 + A) :=
      div_le_div_of_nonneg_right hnum h1Apos.le
    _ ≤ (εE + εA) / (1 / 2) :=
      div_le_div_of_nonneg_left (add_nonneg hεE hεA) (by norm_num) h1A
    _ = 2 * (εE + εA) := by ring

/-- The paper-level estimates behind L19.4, together with the narrow-width,
two-mark, and marginal-energy data needed to turn them into the C5 slot.

The analytic fields are the manuscript's content (KB G.19 and
`research/keybreak-narrow-top-moment.md` §"One nonthin pair on its exact support",
`research/keybreak-mixed-strip-moment.md` §"Denominator of the Poisson quotient");
the derived `loss` is the actual absolute Poisson error, never a zero placeholder. -/
structure PoissonQuotientInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `log D = scale n`. -/
  W_dominates : DominatesScale W
  /-- The two prime mark denominators `b₁, b₂`. -/
  mark₁ : ℕ → ℕ
  /-- The second prime mark denominator. -/
  mark₂ : ℕ → ℕ
  /-- The first mark is prime. -/
  mark₁_prime : ∀ n, (mark₁ n).Prime
  /-- The second mark is prime. -/
  mark₂_prime : ∀ n, (mark₂ n).Prime
  /-- Distinct prime marks, as required by the two-mark Poisson quotient. -/
  mark_distinct : ∀ n, mark₁ n ≠ mark₂ n
  /-- Both marks lie in the top scale `O(V)`. -/
  mark_le : ∀ n, (max (mark₁ n) (mark₂ n) : ℝ) ≤ exp (W n)
  /-- The discrete Gaussian width. -/
  sigma : ℕ → ℝ
  /-- The width is positive. -/
  sigma_pos : ∀ n, 0 < sigma n
  /-- **Narrow width**: `σ = V^{1.01}` (`V = exp W`), the L19 regime. -/
  sigma_narrow : ∀ n, sigma n = exp (W n) ^ (101 / 100 : ℝ)
  /-- The ideal normalized mass `ν(f)` on the restricted support. -/
  nu : ℕ → ℝ
  /-- The actual two-mark pair probability. -/
  actual : ℕ → ℝ
  /-- `ν` is a normalized mass. -/
  nu_nonneg : ∀ n, 0 ≤ nu n
  /-- `ν` is at most one because `0 ≤ f ≤ 1`. -/
  nu_le_one : ∀ n, nu n ≤ 1
  /-- Numerator error `E` in the Poisson quotient. -/
  E : ℕ → ℝ
  /-- Denominator error `A` in the Poisson quotient. -/
  A : ℕ → ℝ
  /-- **Poisson quotient identity** (KB G.19): the actual pair probability is
  the quotient of the ideal numerator plus error by the denominator plus error. -/
  actual_eq : ∀ n, actual n = (nu n + E n) / (1 + A n)
  /-- The first marginal energy `E₁` (a finite Parseval/prefix energy). -/
  E₁ : ℕ → ℝ
  /-- The second marginal energy `E₂`. -/
  E₂ : ℕ → ℝ
  /-- The first energy is nonnegative. -/
  E₁_nonneg : ∀ n, 0 ≤ E₁ n
  /-- The second energy is nonnegative. -/
  E₂_nonneg : ∀ n, 0 ≤ E₂ n
  /-- Exponent in `E₁ = D^{c₁}`. -/
  c₁ : ℝ
  /-- Exponent in `E₂ = D^{c₂}`. -/
  c₂ : ℝ
  /-- Marginal decay exponent of `E₁` in `V`. -/
  η₁ : ℝ
  /-- Marginal decay exponent of `E₂` in `V`. -/
  η₂ : ℝ
  /-- The first marginal decay is genuine. -/
  η₁_pos : 0 < η₁
  /-- The second marginal decay is genuine. -/
  η₂_pos : 0 < η₂
  /-- **Marginal energy bound for `E₁`** (L19.2, KB G.19 + GRH):
  `E₁ ≤ D^{c₁} V^{-η₁}`.  In `RandomizedTopStripMoments` this is the output of
  `primeBinProducts_gridPrefix_from_critical_line` together with the Mellin
  Plancherel energy `primeBinProducts_mellin_energy_from_critical_line`. -/
  E₁_bound : ∀ n, E₁ n ≤ exp (c₁ * scale n) * exp (-η₁ * W n)
  /-- **Marginal energy bound for `E₂`** (L19.2, as above). -/
  E₂_bound : ∀ n, E₂ n ≤ exp (c₂ * scale n) * exp (-η₂ * W n)
  /-- **Numerator error from the coupled modes** (L19.2/L19.4): the Poisson
  numerator error is bounded by the product of the two marginal energies, the
  scalar form of `coupled_mode_cauchy_schwarz` applied to the two Parseval
  energy bounds. -/
  numerator_energy : ∀ n, |E n| ≤ E₁ n * E₂ n
  /-- Exponent in the denominator error envelope `D^{cA} V^{-ηA}`. -/
  cA : ℝ
  /-- Denominator decay exponent in `V`. -/
  ηA : ℝ
  /-- The denominator decay is genuine. -/
  ηA_pos : 0 < ηA
  /-- **Denominator bound for the Poisson quotient** (KB G.19,
  `research/keybreak-mixed-strip-moment.md` §Denominator):
  `|A| ≤ D^{cA} V^{-ηA}`, with `ηA = c' - 2ζ > 0` after the twisted-Gaussian
  variation loss. -/
  A_bound : ∀ n, |A n| ≤ exp (cA * scale n) * exp (-ηA * W n)

namespace PoissonQuotientInputs

variable (I : PoissonQuotientInputs)

/-- The numerator error envelope: the product of the two marginal energies. -/
noncomputable def epsNum (n : ℕ) : ℝ := I.E₁ n * I.E₂ n

/-- The denominator error envelope `D^{cA} V^{-ηA}`. -/
noncomputable def epsDen (n : ℕ) : ℝ :=
  exp (I.cA * scale n) * exp (-I.ηA * I.W n)

/-- The L19.4 deficit: the absolute difference between the actual two-mark pair
probability and the ideal normalized mass.  This is a genuine error, not a
placeholder. -/
noncomputable def loss (n : ℕ) : ℝ := |I.actual n - I.nu n|

theorem epsNum_nonneg (n : ℕ) : 0 ≤ I.epsNum n :=
  mul_nonneg (I.E₁_nonneg n) (I.E₂_nonneg n)

theorem epsDen_pos (n : ℕ) : 0 < I.epsDen n := by
  unfold epsDen
  positivity

/-- The product of the two marginal energies decays faster than any
`D^{-B}`.  This is the L19.2 → L19.4 numerator step. -/
theorem subexpLoss_epsNum : SubexpLoss I.epsNum := by
  unfold epsNum
  exact subexpLoss_marginal_product I.W_dominates I.η₁_pos I.η₂_pos
    I.E₁_nonneg I.E₂_nonneg I.E₁_bound I.E₂_bound

/-- The denominator envelope is eventually at most `1/2`. -/
theorem eventually_epsDen_le_half : ∀ᶠ n : ℕ in atTop, I.epsDen n ≤ 1 / 2 := by
  filter_upwards [eventually_exp_mul_exp_neg_le I.W_dominates (C := I.cA)
      I.ηA_pos (B := 1) (by norm_num),
    scale_grows.eventually_ge_atTop (Real.log 2)] with n hdecay hs
  have hhalf : (1 / 2 : ℝ) = exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  calc
    I.epsDen n ≤ exp (-1 * scale n) := hdecay
    _ ≤ (1 / 2 : ℝ) := by
      rw [hhalf]
      apply exp_le_exp.mpr
      nlinarith

/-- Eventually the actual pair probability differs from the ideal mass by at
most `2 (epsNum + epsDen)`; this is the manuscript's
`actual = ν(f) + O(V^{-1/2})`. -/
theorem eventually_loss_le (n : ℕ) (hn : I.epsDen n ≤ 1 / 2) :
    I.loss n ≤ 2 * (I.epsNum n + I.epsDen n) := by
  unfold loss epsNum epsDen
  rw [I.actual_eq n]
  exact poisson_quotient_error_le (I.nu_nonneg n) (I.nu_le_one n)
    (I.numerator_energy n) (I.A_bound n) hn
    (mul_nonneg (I.E₁_nonneg n) (I.E₂_nonneg n)) (le_of_lt (by positivity))

/-- **L19.4 subexponential statement.**  The actual Poisson quotient error is
`D^{-B}` for every `B > 0`. -/
theorem subexpLoss : SubexpLoss I.loss := by
  apply subexpLoss_of_eventually_le
    (g := fun n => 2 * (I.epsNum n + I.epsDen n))
  · filter_upwards [I.eventually_epsDen_le_half] with n hn
    exact I.eventually_loss_le n hn
  · exact subexpLoss_two_mul
      (subexpLoss_add I.subexpLoss_epsNum
        (subexpLoss_exp_mul_exp_neg I.W_dominates (C := I.cA) I.ηA_pos))

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := abs_nonneg _

/-- **The L19.4 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.subexpLoss

/-- The `B = 2` instance is exactly the `C5Inputs.l19_4` eventuality. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    I.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.subexpLoss 2 (by norm_num)

end PoissonQuotientInputs

/-! ## 4. L19.5: the ideal zero-mode bound

The manuscript bounds the ideal zero-mode second moment by

`D^{O(1)} μ_q² + o(μ²)`.

The `D^{O(1)} μ_q²` term is the polynomial factor that the surrounding assembly
(L17 trimming and the L20.1 recurrence) charges to its own budget; it is **not**
subexponential.  The L19.5 C5 slot is the genuinely small residual `o(μ²)`,
measured relative to `μ²`.  The finite Paley–Zygmund inequality below records
exactly how the zero-mode bound feeds the good-event mass; the polynomial factor
is kept visibly in the denominator. -/

/-- Finite Paley–Zygmund inequality.  For nonnegative scores `X` on a finite
weighted space, `(E X)² ≤ (E X²) · P(X > 0)`. -/
theorem paley_zygmund {Ω : Type*} (s : Finset Ω) (w X : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hX : ∀ ω ∈ s, 0 ≤ X ω) :
    (∑ ω ∈ s, w ω * X ω) ^ 2 ≤
      (∑ ω ∈ s, w ω * X ω ^ 2) * (∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0)) := by
  let f : Ω → ℝ := fun ω => Real.sqrt (w ω) * X ω
  let g : Ω → ℝ := fun ω => Real.sqrt (w ω) * (if 0 < X ω then 1 else 0)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hfg : ∑ ω ∈ s, f ω * g ω =
      ∑ ω ∈ s, w ω * X ω * (if 0 < X ω then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp only [f, g]
    have hsq := Real.mul_self_sqrt (hw ω hω)
    calc
      Real.sqrt (w ω) * X ω *
            (Real.sqrt (w ω) * (if 0 < X ω then 1 else 0))
          = (Real.sqrt (w ω) * Real.sqrt (w ω)) *
              (X ω * (if 0 < X ω then 1 else 0)) := by ring
      _ = w ω * (X ω * (if 0 < X ω then 1 else 0)) := by rw [hsq]
      _ = w ω * X ω * (if 0 < X ω then 1 else 0) := by ring
  have hf2 : ∑ ω ∈ s, f ω ^ 2 = ∑ ω ∈ s, w ω * X ω ^ 2 := by
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (hw ω hω)]
  have hg2 : ∑ ω ∈ s, g ω ^ 2 =
      ∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (hw ω hω)]
    split_ifs <;> ring
  have hXX : ∑ ω ∈ s, w ω * X ω * (if 0 < X ω then 1 else 0) =
      ∑ ω ∈ s, w ω * X ω := by
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : 0 < X ω
    · rw [if_pos h, mul_one]
    · have hzero : X ω = 0 := le_antisymm (not_lt.mp h) (hX ω hω)
      rw [if_neg h, hzero]
      ring
  rw [hfg, hXX, hf2, hg2] at hcs
  exact hcs

/-- Zero-mode mass lower bound with the polynomial factor kept explicit.
If the first moment is at least `μ` and the second moment is at most
`(K + ρ) μ²`, then the success probability is at least `1 / (K + ρ)`. -/
theorem zero_mode_mass_lower {Ω : Type*} (s : Finset Ω) (w X : Ω → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ w ω) (hX : ∀ ω ∈ s, 0 ≤ X ω)
    {μ K ρ : ℝ} (hμ : 0 < μ) (hKρ : 0 < K + ρ)
    (hmean : μ ≤ ∑ ω ∈ s, w ω * X ω)
    (hsecond : ∑ ω ∈ s, w ω * X ω ^ 2 ≤ (K + ρ) * μ ^ 2) :
    (1 : ℝ) / (K + ρ) ≤
      ∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0) := by
  have hpz := paley_zygmund s w X hw hX
  have hsq : μ ^ 2 ≤ (∑ ω ∈ s, w ω * X ω) ^ 2 := by
    exact pow_le_pow_left₀ hμ.le hmean 2
  have hPnonneg : 0 ≤ ∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0) :=
    Finset.sum_nonneg fun ω hω =>
      mul_nonneg (hw ω hω) (by split_ifs <;> norm_num)
  have hμ2 : 0 < μ ^ 2 := pow_pos hμ 2
  have hKμnonneg : 0 ≤ (K + ρ) * μ ^ 2 := le_of_lt (mul_pos hKρ hμ2)
  have hstep : μ ^ 2 ≤ ((K + ρ) * μ ^ 2) *
      (∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0)) := by
    calc
      μ ^ 2 ≤ (∑ ω ∈ s, w ω * X ω) ^ 2 := hsq
      _ ≤ (∑ ω ∈ s, w ω * X ω ^ 2) *
            (∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0)) := hpz
      _ ≤ ((K + ρ) * μ ^ 2) *
            (∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0)) :=
        mul_le_mul hsecond le_rfl hPnonneg hKμnonneg
  have h1 : 1 ≤ (K + ρ) *
      (∑ ω ∈ s, w ω * (if 0 < X ω then 1 else 0)) := by
    nlinarith only [hstep, hKρ, hμ2]
  rw [div_le_iff₀ hKρ]
  nlinarith only [h1]

/-- The diagonal residual bound of `RandomizedDiagonalTransfer` contributes only
to the `D^{O(1)}` zero-mode factor.  If the diagonal envelope `F + C P` is at
most `D^{c} μ`, then the diagonal squared residual divided by `μ²` is at most
`D^{c}` — a polynomial factor, not a subexponential loss. -/
theorem diagonal_contribution_le {ι Ω : Type*} (points : Finset ι)
    (outcomes : Finset Ω) (weight : Ω → ℝ) (f proxy : ι → Ω → ℝ)
    {F P C μ c : ℝ} (n : ℕ)
    (hw : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hf : ∀ i ∈ points, ∀ ω ∈ outcomes, 0 ≤ f i ω ∧ f i ω ≤ F)
    (hp : ∀ i ∈ points, ∀ ω ∈ outcomes, 0 ≤ proxy i ω ∧ proxy i ω ≤ P)
    (hP : 0 ≤ P) (hμ : 0 < μ)
    (hfirst : (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * f i ω) = μ)
    (hproxy : (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * proxy i ω) ≤ C * μ)
    (hscale : F + C * P ≤ exp (c * scale n) * μ) :
    (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * (f i ω - proxy i ω) ^ 2) / μ ^ 2 ≤
      exp (c * scale n) := by
  refine (Cogentic.Randomized.diagonal_residual_le points outcomes weight f proxy
    hw hf hp hP hμ hfirst hproxy).trans ?_
  rw [div_le_iff₀ hμ]
  exact hscale

/-- The paper-level estimates behind L19.5.  The field `zero_mode_bound` is the
manuscript's ellipse-covering/layer-cake bound with the period-prime removal of
`research/keybreak-balanced-ideal-pair-audit.md` §"Prime factors of the period";
`muq_le` is the divided-strip ratio (L20.5). -/
structure IdealZeroModeInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The ideal reference density `μ` on the rational-good strip. -/
  mu : ℕ → ℝ
  /-- The reference density is positive. -/
  mu_pos : ∀ n, 0 < mu n
  /-- The divided-strip density `μ_q`. -/
  muq : ℕ → ℝ
  /-- The divided density is positive. -/
  muq_pos : ∀ n, 0 < muq n
  /-- Exponent in the divided-strip comparison `μ_q ≤ D^{cq} μ`. -/
  cq : ℝ
  /-- **Divided-strip ratio** (L20.5, from
  `RandomizedTopStripMoments.primeBinPatternProducts_dividedStrip_ratio_le`):
  `μ_q ≤ D^{cq} μ`. -/
  muq_le : ∀ n, muq n ≤ exp (cq * scale n) * mu n
  /-- Exponent in the `D^{O(1)}` zero-mode factor. -/
  cz : ℝ
  /-- The ideal zero-mode second moment. -/
  zeroMode : ℕ → ℝ
  /-- The zero-mode term is nonnegative. -/
  zeroMode_nonneg : ∀ n, 0 ≤ zeroMode n
  /-- The `o(μ²)` residual sequence, measured relative to `μ²`. -/
  rho : ℕ → ℝ
  /-- The residual is nonnegative. -/
  rho_nonneg : ∀ n, 0 ≤ rho n
  /-- Exponent in the residual envelope `D^{cr} V^{-η}`. -/
  cr : ℝ
  /-- Decay exponent of the residual in `V`. -/
  eta : ℝ
  /-- The residual decay is genuine. -/
  eta_pos : 0 < eta
  /-- **Residual bound** (KB G.9, `research/keybreak-balanced-ideal-pair-audit.md`
  §"Prime factors of the period"): after removing the period primes,
  `ρ ≤ D^{cr} V^{-η}`. -/
  rho_bound : ∀ n, rho n ≤ exp (cr * scale n) * exp (-eta * W n)
  /-- **Ideal zero-mode bound** (KB G.9, `research/keybreak-balanced-ideal-pair-audit.md`
  §"One-point density and ideal Gaussian quadrature"): the ideal zero-mode term is
  at most `D^{cz} μ_q² + ρ μ²`. -/
  zero_mode_bound : ∀ n,
    zeroMode n ≤ exp (cz * scale n) * muq n ^ 2 + rho n * mu n ^ 2

namespace IdealZeroModeInputs

variable (I : IdealZeroModeInputs)

/-- The folded `D^{O(1)}` zero-mode factor, including the divided-strip ratio. -/
noncomputable def K (n : ℕ) : ℝ := exp ((I.cz + 2 * I.cq) * scale n)

/-- The L19.5 deficit: the relative excess of the ideal zero-mode term over its
`D^{O(1)} μ²` envelope.  This is the `o(μ²)` residual, not a zero placeholder. -/
noncomputable def loss (n : ℕ) : ℝ :=
  max 0 (I.zeroMode n / I.mu n ^ 2 - I.K n)

theorem K_pos (n : ℕ) : 0 < I.K n := by
  unfold K
  exact exp_pos _

/-- Folding the divided-strip ratio into the zero-mode factor gives
`zeroMode ≤ K μ² + ρ μ²` with `K = D^{cz + 2 cq}`. -/
theorem zero_mode_le (n : ℕ) :
    I.zeroMode n ≤ I.K n * I.mu n ^ 2 + I.rho n * I.mu n ^ 2 := by
  have hμ := I.mu_pos n
  have hμq := I.muq_pos n
  have hbound := I.zero_mode_bound n
  have hsq : I.muq n ^ 2 ≤ (exp (I.cq * scale n) * I.mu n) ^ 2 :=
    pow_le_pow_left₀ hμq.le (I.muq_le n) 2
  have hstep : exp (I.cz * scale n) * I.muq n ^ 2 ≤
      exp (I.cz * scale n) * (exp (I.cq * scale n) * I.mu n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (exp_pos _).le
  have hfac : exp (I.cz * scale n) * (exp (I.cq * scale n) * I.mu n) ^ 2 =
      I.K n * I.mu n ^ 2 := by
    unfold K
    rw [mul_pow]
    have hsq : exp (I.cq * scale n) ^ 2 = exp ((2 * I.cq) * scale n) := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    rw [hsq]
    calc
      exp (I.cz * scale n) * (exp ((2 * I.cq) * scale n) * I.mu n ^ 2)
          = (exp (I.cz * scale n) * exp ((2 * I.cq) * scale n)) * I.mu n ^ 2 := by
              ring
      _ = exp ((I.cz + 2 * I.cq) * scale n) * I.mu n ^ 2 := by
              rw [← exp_add]
              congr 1
              ring
  calc
    I.zeroMode n ≤ exp (I.cz * scale n) * I.muq n ^ 2 + I.rho n * I.mu n ^ 2 :=
      hbound
    _ ≤ exp (I.cz * scale n) * (exp (I.cq * scale n) * I.mu n) ^ 2 +
          I.rho n * I.mu n ^ 2 := add_le_add hstep le_rfl
    _ = I.K n * I.mu n ^ 2 + I.rho n * I.mu n ^ 2 := by rw [hfac]

/-- The relative excess is at most the residual `ρ`. -/
theorem loss_le_rho (n : ℕ) : I.loss n ≤ I.rho n := by
  have hμ := I.mu_pos n
  have hdiv : I.zeroMode n / I.mu n ^ 2 ≤ I.K n + I.rho n := by
    rw [div_le_iff₀ (pow_pos hμ 2)]
    nlinarith only [I.zero_mode_le n]
  have hsub : I.zeroMode n / I.mu n ^ 2 - I.K n ≤ I.rho n := by linarith
  exact max_le (I.rho_nonneg n) hsub

/-- **L19.5 subexponential statement.**  The `o(μ²)` residual is `D^{-B}` for
every `B > 0`.  The `D^{O(1)}` factor `K` is deliberately not part of this
statement: it is the polynomial factor of L17/L20.1 and is not subexponential. -/
theorem subexpLoss : SubexpLoss I.loss := by
  have hrho : SubexpLoss I.rho :=
    subexpLoss_of_eventually_le (g := fun n =>
      exp (I.cr * scale n) * exp (-I.eta * I.W n))
      (Eventually.of_forall I.rho_bound)
      (subexpLoss_exp_mul_exp_neg I.W_dominates (C := I.cr) I.eta_pos)
  exact subexpLoss_of_eventually_le (Eventually.of_forall I.loss_le_rho) hrho

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := le_max_left _ _

/-- **The L19.5 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.subexpLoss

/-- The `B = 2` instance is exactly the `C5Inputs.l19_5` eventuality. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    I.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.subexpLoss 2 (by norm_num)

end IdealZeroModeInputs

/-! ## 5. L19.6: thin and small-determinant pairs -/

/-- Pruned-prime restoration with a cardinality bound.  Restoring the removed
primes costs at most one one-point divisibility mass per removed prime; this is
the finite form of `pruned_prime_pair_restoration_weighted` used for the
thin-pair restoration step. -/
theorem pruned_restoration_le {α : Type*} (Ω : Finset α) (w : α → ℝ)
    (hw : ∀ ω ∈ Ω, 0 ≤ w ω) (X₁ X₂ : α → ℕ)
    (S S' removed : Finset ℕ)
    (hprune : ∀ n ∈ S, n ∉ S' → ∃ p ∈ removed, p ∣ n)
    {mass ε : ℝ}
    (hmass : (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S' ∧ X₂ ω ∈ S'), w ω) ≤ mass)
    (hε : ∀ p ∈ removed,
      (∑ ω ∈ Ω.filter (fun ω => p ∣ X₁ ω), w ω) +
        (∑ ω ∈ Ω.filter (fun ω => p ∣ X₂ ω), w ω) ≤ ε) :
    (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S ∧ X₂ ω ∈ S), w ω) ≤
      mass + removed.card * ε := by
  refine (Cogentic.Randomized.pruned_prime_pair_restoration_weighted Ω w hw X₁ X₂
    S S' removed hprune).trans ?_
  have hsum : (∑ p ∈ removed,
      ((∑ ω ∈ Ω.filter (fun ω => p ∣ X₁ ω), w ω) +
        (∑ ω ∈ Ω.filter (fun ω => p ∣ X₂ ω), w ω))) ≤
      ∑ _p ∈ removed, ε := Finset.sum_le_sum hε
  calc
    _ ≤ (∑ ω ∈ Ω.filter (fun ω => X₁ ω ∈ S' ∧ X₂ ω ∈ S'), w ω) +
          ∑ p ∈ removed,
            ((∑ ω ∈ Ω.filter (fun ω => p ∣ X₁ ω), w ω) +
              (∑ ω ∈ Ω.filter (fun ω => p ∣ X₂ ω), w ω)) := le_rfl
    _ ≤ mass + ∑ _p ∈ removed, ε := add_le_add hmass hsum
    _ = mass + removed.card * ε := by simp

/-- The paper-level estimates behind L19.6.

`thin` is the same-denominator/thin fraction and `smallDet` the small-determinant
fraction of `research/keybreak-thin-top-pairs.md`; both are a fixed negative
power of `V` after the `V^{o(1)}` factor is absorbed, as in
`research/keybreak-narrow-top-moment.md` §"From pairs to the moment". -/
structure ThinPairInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- `log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The same-denominator / thin-pair fraction. -/
  thin : ℕ → ℝ
  /-- The small-determinant pair fraction. -/
  smallDet : ℕ → ℝ
  /-- The thin fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The small-determinant fraction is nonnegative. -/
  smallDet_nonneg : ∀ n, 0 ≤ smallDet n
  /-- Exponent in the thin-pair envelope. -/
  cThin : ℝ
  /-- Fixed negative power of `V` in the thin-pair bound. -/
  etaThin : ℝ
  /-- The thin-pair power is genuine. -/
  etaThin_pos : 0 < etaThin
  /-- Exponent in the small-determinant envelope. -/
  cDet : ℝ
  /-- Fixed negative power of `V` in the small-determinant bound. -/
  etaDet : ℝ
  /-- The small-determinant power is genuine. -/
  etaDet_pos : 0 < etaDet
  /-- **Thin-pair bound** (`research/keybreak-thin-top-pairs.md`,
  `research/keybreak-narrow-top-moment.md` §"From pairs to the moment"): the
  same-denominator fraction is at most `D^{cThin} V^{-etaThin}`. -/
  thin_bound : ∀ n, thin n ≤ exp (cThin * scale n) * exp (-etaThin * W n)
  /-- **Small-determinant bound** (`research/keybreak-thin-top-pairs.md`): the
  small-determinant fraction is at most `D^{cDet} V^{-etaDet}`. -/
  smallDet_bound : ∀ n,
    smallDet n ≤ exp (cDet * scale n) * exp (-etaDet * W n)

namespace ThinPairInputs

variable (I : ThinPairInputs)

/-- The L19.6 deficit: the sum of the thin and small-determinant fractions. -/
noncomputable def loss (n : ℕ) : ℝ := I.thin n + I.smallDet n

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n :=
  add_nonneg (I.thin_nonneg n) (I.smallDet_nonneg n)

/-- **L19.6 subexponential statement.**  The thin and small-determinant fractions
are `D^{-B}` for every `B > 0`. -/
theorem subexpLoss : SubexpLoss I.loss := by
  apply subexpLoss_of_eventually_le
    (g := fun n => exp (I.cThin * scale n) * exp (-I.etaThin * I.W n) +
      exp (I.cDet * scale n) * exp (-I.etaDet * I.W n))
  · exact Eventually.of_forall fun n => by
      unfold loss
      exact add_le_add (I.thin_bound n) (I.smallDet_bound n)
  · exact subexpLoss_add
      (subexpLoss_exp_mul_exp_neg I.W_dominates (C := I.cThin) I.etaThin_pos)
      (subexpLoss_exp_mul_exp_neg I.W_dominates (C := I.cDet) I.etaDet_pos)

/-- **The L19.6 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.subexpLoss

/-- The `B = 2` instance is exactly the `C5Inputs.l19_6` eventuality. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    I.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.subexpLoss 2 (by norm_num)

end ThinPairInputs

/-! ## 6. The bundled L19 inputs and the three C5 slots -/

/-- The three L19 leaves as explicit input structures. -/
structure L19Inputs where
  /-- L19.4: the Poisson quotient at narrow width. -/
  poisson : PoissonQuotientInputs
  /-- L19.5: the ideal zero-mode bound. -/
  zeroMode : IdealZeroModeInputs
  /-- L19.6: thin and small-determinant pairs. -/
  thin : ThinPairInputs

/-- The three `SubexpLeaf` records produced by `L19Inputs`. -/
structure L19Leaves where
  /-- L19.4. -/
  l19_4 : SubexpLeaf
  /-- L19.5. -/
  l19_5 : SubexpLeaf
  /-- L19.6. -/
  l19_6 : SubexpLeaf

namespace L19Inputs

variable (I : L19Inputs)

/-- **L19.4 as a `SubexpLeaf`.** -/
noncomputable def leaf_poisson : SubexpLeaf := I.poisson.toSubexpLeaf

/-- **L19.5 as a `SubexpLeaf`.** -/
noncomputable def leaf_zeroMode : SubexpLeaf := I.zeroMode.toSubexpLeaf

/-- **L19.6 as a `SubexpLeaf`.** -/
noncomputable def leaf_thin : SubexpLeaf := I.thin.toSubexpLeaf

/-- The three leaves together. -/
noncomputable def leaves : L19Leaves where
  l19_4 := I.leaf_poisson
  l19_5 := I.leaf_zeroMode
  l19_6 := I.leaf_thin

/-- A partial C5 ledger: the three L19 slots are the genuine L19 losses, and all
other slots are inherited from an arbitrary ambient ledger `rest`.  This is the
only place where the other leaves enter; no L19 loss is set to zero. -/
noncomputable def slots (rest : C5LossSlots) : C5LossSlots
  | .poissonQuotient => I.poisson.loss
  | .idealZeroMode => I.zeroMode.loss
  | .thinPairs => I.thin.loss
  | k => rest k

/-- The L19.4 slot is eventually `≤ exp (-2 scale n)`. -/
theorem slots_poisson (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      I.slots rest .poissonQuotient n ≤ exp (-(2 : ℝ) * scale n) := by
  simpa only [slots] using I.poisson.slot_le

/-- The L19.5 slot is eventually `≤ exp (-2 scale n)`. -/
theorem slots_zeroMode (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      I.slots rest .idealZeroMode n ≤ exp (-(2 : ℝ) * scale n) := by
  simpa only [slots] using I.zeroMode.slot_le

/-- The L19.6 slot is eventually `≤ exp (-2 scale n)`. -/
theorem slots_thin (rest : C5LossSlots) :
    ∀ᶠ n : ℕ in atTop,
      I.slots rest .thinPairs n ≤ exp (-(2 : ℝ) * scale n) := by
  simpa only [slots] using I.thin.slot_le

/-- **The three C5 slot bounds from the L19 inputs.** -/
theorem slots_bounds (rest : C5LossSlots) :
    (∀ᶠ n : ℕ in atTop,
        I.slots rest .poissonQuotient n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.slots rest .idealZeroMode n ≤ exp (-(2 : ℝ) * scale n)) ∧
      (∀ᶠ n : ℕ in atTop,
        I.slots rest .thinPairs n ≤ exp (-(2 : ℝ) * scale n)) :=
  ⟨I.slots_poisson rest, I.slots_zeroMode rest, I.slots_thin rest⟩

end L19Inputs

/-! ## Axiom audit -/

#print axioms subexpLoss_of_eventually_le
#print axioms eventually_exp_mul_exp_neg_le
#print axioms subexpLoss_exp_mul_exp_neg
#print axioms subexpLoss_add
#print axioms subexpLoss_two_mul
#print axioms averaged_ratio_upper
#print axioms poisson_quotient_error_le
#print axioms PoissonQuotientInputs.subexpLoss_epsNum
#print axioms PoissonQuotientInputs.eventually_epsDen_le_half
#print axioms PoissonQuotientInputs.subexpLoss
#print axioms PoissonQuotientInputs.toSubexpLeaf
#print axioms PoissonQuotientInputs.slot_le
#print axioms paley_zygmund
#print axioms zero_mode_mass_lower
#print axioms diagonal_contribution_le
#print axioms IdealZeroModeInputs.zero_mode_le
#print axioms IdealZeroModeInputs.loss_le_rho
#print axioms IdealZeroModeInputs.subexpLoss
#print axioms IdealZeroModeInputs.toSubexpLeaf
#print axioms IdealZeroModeInputs.slot_le
#print axioms pruned_restoration_le
#print axioms ThinPairInputs.subexpLoss
#print axioms ThinPairInputs.toSubexpLeaf
#print axioms ThinPairInputs.slot_le
#print axioms L19Inputs.leaves
#print axioms L19Inputs.slots_bounds

end Cogentic.RandomizedL19SecondMoment
