import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedTopStripMoments

/-!
# L19.4: the Poisson numerator energy and the denominator bound

`RandomizedL19SecondMoment.PoissonQuotientInputs` records the paper's L19.4
Poisson quotient for the actual discrete Gaussian two-mark law at the narrow
width `σ = V^{1.01}`.  Its Poisson identity

  `actual n = (ν n + E n) / (1 + A n)`

and the narrow-width hypothesis `σ n = exp (W n) ^ (101 / 100)` are data of the
interface.  This file leaves both untouched and discharges the two remaining
analytic proof fields:

* **`numerator_energy`** (`|E n| ≤ E₁ n * E₂ n`) is *proved* from the existing
  multiplier-averaged coupled-mode Cauchy–Schwarz inequality
  `RandomizedTopStripMoments.coupled_mode_cauchy_schwarz`.  The only extra
  ingredient is the absolute-value form of that inequality
  (`coupled_mode_abs_bound` below): since the numerator error is the signed
  nonzero-mode sum, its absolute value is bounded by the absolute-mode sum,
  which is exactly the quantity the two marginal Parseval energies control.
  The data are packaged in `CoupledNumeratorData`, whose fields are the two
  displayed marginal energy inequalities of
  `research/keybreak-mixed-strip-moment.md` §"Second moment for the numerator",
  together with the identification of `E n` with the coupled mode sum.

* **`A_bound`** (`|A n| ≤ exp (cA * scale n) * exp (-ηA * W n)`) is *reduced* to
  the denominator estimate of `research/keybreak-mixed-strip-moment.md`
  §"Denominator of the Poisson quotient".  That note proves

  `Poisson denominator = 1 + O (V^{-c'})`,  `c' = ξ - 2ζ`,  when `2ζ < ξ`,

  where `ξ > 0` is the width-ratio separation `Q_i ≫ V^{ξ-o(1)}` of the narrow
  width `σ ≥ V^{1+ξ}` and `2ζ` is the twisted-Gaussian variation loss
  `V^{2ζ+o(1)}`.  `PoissonDenominatorData` records the retained-mode estimate
  with both exponents visible,
  `|A| ≤ D^{cDen} · V^{-ξ} · V^{2ζ}`, and

  - proves `σ n ≥ exp ((1 + ξ) W n)` from the narrow-width field
    `sigma_narrow` and `ξ ≤ 1/100` (`sigma_separation`);
  - proves `ηA = ξ - 2ζ > 0` (`etaA_pos`);
  - derives the ledger shape with `cA = cDen`, `ηA = ξ - 2ζ`
    (`denominator_le_etaA`), and also with any `0 < η ≤ ξ - 2ζ`
    (`A_bound`).

The two replacements `replaceNumerator`, `replaceDenominator`, and their
combination `replaceNumeratorAndDenominator` rebuild a `PoissonQuotientInputs`
whose Poisson identity, narrow width, marks, `ν`, and `actual` are literally
those of the original.  Consequently the existing L19.4 conclusion
(`SubexpLoss loss`, the `B = 2` C5 slot, and the `SubexpLeaf`) is available for
the rebuilt record.

Nothing is a `sorry`, an `admit`, an `axiom`, or `native_decide`; no error,
mass, count, or loss is set to zero.
-/

namespace Cogentic.RandomizedL19Poisson

open Filter Real
open scoped BigOperators
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## 1. The absolute-value coupled-mode Cauchy–Schwarz bound -/

/-- **Absolute coupled-mode bound.**  The signed coupled sum of
`coupled_mode_cauchy_schwarz` is replaced by its absolute value.  The triangle
inequality `|∑| ≤ ∑ |·|` and `|f g| = |f| |g|` reduce the claim to the same
Cauchy–Schwarz inequality applied to `|f|` and `|g|`; the marginal energies are
unchanged because `|x| ^ 2 = x ^ 2`.

This is the form in which the Poisson numerator error `E` is controlled: `E` is
a signed sum over the nonzero dual modes, while the two marginal Parseval
energies bound the absolute-mode sum. -/
theorem coupled_mode_abs_bound {Ω S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    (phases : Finset Ω) (w : Ω → ℝ) (hw : ∀ o ∈ phases, 0 ≤ w o)
    (i : S ↪ A) (j : S ↪ B) (f : Ω → A → ℝ) (g : Ω → B → ℝ)
    {E₁ E₂ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ E₂ ^ 2) :
    |∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s)| ≤ E₁ * E₂ := by
  have hf' : ∑ o ∈ phases, w o * ∑ a, |f o a| ^ 2 ≤ E₁ ^ 2 := by
    simpa only [sq_abs] using hf
  have hg' : ∑ o ∈ phases, w o * ∑ b, |g o b| ^ 2 ≤ E₂ ^ 2 := by
    simpa only [sq_abs] using hg
  have hinner : ∀ o, |∑ s, f o (i s) * g o (j s)| ≤
      ∑ s, |f o (i s)| * |g o (j s)| := by
    intro o
    simpa only [abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun s => f o (i s) * g o (j s)) Finset.univ)
  calc
    |∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s)|
        ≤ ∑ o ∈ phases, |w o * ∑ s, f o (i s) * g o (j s)| :=
      Finset.abs_sum_le_sum_abs _ phases
    _ ≤ ∑ o ∈ phases, w o * ∑ s, |f o (i s)| * |g o (j s)| := by
      apply Finset.sum_le_sum
      intro o ho
      rw [abs_mul, abs_of_nonneg (hw o ho)]
      exact mul_le_mul_of_nonneg_left (hinner o) (hw o ho)
    _ ≤ E₁ * E₂ :=
      coupled_mode_cauchy_schwarz phases w hw i j
        (fun o a => |f o a|) (fun o b => |g o b|) hE₁ hE₂ hf' hg'

/-- The absolute coupled-mode bound in the equality form used for the Poisson
numerator: if `E` is the coupled mode sum, then `|E| ≤ E₁ E₂`. -/
theorem abs_le_coupled_modes {Ω S A B : Type*} [Fintype S] [Fintype A] [Fintype B]
    (phases : Finset Ω) (w : Ω → ℝ) (hw : ∀ o ∈ phases, 0 ≤ w o)
    (i : S ↪ A) (j : S ↪ B) (f : Ω → A → ℝ) (g : Ω → B → ℝ)
    {E E₁ E₂ : ℝ} (hE : E = ∑ o ∈ phases, w o * ∑ s, f o (i s) * g o (j s))
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hf : ∑ o ∈ phases, w o * ∑ a, f o a ^ 2 ≤ E₁ ^ 2)
    (hg : ∑ o ∈ phases, w o * ∑ b, g o b ^ 2 ≤ E₂ ^ 2) :
    |E| ≤ E₁ * E₂ := by
  rw [hE]
  exact coupled_mode_abs_bound phases w hw i j f g hE₁ hE₂ hf hg

/-! ## 2. The coupled-mode numerator data and `numerator_energy` -/

/-- The concrete coupled-mode data behind the Poisson numerator error `E`.

For each ledger index `n` the dual modes form a finite phase set `phases n` with
nonnegative multiplier weights `weight n`; the two coordinates are embedded into
the two frequency grids `A` and `B` by `inj₁`, `inj₂`, and evaluated by `f n`,
`g n`.  The field `numerator_eq` identifies `I.E n` with the signed nonzero-mode
sum (the zero mode is already part of the ideal mass `ν`), and `marginal₁`,
`marginal₂` are the two displayed marginal Parseval/prefix energy inequalities
of `research/keybreak-mixed-strip-moment.md` §"Second moment for the numerator".

No analytic estimate is hidden in `E` itself: `numerator_eq` is an identity and
the two marginal fields are the paper's estimates, not the desired conclusion. -/
structure CoupledNumeratorData (I : PoissonQuotientInputs) where
  /-- The finite phase/multiplier index type. -/
  Ω : Type
  /-- The common short-mode index type. -/
  S : Type
  /-- The first frequency grid. -/
  A : Type
  /-- The second frequency grid. -/
  B : Type
  /-- The short-mode type is finite. -/
  [fintypeS : Fintype S]
  /-- The first frequency grid is finite. -/
  [fintypeA : Fintype A]
  /-- The second frequency grid is finite. -/
  [fintypeB : Fintype B]
  /-- The retained phase sets. -/
  phases : ℕ → Finset Ω
  /-- The multiplier/phase weights. -/
  weight : ℕ → Ω → ℝ
  /-- The weights are nonnegative on the retained phases. -/
  weight_nonneg : ∀ n (o : Ω), o ∈ phases n → 0 ≤ weight n o
  /-- The embedding of the short modes into the first grid. -/
  inj₁ : S ↪ A
  /-- The embedding of the short modes into the second grid. -/
  inj₂ : S ↪ B
  /-- The first coordinate array. -/
  f : ℕ → Ω → A → ℝ
  /-- The second coordinate array. -/
  g : ℕ → Ω → B → ℝ
  /-- **Poisson numerator identity**: the numerator error is the signed
  coupled sum over the nonzero dual modes. -/
  numerator_eq : ∀ n,
    I.E n = ∑ o ∈ phases n, weight n o * ∑ s, f n o (inj₁ s) * g n o (inj₂ s)
  /-- **First marginal Parseval/prefix energy** (KB G.19,
  `research/keybreak-mixed-strip-moment.md` §"Second moment for the numerator"):
  the phase-averaged squared first marginal coefficient is at most `E₁²`. -/
  marginal₁ : ∀ n,
    ∑ o ∈ phases n, weight n o * ∑ a, f n o a ^ 2 ≤ I.E₁ n ^ 2
  /-- **Second marginal Parseval/prefix energy**, as above. -/
  marginal₂ : ∀ n,
    ∑ o ∈ phases n, weight n o * ∑ b, g n o b ^ 2 ≤ I.E₂ n ^ 2

namespace CoupledNumeratorData

variable {I : PoissonQuotientInputs}

/-- **`PoissonQuotientInputs.numerator_energy`.**  The absolute Poisson
numerator error is at most the product of the two marginal energies.  This is
`coupled_mode_abs_bound` applied to the two marginal energy fields. -/
theorem numerator_energy (D : CoupledNumeratorData I) (n : ℕ) :
    |I.E n| ≤ I.E₁ n * I.E₂ n := by
  rw [D.numerator_eq n]
  exact @coupled_mode_abs_bound D.Ω D.S D.A D.B D.fintypeS D.fintypeA D.fintypeB
    (D.phases n) (D.weight n) (D.weight_nonneg n)
    D.inj₁ D.inj₂ (D.f n) (D.g n) (I.E₁ n) (I.E₂ n)
    (I.E₁_nonneg n) (I.E₂_nonneg n) (D.marginal₁ n) (D.marginal₂ n)

/-- The numerator error is a `SubexpLoss` sequence once the two marginal
energies have the critical-line `D^{O(1)} V^{-η}` decay recorded by
`E₁_bound`/`E₂_bound`.  This is the L19.2 → L19.4 scalar step for the signed
numerator itself, not just for `E₁ E₂`. -/
theorem abs_numerator_subexpLoss (D : CoupledNumeratorData I) :
    SubexpLoss (fun n => |I.E n|) := by
  refine subexpLoss_of_eventually_le (g := I.epsNum)
    (Eventually.of_forall ?_) I.subexpLoss_epsNum
  intro n
  simpa only [PoissonQuotientInputs.epsNum] using D.numerator_energy n

end CoupledNumeratorData

/-! ## 3. The denominator data and `A_bound` -/

/-- The explicit denominator data of `research/keybreak-mixed-strip-moment.md`
§"Denominator of the Poisson quotient".

`ξ > 0` is the width-ratio separation exponent of the narrow width
(`σ ≥ V^{1+ξ}`, proved below from `σ = V^{1.01}` and `ξ ≤ 1/100`), `ζ ≥ 0` is
the twisted-Gaussian variation exponent, and `2ζ < ξ` is the genuine gain of the
note.  The field `denominator_raw` is the note's retained-mode estimate

  `|A n| ≤ D^{cDen} · V^{-ξ} · V^{2ζ}`,

i.e. each nonzero mode costs `V^{-ξ}` and the mode count/variation costs
`V^{2ζ}`.  The discarded Fourier tail is superpolynomially small in the note and
is absorbed in the `D^{cDen}` factor.  Nothing is bounded by zero. -/
structure PoissonDenominatorData (I : PoissonQuotientInputs) where
  /-- Width-ratio separation exponent `ξ > 0` (the note's `Q_i ≫ V^{ξ-o(1)}`). -/
  xi : ℝ
  /-- The separation exponent is positive. -/
  xi_pos : 0 < xi
  /-- The narrow width `σ = V^{101/100}` supplies any separation `ξ ≤ 1/100`. -/
  xi_le_narrow : xi ≤ 1 / 100
  /-- Twisted-Gaussian variation exponent `ζ`. -/
  zeta : ℝ
  /-- The variation exponent is nonnegative. -/
  zeta_nonneg : 0 ≤ zeta
  /-- **Denominator gain**: `2ζ < ξ`, the condition under which the note
  concludes `1 + O(V^{-(ξ-2ζ)})`. -/
  variation_gap : 2 * zeta < xi
  /-- Exponent of `D` in the retained-mode denominator envelope. -/
  cDen : ℝ
  /-- **Retained-mode denominator estimate** (KB G.19,
  `research/keybreak-mixed-strip-moment.md` §"Denominator of the Poisson
  quotient"): the mode sum is `V^{-ξ+2ζ+o(1)}`, with the `o(1)` absorbed in the
  `D^{cDen}` factor. -/
  denominator_raw : ∀ n,
    |I.A n| ≤
      exp (cDen * scale n) * exp (-xi * I.W n) * exp (2 * zeta * I.W n)

namespace PoissonDenominatorData

variable {I : PoissonQuotientInputs}

/-- The denominator decay exponent `ηA = ξ - 2ζ`. -/
noncomputable def etaA (D : PoissonDenominatorData I) : ℝ := D.xi - 2 * D.zeta

/-- **`ηA > 0`.**  This is exactly the note's condition `2ζ < ξ`. -/
theorem etaA_pos (D : PoissonDenominatorData I) : 0 < D.etaA := by
  unfold etaA
  linarith only [D.variation_gap]

/-- **The narrow-width separation `σ ≥ V^{1+ξ}`.**  The interface's narrow width
`σ = exp W ^ (101/100)` and `ξ ≤ 1/100` give
`exp ((1 + ξ) W) ≤ σ` for `W ≥ 0`.  This keeps the narrow-width hypothesis
explicit and shows that the denominator data uses the actual L19 width. -/
theorem sigma_separation (D : PoissonDenominatorData I) (n : ℕ) :
    exp ((1 + D.xi) * I.W n) ≤ I.sigma n := by
  have hW := I.W_nonneg n
  have hmul : D.xi * I.W n ≤ (1 / 100 : ℝ) * I.W n :=
    mul_le_mul_of_nonneg_right D.xi_le_narrow hW
  have hexp : exp ((1 + D.xi) * I.W n) ≤ exp ((101 / 100 : ℝ) * I.W n) := by
    apply exp_le_exp.mpr
    nlinarith only [hmul]
  calc
    exp ((1 + D.xi) * I.W n) ≤ exp ((101 / 100 : ℝ) * I.W n) := hexp
    _ = exp (I.W n * (101 / 100 : ℝ)) := by ring_nf
    _ = exp (I.W n) ^ (101 / 100 : ℝ) := Real.exp_mul _ _
    _ = I.sigma n := (I.sigma_narrow n).symm

/-- **The denominator bound with `ηA = ξ - 2ζ`.**  Combining
`exp (-ξ W) · exp (2ζ W) = exp (-(ξ - 2ζ) W)` turns the retained-mode estimate
into the ledger shape with `cA = cDen` and `ηA = ξ - 2ζ`. -/
theorem denominator_le_etaA (D : PoissonDenominatorData I) (n : ℕ) :
    |I.A n| ≤ exp (D.cDen * scale n) * exp (-D.etaA * I.W n) := by
  have hfac : exp (-D.xi * I.W n) * exp (2 * D.zeta * I.W n) =
      exp (-(D.xi - 2 * D.zeta) * I.W n) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    |I.A n| ≤ exp (D.cDen * scale n) * exp (-D.xi * I.W n) *
        exp (2 * D.zeta * I.W n) := D.denominator_raw n
    _ = exp (D.cDen * scale n) *
        (exp (-D.xi * I.W n) * exp (2 * D.zeta * I.W n)) := by ring
    _ = exp (D.cDen * scale n) * exp (-(D.xi - 2 * D.zeta) * I.W n) := by
      rw [hfac]
    _ = exp (D.cDen * scale n) * exp (-D.etaA * I.W n) := by
      simp only [etaA]

/-- **`A_bound` with any exponent `0 < η ≤ ξ - 2ζ`.**  Weakening the decay
exponent only weakens the envelope because `W ≥ 0`
(`exp (-(ξ-2ζ) W) ≤ exp (-η W)`), so every admissible `η` gives the ledger
shape. -/
theorem A_bound (D : PoissonDenominatorData I) {η : ℝ} (_hη : 0 < η)
    (hle : η ≤ D.etaA) (n : ℕ) :
    |I.A n| ≤ exp (D.cDen * scale n) * exp (-η * I.W n) := by
  refine (D.denominator_le_etaA n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  apply exp_le_exp.mpr
  have hW := I.W_nonneg n
  have hmul : η * I.W n ≤ D.etaA * I.W n :=
    mul_le_mul_of_nonneg_right hle hW
  linarith only [hmul]

/-- **`PoissonQuotientInputs.A_bound`.**  The denominator error has the exact
ledger shape with `cA = cDen`, `ηA = ξ - 2ζ > 0`. -/
theorem A_bound_etaA (D : PoissonDenominatorData I) :
    ∀ n, |I.A n| ≤ exp (D.cDen * scale n) * exp (-D.etaA * I.W n) :=
  fun n => D.denominator_le_etaA n

/-- The denominator error is a `SubexpLoss` sequence: the `D^{cDen}` factor is
absorbed by `W` dominating every fixed multiple of the ledger scale. -/
theorem abs_A_subexpLoss (D : PoissonDenominatorData I) :
    SubexpLoss (fun n => |I.A n|) := by
  refine subexpLoss_of_eventually_le
    (g := fun n => exp (D.cDen * scale n) * exp (-D.etaA * I.W n))
    (Eventually.of_forall D.A_bound_etaA) ?_
  exact subexpLoss_exp_mul_exp_neg I.W_dominates (C := D.cDen) D.etaA_pos

end PoissonDenominatorData

end Cogentic.RandomizedL19Poisson

/-! ## 4. Literal replacement of `numerator_energy` and `A_bound` -/

namespace Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs

open Filter
open Real
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements

variable (I : PoissonQuotientInputs)

/-- **Replace `numerator_energy` by the coupled-mode certificate.**  The
Poisson identity, narrow width, marks, `ν`, and `actual` are unchanged. -/
noncomputable def replaceNumerator (D : CoupledNumeratorData I) :
    PoissonQuotientInputs :=
  { I with numerator_energy := fun n => D.numerator_energy n }

/-- **Replace `A_bound` by the denominator certificate**, with the paper's
exponents `cA = cDen` and `ηA = ξ - 2ζ`. -/
noncomputable def replaceDenominator (D : PoissonDenominatorData I) :
    PoissonQuotientInputs :=
  { I with
    cA := D.cDen
    ηA := D.etaA
    ηA_pos := D.etaA_pos
    A_bound := fun n => D.denominator_le_etaA n }

/-- **Replace both analytic fields at once.** -/
noncomputable def replaceNumeratorAndDenominator
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) :
    PoissonQuotientInputs :=
  { I with
    numerator_energy := fun n => Dnum.numerator_energy n
    cA := Dden.cDen
    ηA := Dden.etaA
    ηA_pos := Dden.etaA_pos
    A_bound := fun n => Dden.denominator_le_etaA n }

/-- The actual pair probability is untouched by the numerator replacement. -/
@[simp] theorem replaceNumerator_actual (D : CoupledNumeratorData I) :
    (I.replaceNumerator D).actual = I.actual := rfl

/-- The Poisson denominator error is untouched by the numerator replacement. -/
@[simp] theorem replaceNumerator_A (D : CoupledNumeratorData I) :
    (I.replaceNumerator D).A = I.A := rfl

/-- The ideal mass is untouched by the numerator replacement. -/
@[simp] theorem replaceNumerator_nu (D : CoupledNumeratorData I) :
    (I.replaceNumerator D).nu = I.nu := rfl

/-- The narrow width is untouched by the numerator replacement. -/
@[simp] theorem replaceNumerator_sigma (D : CoupledNumeratorData I) :
    (I.replaceNumerator D).sigma = I.sigma := rfl

/-- The L19.4 loss is untouched by the numerator replacement. -/
@[simp] theorem replaceNumerator_loss (D : CoupledNumeratorData I) :
    (I.replaceNumerator D).loss = I.loss := rfl

/-- The actual pair probability is untouched by the denominator replacement. -/
@[simp] theorem replaceDenominator_actual (D : PoissonDenominatorData I) :
    (I.replaceDenominator D).actual = I.actual := rfl

/-- The numerator error is untouched by the denominator replacement. -/
@[simp] theorem replaceDenominator_E (D : PoissonDenominatorData I) :
    (I.replaceDenominator D).E = I.E := rfl

/-- The L19.4 loss is untouched by the denominator replacement. -/
@[simp] theorem replaceDenominator_loss (D : PoissonDenominatorData I) :
    (I.replaceDenominator D).loss = I.loss := rfl

/-- **The Poisson identity survives the replacement.**  The rebuilt record
satisfies `actual = (ν + E) / (1 + A)` with its own fields, exactly as the
original. -/
theorem replaceNumeratorAndDenominator_poisson_identity
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) (n : ℕ) :
    (I.replaceNumeratorAndDenominator Dnum Dden).actual n =
      ((I.replaceNumeratorAndDenominator Dnum Dden).nu n +
        (I.replaceNumeratorAndDenominator Dnum Dden).E n) /
        (1 + (I.replaceNumeratorAndDenominator Dnum Dden).A n) :=
  (I.replaceNumeratorAndDenominator Dnum Dden).actual_eq n

/-- **The narrow-width hypothesis survives the replacement.** -/
theorem replaceNumeratorAndDenominator_sigma_narrow
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) (n : ℕ) :
    (I.replaceNumeratorAndDenominator Dnum Dden).sigma n =
      exp ((I.replaceNumeratorAndDenominator Dnum Dden).W n) ^
        (101 / 100 : ℝ) :=
  (I.replaceNumeratorAndDenominator Dnum Dden).sigma_narrow n

/-- **The denominator is eventually below `1/2`**, so the Poisson quotient is
uniformly well defined.  This uses the derived `A_bound` and the existing
`eventually_epsDen_le_half`. -/
theorem replaceNumeratorAndDenominator_eventually_abs_A_le_half
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) :
    ∀ᶠ n : ℕ in atTop,
      |(I.replaceNumeratorAndDenominator Dnum Dden).A n| ≤ 1 / 2 := by
  filter_upwards [(I.replaceNumeratorAndDenominator Dnum Dden).eventually_epsDen_le_half]
    with n hn
  exact ((I.replaceNumeratorAndDenominator Dnum Dden).A_bound n).trans hn

/-- **L19.4 survives the numerator replacement.** -/
theorem replaceNumerator_subexpLoss (D : CoupledNumeratorData I) :
    SubexpLoss (I.replaceNumerator D).loss :=
  (I.replaceNumerator D).subexpLoss

/-- **L19.4 survives the denominator replacement.** -/
theorem replaceDenominator_subexpLoss (D : PoissonDenominatorData I) :
    SubexpLoss (I.replaceDenominator D).loss :=
  (I.replaceDenominator D).subexpLoss

/-- **L19.4 survives both replacements.** -/
theorem replaceNumeratorAndDenominator_subexpLoss
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) :
    SubexpLoss (I.replaceNumeratorAndDenominator Dnum Dden).loss :=
  (I.replaceNumeratorAndDenominator Dnum Dden).subexpLoss

/-- The `B = 2` C5 slot for the fully rebuilt record. -/
theorem replaceNumeratorAndDenominator_slot_le
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) :
    ∀ᶠ n : ℕ in atTop,
      (I.replaceNumeratorAndDenominator Dnum Dden).loss n ≤
        exp (-(2 : ℝ) * scale n) :=
  (I.replaceNumeratorAndDenominator Dnum Dden).slot_le

/-- The fully rebuilt record as an L19.4 `SubexpLeaf`. -/
noncomputable def replaceNumeratorAndDenominator_toSubexpLeaf
    (Dnum : CoupledNumeratorData I) (Dden : PoissonDenominatorData I) :
    SubexpLeaf :=
  (I.replaceNumeratorAndDenominator Dnum Dden).toSubexpLeaf

end Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs

namespace Cogentic.RandomizedL19Poisson

/-! ## Axiom audit -/

#print axioms coupled_mode_abs_bound
#print axioms abs_le_coupled_modes
#print axioms CoupledNumeratorData.numerator_energy
#print axioms CoupledNumeratorData.abs_numerator_subexpLoss
#print axioms PoissonDenominatorData.etaA_pos
#print axioms PoissonDenominatorData.sigma_separation
#print axioms PoissonDenominatorData.denominator_le_etaA
#print axioms PoissonDenominatorData.A_bound
#print axioms PoissonDenominatorData.A_bound_etaA
#print axioms PoissonDenominatorData.abs_A_subexpLoss
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumerator
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceDenominator
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_poisson_identity
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_sigma_narrow
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_eventually_abs_A_le_half
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumerator_subexpLoss
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceDenominator_subexpLoss
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_subexpLoss
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_slot_le
#print axioms Cogentic.RandomizedL19SecondMoment.PoissonQuotientInputs.replaceNumeratorAndDenominator_toSubexpLeaf

end Cogentic.RandomizedL19Poisson
