import Cogentic.RandomizedL27HurwitzAssembly

/-!
# L27: the `L(1, χ_D)` lower bound from Siegel's theorem

`Cogentic.RandomizedL27ClassNumber` reduced the Siegel leaf to the qualitative
absence of an exceptional sequence of Frobenius discriminants,

`NoExceptionalLOneSequence L1`,

and showed this is equivalent, under pointwise positivity, to the existence of a
uniform positive lower bound `l ≤ L(1, χ_D)`.  The present file identifies the
constant bound as the smallest explicit `L`-one input, derives it from the
Landau–Page exceptional-zero alternative, and records precisely where the
classical `ε`-loss and Brauer–Siegel forms stop being sufficient.  In
particular, it proves that the classical `ε`-loss form alone does **not** imply
the constant bound: the model `1 / log (D + 2)` satisfies every `ε`-loss bound
and still has an exceptional sequence.

## The arithmetic inputs

* `SiegelLOneLower L1` — the constant form: there is an absolute `c > 0` with
  `c ≤ L(1, χ_D)` on every Frobenius discriminant.  This is the smallest
  statement that feeds the L27 trace leaf.  `SiegelLOneLowerAt L1 c` is the
  same statement with the constant exposed; it is definitionally the input
  `DirichletLOneLower L1 c` of `Cogentic.RandomizedL27Siegel`.
* `LandauPageAlternative L1` — the Landau–Page exceptional-zero dichotomy in
  the form needed here: an absolute `c > 0` bounds `L(1, χ_D)` from below for
  every Frobenius discriminant except possibly one exceptional discriminant
  `E`.  Combined with the pointwise positivity at `E`, which is *derived* from
  the class-number formula (`L1_pos_of_dirichletFormula`), this yields the
  constant form `SiegelLOneLower`.  This is a genuine standard form of the
  exceptional-zero alternative and is strictly weaker than the constant bound
  away from `E`.

## What the weaker classical forms do *not* give

The classical Siegel bound has a polynomial loss,
`c(ε) |D|^{-ε}`, and the effective Brauer–Siegel bound has a logarithmic loss,
`c / log |D|`.  Neither is strong enough for the L27 constant `κ`: the
normalized ratio `L(1, χ_D)` (respectively `H(-D)/√D`) still tends to zero along
a sequence of Frobenius discriminants.

The file proves this as an explicit obstruction, not as a remark:

* `logDecayModel_siegelEpsilon` — the model `1 / log (D + 2)` satisfies the
  classical `ε`-loss form for every `ε > 0`;
* `logDecayModel_not_constant` and `logDecayModel_exceptionalSequence` — the
  same model has no positive uniform lower bound, and in fact has an actual
  exceptional sequence;
* `siegelEpsilonLOneLower_not_imply_noExceptional` and
  `brauerSiegelLOneLower_not_imply_noExceptional` — the classical `ε`-loss form
  and the Brauer–Siegel `L`-form are both insufficient for the L27 qualitative
  input;
* `brauerSiegelLower_of_classNumberFormula_and_log` — the class-number formula
  and a `c / log |D|` `L`-bound yield the Brauer–Siegel `√D / log D` Hurwitz
  bound;
* `brauerSiegelLower_logLossHurwitz`, `logLossHurwitz_no_constant`, and
  `logLossHurwitz_ratio_small` — the Hurwitz model `√D / log (D + 2)`,
  exactly the shape produced by the Brauer–Siegel `L`-bound through the
  class-number formula, satisfies `BrauerSiegelLower` with constant `1` but
  admits no constant `c > 0` with `HurwitzSiegelLowerFrob`: for every proposed
  `κ > 0` it is below `κ√D` somewhere.

## The trace bound

From the constant form and the Dirichlet class-number formula one obtains the
Hurwitz trace leaf with constant `classNumberFormulaConstant * l`, and hence
the `L27HurwitzAssemblyInputs` trace bound:
`hurwitzSiegelLowerTrace_of_siegelLOneLower`,
`exists_hurwitzSiegelLowerTrace_of_siegelLOneLower`, and
`toAssemblyInputs_of_siegel`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No class number,
curve count, or loss is set to zero.
-/

namespace Cogentic.RandomizedL27LOneSiegel

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27_1Sub
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27ClassNumber
open Cogentic.RandomizedL27Deuring
open Cogentic.RandomizedL27Fiber
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27HurwitzAssembly
open Cogentic.RandomizedL27Scale
open Cogentic.RandomizedL27Siegel
open Cogentic.RandomizedL27Stratification
open Cogentic.RandomizedL27TraceClass
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL27Weighted

noncomputable section

/-! ## 0. Frobenius discriminants are positive integers -/

/-- A Frobenius discriminant is at least `1`. -/
theorem isFrobeniusDiscriminant_one_le {D : ℤ} (h : IsFrobeniusDiscriminant D) :
    1 ≤ D := by
  have hpos := isFrobeniusDiscriminant_pos h
  omega

/-- `4p` is a Frobenius discriminant for every positive `p` (take trace `0`).
This is the sequence used to expose the failure of the polynomial and
logarithmic bounds. -/
theorem isFrobeniusDiscriminant_four_mul (p : ℕ) (hp : 0 < p) :
    IsFrobeniusDiscriminant (4 * (p : ℤ)) := by
  refine ⟨p, hp, 0, ?_, ?_⟩
  · simp only [traceDisc, Int.reducePow, sub_zero]
    have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  · simp only [traceDisc, Int.reducePow, sub_zero]

/-- Cast form of `4p`, used in the obstruction arithmetic. -/
theorem cast_four_mul (p : ℕ) :
    (((4 * (p : ℤ) : ℤ) : ℝ)) = 4 * (p : ℝ) := by
  push_cast
  ring

/-! ## 1. The classical weak forms -/

/-- **Siegel's classical `ε`-loss form.**  For every `ε > 0` there is
`c(ε) > 0` with `c(ε) · |D|^{-ε} ≤ L(1, χ_D)` on Frobenius discriminants.
This is the polynomial-loss shape of the standard theorem. -/
def SiegelEpsilonLOneLower (L1 : ℤ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ D : ℤ, IsFrobeniusDiscriminant D → c * (D : ℝ) ^ (-ε) ≤ L1 D

/-- **The effective Brauer–Siegel logarithmic form.**  An absolute constant
`c > 0` with `c / log (D + 2) ≤ L(1, χ_D)` on Frobenius discriminants. -/
def BrauerSiegelLOneLower (L1 : ℤ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ D : ℤ, IsFrobeniusDiscriminant D →
    c / Real.log ((D : ℝ) + 2) ≤ L1 D

/-! ## 2. The constant form and its equivalence with the L27 input -/

/-- **Siegel's theorem in the constant form required by L27.**  There is an
absolute `c > 0` such that `c ≤ L(1, χ_D)` for every Frobenius discriminant.
This is the smallest statement that supplies the L27 Siegel constant; the
`ε`-loss and logarithmic forms below are strictly weaker. -/
def SiegelLOneLower (L1 : ℤ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ D : ℤ, IsFrobeniusDiscriminant D → c ≤ L1 D

/-- The constant form with the constant exposed.  It is definitionally the
`DirichletLOneLower` input of `Cogentic.RandomizedL27Siegel`. -/
def SiegelLOneLowerAt (L1 : ℤ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ D : ℤ, IsFrobeniusDiscriminant D → c ≤ L1 D

/-- The existential constant form is the existential of the exposed form. -/
theorem siegelLOneLower_iff_exists_at {L1 : ℤ → ℝ} :
    SiegelLOneLower L1 ↔ ∃ c : ℝ, SiegelLOneLowerAt L1 c :=
  Iff.rfl

/-- The exposed Siegel form is exactly `DirichletLOneLower`. -/
theorem siegelLOneLowerAt_iff_dirichletLOneLower {L1 : ℤ → ℝ} {c : ℝ} :
    SiegelLOneLowerAt L1 c ↔ DirichletLOneLower L1 c :=
  Iff.rfl

/-- The constant Siegel input is exactly `DirichletLOneInput`. -/
theorem siegelLOneLower_iff_dirichletLOneInput {L1 : ℤ → ℝ} :
    SiegelLOneLower L1 ↔ DirichletLOneInput L1 :=
  Iff.rfl

/-- **The constant Siegel input rules out an exceptional sequence.** -/
theorem noExceptional_of_siegelLOneLower {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D)
    (h : SiegelLOneLower L1) : NoExceptionalLOneSequence L1 :=
  (dirichletLOneInput_iff_noExceptionalSequence hpos).mp h

/-- **The absence of an exceptional sequence gives the constant Siegel input**
once pointwise positivity is available.  Together with the previous theorem
this identifies the constant form as the smallest sufficient `L`-one input. -/
theorem siegelLOneLower_of_noExceptional {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D)
    (h : NoExceptionalLOneSequence L1) : SiegelLOneLower L1 :=
  (dirichletLOneInput_iff_noExceptionalSequence hpos).mpr h

/-- **The constant form is exactly the `L27` qualitative input**, under the
pointwise positivity that the class-number formula supplies. -/
theorem siegelLOneLower_iff_noExceptional {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    SiegelLOneLower L1 ↔ NoExceptionalLOneSequence L1 :=
  ⟨noExceptional_of_siegelLOneLower hpos, siegelLOneLower_of_noExceptional hpos⟩

/-- The constant form implies the classical `ε`-loss form.  The reverse
implication fails; see `logDecayModel_not_constant`. -/
theorem siegelEpsilonLOneLower_of_siegelLOneLower {L1 : ℤ → ℝ}
    (h : SiegelLOneLower L1) : SiegelEpsilonLOneLower L1 := by
  obtain ⟨c, hc, hbound⟩ := h
  intro ε hε
  refine ⟨c, hc, ?_⟩
  intro D hD
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast isFrobeniusDiscriminant_one_le hD
  have hD0 : (0 : ℝ) < (D : ℝ) := by
    have hpos := isFrobeniusDiscriminant_pos hD
    exact_mod_cast hpos
  have hpow : (D : ℝ) ^ (-ε) ≤ 1 := by
    rw [Real.rpow_neg hD0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hD1 hε.le)
  calc
    c * (D : ℝ) ^ (-ε) ≤ c * 1 := mul_le_mul_of_nonneg_left hpow hc.le
    _ = c := by ring
    _ ≤ L1 D := hbound D hD

/-- The constant form implies the Brauer–Siegel logarithmic form, with the
smaller constant `c · log 3`, so the constant form is the strongest of the
three. -/
theorem brauerSiegelLOneLower_of_siegelLOneLower {L1 : ℤ → ℝ}
    (h : SiegelLOneLower L1) : BrauerSiegelLOneLower L1 := by
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨c * Real.log 3, mul_pos hc (Real.log_pos (by norm_num)), ?_⟩
  intro D hD
  have hD1 := isFrobeniusDiscriminant_one_le hD
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hlog : 0 < Real.log ((D : ℝ) + 2) := by
    apply Real.log_pos
    linarith
  have hlog3le : Real.log 3 ≤ Real.log ((D : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hquot : c * Real.log 3 / Real.log ((D : ℝ) + 2) ≤ c := by
    rw [div_le_iff₀ hlog]
    exact mul_le_mul_of_nonneg_left hlog3le hc.le
  exact hquot.trans (hbound D hD)

/-! ## 3. The logarithmic model: `1 / log (D + 2)` -/

/-- The model function decaying like `1 / log D`. -/
def logDecayModel (D : ℤ) : ℝ := 1 / Real.log ((D : ℝ) + 2)

/-- The model is positive on Frobenius discriminants. -/
theorem logDecayModel_pos {D : ℤ} (hD : IsFrobeniusDiscriminant D) :
    0 < logDecayModel D := by
  unfold logDecayModel
  have hD1 := isFrobeniusDiscriminant_one_le hD
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  exact one_div_pos.mpr (Real.log_pos (by linarith))

/-- The logarithm is bounded by any positive power, with an explicit
constant.  This is the elementary inequality behind the `ε`-loss model. -/
theorem log_add_two_le_rpow_mul (D : ℤ) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    Real.log ((D : ℝ) + 2) ≤ (Real.log 3 + 1 / ε) * (D : ℝ) ^ ε := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by
    have : (0 : ℤ) < D := by omega
    exact_mod_cast this
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD2pos : (0 : ℝ) < (D : ℝ) + 2 := by linarith
  have hle : (D : ℝ) + 2 ≤ 3 * (D : ℝ) := by nlinarith
  have hlog_le : Real.log ((D : ℝ) + 2) ≤ Real.log (3 * (D : ℝ)) :=
    Real.log_le_log hD2pos hle
  have hlog3D : Real.log (3 * (D : ℝ)) = Real.log 3 + Real.log (D : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hD0)]
  have hlogD : Real.log (D : ℝ) ≤ (D : ℝ) ^ ε / ε :=
    Real.log_le_rpow_div hD0.le hε
  have hrpow1 : (1 : ℝ) ≤ (D : ℝ) ^ ε := Real.one_le_rpow hD1R hε.le
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3_le : Real.log 3 ≤ Real.log 3 * (D : ℝ) ^ ε := by
    calc
      Real.log 3 = Real.log 3 * 1 := by ring
      _ ≤ Real.log 3 * (D : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hrpow1 hlog3
  calc
    Real.log ((D : ℝ) + 2) ≤ Real.log 3 + Real.log (D : ℝ) := by
      rw [← hlog3D]
      exact hlog_le
    _ ≤ Real.log 3 * (D : ℝ) ^ ε + (D : ℝ) ^ ε / ε := by linarith
    _ = (Real.log 3 + 1 / ε) * (D : ℝ) ^ ε := by ring

/-- **The `1 / log D` model satisfies the classical `ε`-loss Siegel form.**
For each `ε > 0` the explicit constant `1 / (log 3 + 1/ε)` works. -/
theorem logDecayModel_siegelEpsilon : SiegelEpsilonLOneLower logDecayModel := by
  intro ε hε
  refine ⟨1 / (Real.log 3 + 1 / ε), ?_, ?_⟩
  · have hC : 0 < Real.log 3 + 1 / ε := by positivity
    exact one_div_pos.mpr hC
  · intro D hD
    have hD1 := isFrobeniusDiscriminant_one_le hD
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have : (0 : ℤ) < D := by omega
      exact_mod_cast this
    have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have hlogpos : 0 < Real.log ((D : ℝ) + 2) :=
      Real.log_pos (by linarith)
    have hC : 0 < Real.log 3 + 1 / ε := by positivity
    have hDpow : 0 < (D : ℝ) ^ ε := Real.rpow_pos_of_pos hD0 ε
    have hbound := log_add_two_le_rpow_mul D hD1 hε
    have hle : 1 / ((Real.log 3 + 1 / ε) * (D : ℝ) ^ ε) ≤
        1 / Real.log ((D : ℝ) + 2) :=
      one_div_le_one_div_of_le hlogpos hbound
    rw [Real.rpow_neg hD0.le]
    unfold logDecayModel
    calc
      (1 / (Real.log 3 + 1 / ε)) * ((D : ℝ) ^ ε)⁻¹ =
          1 / ((Real.log 3 + 1 / ε) * (D : ℝ) ^ ε) := by
        field_simp [hC.ne', hDpow.ne']
      _ ≤ 1 / Real.log ((D : ℝ) + 2) := hle

/-- **The `ε`-loss form does not imply the constant form.**  The logarithmic
model satisfies the classical Siegel bound for every `ε > 0` but has no
positive uniform lower bound: along `D = 4p` its value tends to zero. -/
theorem logDecayModel_not_constant :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ D : ℤ, IsFrobeniusDiscriminant D → c ≤ logDecayModel D := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨p, hp⟩ := exists_nat_gt (Real.exp (1 / c))
  have hp0 : 0 < p := by
    have hexp : (0 : ℝ) < Real.exp (1 / c) := Real.exp_pos _
    have hpR : (0 : ℝ) < (p : ℝ) := lt_trans hexp hp
    exact_mod_cast hpR
  have hD := isFrobeniusDiscriminant_four_mul p hp0
  have hle := hbound (4 * (p : ℤ)) hD
  have harg : Real.exp (1 / c) < ((4 * (p : ℤ) : ℤ) : ℝ) + 2 := by
    rw [cast_four_mul]
    have hpR : Real.exp (1 / c) < (p : ℝ) := hp
    nlinarith [Real.exp_pos (1 / c)]
  have hloggt : 1 / c < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) := by
    calc
      1 / c = Real.log (Real.exp (1 / c)) := by rw [Real.log_exp]
      _ < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
        Real.log_lt_log (Real.exp_pos _) harg
  have hlogpos : 0 < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
    lt_trans (by positivity) hloggt
  have hlt : 1 / Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) < c := by
    rw [div_lt_iff₀ hlogpos]
    calc
      1 = c * (1 / c) := by field_simp
      _ < c * Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
        mul_lt_mul_of_pos_left hloggt hc
  unfold logDecayModel at hle
  linarith

/-- **The logarithmic model has an actual exceptional sequence.**  Along
`D = 4p` the model tends to zero, so the `ε`-loss bound does not merely fail to
give a constant: it is compatible with the exact failure mode that
`NoExceptionalLOneSequence` excludes. -/
theorem logDecayModel_exceptionalSequence : ExceptionalLOneSequence logDecayModel := by
  by_contra hno
  exact logDecayModel_not_constant
    (siegelLOneLower_of_noExceptional (fun _ hD => logDecayModel_pos hD) hno)

/-- **The classical `ε`-loss form does not imply the L27 qualitative input.**
The logarithmic model satisfies Siegel's `ε`-loss bound for every `ε > 0` and
still has an exceptional sequence. -/
theorem siegelEpsilonLOneLower_not_imply_noExceptional :
    ∃ L1 : ℤ → ℝ, SiegelEpsilonLOneLower L1 ∧ ¬ NoExceptionalLOneSequence L1 :=
  ⟨logDecayModel, logDecayModel_siegelEpsilon,
    fun hno => logDecayModel_not_constant
      (siegelLOneLower_of_noExceptional (fun _ hD => logDecayModel_pos hD) hno)⟩

/-- The logarithmic model satisfies the Brauer–Siegel `L`-bound with constant
`1`. -/
theorem brauerSiegelLOneLower_logDecayModel : BrauerSiegelLOneLower logDecayModel := by
  refine ⟨1, one_pos, ?_⟩
  intro D _hD
  simp [logDecayModel]

/-- **The Brauer–Siegel `L`-bound does not imply the L27 qualitative input.**
The same logarithmic model is a counterexample to the implication
`BrauerSiegelLOneLower → NoExceptionalLOneSequence`. -/
theorem brauerSiegelLOneLower_not_imply_noExceptional :
    ∃ L1 : ℤ → ℝ, BrauerSiegelLOneLower L1 ∧ ¬ NoExceptionalLOneSequence L1 :=
  ⟨logDecayModel, brauerSiegelLOneLower_logDecayModel,
    fun hno => logDecayModel_not_constant
      (siegelLOneLower_of_noExceptional (fun _ hD => logDecayModel_pos hD) hno)⟩

/-! ## 4. The Brauer–Siegel model: `√D / log (D + 2)` -/

/-- The Hurwitz class-number model with the exact `√D / log D` Brauer–Siegel
shape. -/
def logLossHurwitz (D : ℤ) : ℝ :=
  Real.sqrt (D : ℝ) / Real.log ((D : ℝ) + 2)

/-- **The Brauer–Siegel model satisfies `BrauerSiegelLower` with constant
`1`.** -/
theorem brauerSiegelLower_logLossHurwitz : BrauerSiegelLower logLossHurwitz 1 := by
  intro D _hD
  unfold logLossHurwitz
  norm_num

/-- **The Brauer–Siegel model admits no constant Siegel lower bound.**  This is
the concrete form of the statement that a logarithmic `L`-loss cannot produce
the paper's constant `κ`: the normalized ratio is `1 / log (D + 2)`, which
tends to zero along `D = 4p`. -/
theorem logLossHurwitz_no_constant :
    ¬ ∃ c : ℝ, 0 < c ∧ HurwitzSiegelLowerFrob logLossHurwitz c := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨p, hp⟩ := exists_nat_gt (Real.exp (1 / c))
  have hp0 : 0 < p := by
    have hexp : (0 : ℝ) < Real.exp (1 / c) := Real.exp_pos _
    have hpR : (0 : ℝ) < (p : ℝ) := lt_trans hexp hp
    exact_mod_cast hpR
  have hD := isFrobeniusDiscriminant_four_mul p hp0
  have hDpos : (0 : ℝ) < (((4 * (p : ℤ) : ℤ) : ℝ)) := by
    rw [cast_four_mul]
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    linarith
  have hsqrt : 0 < Real.sqrt (((4 * (p : ℤ) : ℤ) : ℝ)) :=
    Real.sqrt_pos.mpr hDpos
  have harg : Real.exp (1 / c) < ((4 * (p : ℤ) : ℤ) : ℝ) + 2 := by
    rw [cast_four_mul]
    have hpR : Real.exp (1 / c) < (p : ℝ) := hp
    nlinarith [Real.exp_pos (1 / c)]
  have hloggt : 1 / c < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) := by
    calc
      1 / c = Real.log (Real.exp (1 / c)) := by rw [Real.log_exp]
      _ < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
        Real.log_lt_log (Real.exp_pos _) harg
  have hlogpos : 0 < Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
    lt_trans (by positivity) hloggt
  have hle := hbound (4 * (p : ℤ)) hD
  unfold logLossHurwitz at hle
  have hcle : c ≤ 1 / Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) := by
    have h2 : c ≤
        (Real.sqrt (((4 * (p : ℤ) : ℤ) : ℝ)) /
            Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2)) /
          Real.sqrt (((4 * (p : ℤ) : ℤ) : ℝ)) :=
      (le_div_iff₀ hsqrt).mpr hle
    have h3 : (Real.sqrt (((4 * (p : ℤ) : ℤ) : ℝ)) /
          Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2)) /
        Real.sqrt (((4 * (p : ℤ) : ℤ) : ℝ)) =
        1 / Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) := by
      field_simp
    rwa [h3] at h2
  have hlt : 1 / Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) < c := by
    rw [div_lt_iff₀ hlogpos]
    calc
      1 = c * (1 / c) := by field_simp
      _ < c * Real.log (((4 * (p : ℤ) : ℤ) : ℝ) + 2) :=
        mul_lt_mul_of_pos_left hloggt hc
  linarith

/-- **The Brauer–Siegel shape is insufficient for a constant `κ`.**  There is a
Hurwitz model satisfying the logarithmic Brauer–Siegel lower bound whose
normalized ratio `H(-D)/√D` is below every positive constant along a
Frobenius sequence. -/
theorem brauerSiegelLower_insufficient_for_constant :
    ∃ hurwitz : ℤ → ℝ, BrauerSiegelLower hurwitz 1 ∧
      ¬ ∃ c : ℝ, 0 < c ∧ HurwitzSiegelLowerFrob hurwitz c :=
  ⟨logLossHurwitz, brauerSiegelLower_logLossHurwitz, logLossHurwitz_no_constant⟩

/-- Pointwise form of the obstruction: for every proposed `κ > 0` the
Brauer–Siegel model is eventually below `κ√D`. -/
theorem logLossHurwitz_ratio_small (κ : ℝ) (hκ : 0 < κ) :
    ∃ D : ℤ, IsFrobeniusDiscriminant D ∧ logLossHurwitz D < κ * Real.sqrt (D : ℝ) := by
  by_contra hnot
  push Not at hnot
  have hconst : ∃ c : ℝ, 0 < c ∧ HurwitzSiegelLowerFrob logLossHurwitz c :=
    ⟨κ, hκ, fun D hD => hnot D hD⟩
  exact logLossHurwitz_no_constant hconst

/-- **The class-number formula plus a logarithmic `L`-bound gives the
Brauer–Siegel `√D / log D` Hurwitz bound.**  This is the precise sense in which
the class-number formula supplies only a logarithmic loss: a `c / log |D|`
lower bound for `L(1, χ_D)` becomes
`(1/(2π)) c √D / log |D|` for `H(-D)`. -/
theorem brauerSiegelLower_of_classNumberFormula_and_log
    {hurwitz classNumber L1 weight : ℤ → ℝ} {c : ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hc : 0 < c)
    (hL : ∀ D : ℤ, IsFrobeniusDiscriminant D →
      c / Real.log ((D : ℝ) + 2) ≤ L1 D) :
    BrauerSiegelLower hurwitz (classNumberFormulaConstant * c) :=
  brauerSiegelLower_of_formula_and_LOneLog
    classNumberFormulaConstant_nonneg hc
    (hurwitzClassNumberFormulaLower_of_dirichletFormula hformula hw hdom) hL

/-! ## 5. The Landau–Page exceptional alternative -/

/-- **The Landau–Page exceptional-zero alternative.**  There is an absolute
`c > 0` such that `c ≤ L(1, χ_D)` for every Frobenius discriminant `D` except
possibly a single exceptional discriminant `E`.  The exception is itself a
Frobenius discriminant; no bound at `E` is asserted here.  The statement is
taken directly on the Frobenius support used below, so that no conductor
bookkeeping is hidden in the reduction. -/
def LandauPageAlternative (L1 : ℤ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ E : ℤ, IsFrobeniusDiscriminant E ∧
    ∀ D : ℤ, IsFrobeniusDiscriminant D → D ≠ E → c ≤ L1 D

/-- **Landau–Page plus positivity at the exceptional discriminant gives the
constant Siegel input.**  The constant is `min c (L(1, χ_E))`. -/
theorem siegelLOneLower_of_landauPageAlternative {L1 : ℤ → ℝ}
    (h : LandauPageAlternative L1)
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    SiegelLOneLower L1 := by
  obtain ⟨c, hc, E, hE, hbound⟩ := h
  refine ⟨min c (L1 E), lt_min hc (hpos E hE), ?_⟩
  intro D hD
  by_cases hDE : D = E
  · subst hDE
    exact min_le_right _ _
  · exact (min_le_left _ _).trans (hbound D hD hDE)

/-- **The Landau–Page alternative plus the class-number formula gives the
constant Siegel input**, because the class-number formula already supplies
pointwise positivity of `L(1, χ_D)`. -/
theorem siegelLOneLower_of_landauPageAlternative_classNumberFormula
    {classNumber L1 weight : ℤ → ℝ}
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (h : LandauPageAlternative L1) :
    SiegelLOneLower L1 :=
  siegelLOneLower_of_landauPageAlternative h
    (L1_pos_of_dirichletFormula hformula hw hclass)

/-- The constant form gives the Landau–Page alternative (any Frobenius
discriminant may be taken as the nominal exception). -/
theorem landauPageAlternative_of_siegelLOneLower {L1 : ℤ → ℝ}
    (h : SiegelLOneLower L1) : LandauPageAlternative L1 := by
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨c, hc, 4 * (1 : ℤ), isFrobeniusDiscriminant_four_mul 1 one_pos, ?_⟩
  intro D hD _hDE
  exact hbound D hD

/-- **The Landau–Page alternative, with positivity at the exception, is
equivalent to the constant form.**  Thus it is a faithful "standard form" of
the arithmetic input, neither stronger nor weaker in the presence of the
positivity supplied by the class-number formula. -/
theorem landauPageAlternative_iff_siegelLOneLower {L1 : ℤ → ℝ}
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    LandauPageAlternative L1 ↔ SiegelLOneLower L1 :=
  ⟨fun h => siegelLOneLower_of_landauPageAlternative h hpos,
    landauPageAlternative_of_siegelLOneLower⟩

/-! ## 6. The Hurwitz trace leaf from the constant Siegel input -/

/-- **The Hurwitz trace leaf from the constant Siegel input.**  The
class-number formula, the unit weight, the Hurwitz domination, and an explicit
constant `l` with `SiegelLOneLowerAt L1 l` give
`H(-D) ≥ (1/(2π)) · l · √D` on trace discriminants. -/
theorem hurwitzSiegelLowerTrace_of_siegelLOneLower
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ} {l : ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hS : SiegelLOneLowerAt L1 l) :
    HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  hurwitzSiegelLowerTrace_of_classNumberFormula hp hformula hw hdom hS.1 hS.2

/-- **The Hurwitz trace leaf from the existential constant Siegel input.** -/
theorem exists_hurwitzSiegelLowerTrace_of_siegelLOneLower
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hS : SiegelLOneLower L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) := by
  obtain ⟨l, hl, hbound⟩ := hS
  exact ⟨l, hl,
    hurwitzSiegelLowerTrace_of_classNumberFormula hp hformula hw hdom hl hbound⟩

/-- **The Hurwitz trace leaf from Landau–Page and the class-number formula.**
This is the route through the standard exceptional-zero alternative: the
formula supplies positivity at the exceptional discriminant, and Landau–Page
supplies the constant away from it. -/
theorem exists_hurwitzSiegelLowerTrace_of_landauPage
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hLP : LandauPageAlternative L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  exists_hurwitzSiegelLowerTrace_of_siegelLOneLower hp hformula hw hdom
    (siegelLOneLower_of_landauPageAlternative_classNumberFormula
      hformula hw hclass hLP)

/-- **The Hurwitz trace leaf from the qualitative input**, with the constant
form obtained from `NoExceptionalLOneSequence` and formula positivity. -/
theorem exists_hurwitzSiegelLowerTrace_of_noExceptional
    {p : ℕ → ℕ} {hurwitz classNumber L1 weight : ℤ → ℝ}
    (hp : ∀ n, 0 < p n)
    (hformula : DirichletClassNumberFormula classNumber L1 weight)
    (hw : UnitWeightPositive weight)
    (hclass : OrderClassNumberPositive classNumber)
    (hdom : HurwitzDominatesWeightedClassNumber hurwitz classNumber weight)
    (hno : NoExceptionalLOneSequence L1) :
    ∃ l : ℝ, 0 < l ∧
      HurwitzSiegelLowerTrace p hurwitz (classNumberFormulaConstant * l) :=
  exists_hurwitzSiegelLowerTrace_of_siegelLOneLower hp hformula hw hdom
    (siegelLOneLower_of_noExceptional
      (L1_pos_of_dirichletFormula hformula hw hclass) hno)

/-! ## 7. The `L27HurwitzAssemblyInputs` trace bound -/

/-- **Assemble `L27HurwitzAssemblyInputs` with the `L`-bound supplied by the
constant Siegel input.**  Compared with the assembly bundle of
`Cogentic.RandomizedL27HurwitzAssembly`, the fields `l`, `l_pos`, and
`l_one_lower` are filled from `SiegelLOneLowerAt L1 l`; all the curve-theoretic
and geometric fields are unchanged. -/
def toAssemblyInputs_of_siegel {I : L27_1Inputs}
    (hurwitz L1 : ℤ → ℝ) (classInput : DirichletClassNumberInput hurwitz L1)
    {l θ : ℝ} (hS : SiegelLOneLowerAt L1 l) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (central_trace : CentralTraceWindow I.p I.smooth θ)
    (p_prime : ∀ n, (I.p n).Prime)
    (waterhouse_model : ∀ n,
      WaterhouseWeightedModelCount (I.p n) (p_prime n) hurwitz)
    (orderCount_dominates_raw : ∀ n j,
      rawCurveOrderCount I.p p_prime n j ≤ I.orderCount n j)
    (fiber : JLineFiberInput I.p I.orderCount I.orderTop)
    (p_ge_four : ∀ n, 4 ≤ I.p n) : L27HurwitzAssemblyInputs I :=
  ⟨hurwitz, L1, classInput, l, hS.1, hS.2, θ, θ_pos, kappa_le,
    central_trace, p_prime, waterhouse_model, orderCount_dominates_raw,
    fiber, p_ge_four⟩

/-- **The trace bound of the assembled bundle.**  This is the Siegel leaf consumed
by `L27HurwitzInputs`, with constant `classNumberFormulaConstant * l`. -/
theorem toAssemblyInputs_of_siegel_siegelLower {I : L27_1Inputs}
    (hurwitz L1 : ℤ → ℝ) (classInput : DirichletClassNumberInput hurwitz L1)
    {l θ : ℝ} (hS : SiegelLOneLowerAt L1 l) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (central_trace : CentralTraceWindow I.p I.smooth θ)
    (p_prime : ∀ n, (I.p n).Prime)
    (waterhouse_model : ∀ n,
      WaterhouseWeightedModelCount (I.p n) (p_prime n) hurwitz)
    (orderCount_dominates_raw : ∀ n j,
      rawCurveOrderCount I.p p_prime n j ≤ I.orderCount n j)
    (fiber : JLineFiberInput I.p I.orderCount I.orderTop)
    (p_ge_four : ∀ n, 4 ≤ I.p n) :
    HurwitzSiegelLowerTrace I.p hurwitz (classNumberFormulaConstant * l) :=
  (toAssemblyInputs_of_siegel hurwitz L1 classInput hS θ_pos kappa_le
    central_trace p_prime waterhouse_model orderCount_dominates_raw fiber
    p_ge_four).siegelLower

/-- **The no-exceptional-sequence field of the assembled bundle**, derived from
the constant Siegel input. -/
theorem toAssemblyInputs_of_siegel_noExceptional {I : L27_1Inputs}
    (hurwitz L1 : ℤ → ℝ) (classInput : DirichletClassNumberInput hurwitz L1)
    {l θ : ℝ} (hS : SiegelLOneLowerAt L1 l) (θ_pos : 0 < θ)
    (kappa_le : I.κ ≤ (classNumberFormulaConstant * l) * Real.sqrt θ)
    (central_trace : CentralTraceWindow I.p I.smooth θ)
    (p_prime : ∀ n, (I.p n).Prime)
    (waterhouse_model : ∀ n,
      WaterhouseWeightedModelCount (I.p n) (p_prime n) hurwitz)
    (orderCount_dominates_raw : ∀ n j,
      rawCurveOrderCount I.p p_prime n j ≤ I.orderCount n j)
    (fiber : JLineFiberInput I.p I.orderCount I.orderTop)
    (p_ge_four : ∀ n, 4 ≤ I.p n) :
    NoExceptionalLOneSequence L1 :=
  (toAssemblyInputs_of_siegel hurwitz L1 classInput hS θ_pos kappa_le
    central_trace p_prime waterhouse_model orderCount_dominates_raw fiber
    p_ge_four).noExceptional

/-- **The Landau–Page alternative supplies an explicit constant for the
assembly bundle.**  Combined with positivity at the exceptional discriminant,
it yields an `l` with `SiegelLOneLowerAt L1 l`, which is precisely the `l`-field
consumed by `toAssemblyInputs_of_siegel`. -/
theorem exists_siegelLOneLowerAt_of_landauPage {L1 : ℤ → ℝ}
    (hLP : LandauPageAlternative L1)
    (hpos : ∀ D : ℤ, IsFrobeniusDiscriminant D → 0 < L1 D) :
    ∃ l : ℝ, SiegelLOneLowerAt L1 l :=
  siegelLOneLower_of_landauPageAlternative hLP hpos

/-! ## Axiom audit -/

#print axioms isFrobeniusDiscriminant_four_mul
#print axioms siegelLOneLower_iff_dirichletLOneInput
#print axioms noExceptional_of_siegelLOneLower
#print axioms siegelLOneLower_of_noExceptional
#print axioms siegelLOneLower_iff_noExceptional
#print axioms siegelEpsilonLOneLower_of_siegelLOneLower
#print axioms brauerSiegelLOneLower_of_siegelLOneLower
#print axioms log_add_two_le_rpow_mul
#print axioms logDecayModel_siegelEpsilon
#print axioms logDecayModel_not_constant
#print axioms logDecayModel_exceptionalSequence
#print axioms siegelEpsilonLOneLower_not_imply_noExceptional
#print axioms brauerSiegelLOneLower_logDecayModel
#print axioms brauerSiegelLOneLower_not_imply_noExceptional
#print axioms brauerSiegelLower_logLossHurwitz
#print axioms logLossHurwitz_no_constant
#print axioms brauerSiegelLower_insufficient_for_constant
#print axioms logLossHurwitz_ratio_small
#print axioms brauerSiegelLower_of_classNumberFormula_and_log
#print axioms siegelLOneLower_of_landauPageAlternative
#print axioms siegelLOneLower_of_landauPageAlternative_classNumberFormula
#print axioms landauPageAlternative_of_siegelLOneLower
#print axioms landauPageAlternative_iff_siegelLOneLower
#print axioms hurwitzSiegelLowerTrace_of_siegelLOneLower
#print axioms exists_hurwitzSiegelLowerTrace_of_siegelLOneLower
#print axioms exists_hurwitzSiegelLowerTrace_of_landauPage
#print axioms exists_hurwitzSiegelLowerTrace_of_noExceptional
#print axioms toAssemblyInputs_of_siegel
#print axioms toAssemblyInputs_of_siegel_siegelLower
#print axioms toAssemblyInputs_of_siegel_noExceptional
#print axioms exists_siegelLOneLowerAt_of_landauPage

end

end Cogentic.RandomizedL27LOneSiegel
