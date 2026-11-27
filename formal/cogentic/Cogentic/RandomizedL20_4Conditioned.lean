import Cogentic.RandomizedL20_4Sub
import Cogentic.RandomizedHasseIncidence
import Cogentic.RandomizedEpochPool
import Cogentic.RandomizedL21_2

/-!
# L20.4 conditioned: reducing the child-root-conditioned inputs

`Cogentic.RandomizedL20_4Sub` isolates four paper-level `Prop`s inside the
KeyBreak G.12 top step:

* `ConditionedTwoPoint` — the conditioned second moment of the normalized top
  height is `D^{O(1)}`;
* `ConditionedMeanLower` — the conditioned first moment is at least a fixed
  `a > 0`;
* `InteriorConcentration` — the G.11 base mass, the elliptic deletion fraction
  and the two G.12 rational exceptions are `D^{-B}` for every `B`;
* `TopG12Comparison` — the G.12 top square-root comparison.

This file reduces the first two to ordinary (unconditioned) estimates plus the
explicit conditioning loss, and either reduces or splits the last two into the
smallest explicit analytic sub-`Prop`s.  It then proves that the reduced bundle
realizes `L20_4SubInputs`, hence the `SubexpLeaf` and the `B = 2` ledger slot.

## What is reduced

1. **`ConditionedTwoPoint`.**  If the ordinary second moment is at most
   `D^{c_U}` and the conditioning event `g ∧ R_{q,s}` has mass at least
   `D^{-c_E}`, then the conditioned second moment is at most
   `D^{c_U + c_E}`.  The exponent `c_E` is exactly the `q`-loss the pool note
   warns about; it is kept explicit, never set to one
   (`conditionedTwoPoint_of_unconditioned`).
2. **`ConditionedMeanLower`.**  If the ordinary first moment is at least
   `a₀`, the top height is at most `D^{c_V}` off the conditioning event, the
   conditioning event has mass at least `D^{-c_E}` and the complement has mass
   at most `D^{-c_B}` with `c_V < c_B`, then the conditioned mean is at least
   `a` for every fixed `a ≤ a₀/2` (`conditionedMeanLower_of_unconditioned`).
   This is the elementary half of the balanced-strip-transfer comparison; the
   analytic content left over is only the ordinary one-point bound and the
   polynomial height cut.
3. **`InteriorConcentration`.**  It is split into four named `SubexpLoss`
   fields (`InteriorSubProps`).  The elliptic field is discharged from the
   existing L21.2 smooth-number estimate
   (`subexpLoss_of_L21_2`), and the union of the four fields is equivalent to
   the parent `Prop` (`interiorConcentration_iff_subProps`).
4. **`TopG12Comparison`.**  It is already the smallest explicit analytic
   sub-`Prop`: the G.12 incidence comparison.  We record its two equivalent
   explicit forms.  The additive three-term form
   (`topG12Comparison_of_additive`) is the shape produced by the G.54--G.55
   Cauchy--Schwarz step and assumes no cancellation between the internal, the
   incoming and the elliptic contributions.  The G.11-majorant form
   (`TopG12LinearComparison`) replaces `δ₀` by the explicit majorant
   `step^L (δ_L + L(η + ε_rat))`; it is a proved consequence of
   `TopG12Comparison` via `internal_linear_recurrence_bound`
   (`topG12LinearComparison_of_comparison`) and is exactly what
   `G12TopInputs.top_bound` consumes.

## Existing estimates used

* Paley–Zygmund in the pool form (`paleyZygmund_lower_of_unconditioned`) is the
  same estimate that `RandomizedEpochPool.PoolCoverageInputs.moment_bounds`
  consumes at reference scale `τ = 1`.
* The Hasse incidence count (`hasse_rich_fraction_le`) is the dyadic
  prime-counting input behind the deterministic trimming; it is recorded here
  in the exact fraction form used by the pool note.
* The L21.2 elliptic deletion fraction is a `SubexpLoss` by
  `RandomizedL21_2.L21_2Inputs.loss_le_exp_neg`.

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss: every exponent and
every deficit is explicit, and no estimate is replaced by `0`.
-/

namespace Cogentic.RandomizedL20_4Conditioned

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL20_4
open Cogentic.RandomizedL20_4Sub

/-! ## 1. Ordinary (unconditioned) sub-`Prop`s -/

/-- The ordinary second moment of the normalized top height is `D^{c}`.  This is
the unconditioned two-point estimate of pool-note item 1; it is the same shape
as `RandomizedEpochPool.PoolCoverageInputs.hsecond` at reference scale one. -/
def UnconditionedTwoPoint {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    pmfExpect (μ n) (fun ω => Z n ω ^ 2) ≤ Real.exp (c * scale n)

/-- The ordinary first moment of the normalized top height is at least `a₀`.
This is the unconditioned one-point estimate of pool-note item 1, matching
`RandomizedEpochPool.PoolCoverageInputs.hmean` at reference scale one. -/
def UnconditionedMeanLower {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (Z : ℕ → Ω → ℝ) (a₀ : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, a₀ ≤ pmfExpect (μ n) (Z n)

/-- The conditioning event `g ∧ R_{q,s}` has mass at least `D^{-c}`.  The
exponent `c` is the explicit `q`-loss of the conditioning. -/
def EventMassLower {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, Real.exp (-c * scale n) ≤ pmfProb (μ n) (E n)

/-- The complement of the conditioning event has mass at most `D^{-c}`. -/
def ComplementMassUpper {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, pmfProb (μ n) (fun ω => ¬ E n ω) ≤ Real.exp (-c * scale n)

/-- Off the conditioning event the normalized top height is at most `D^{c}`.
This is the ordinary polynomial height cut (the upper second-moment cut of the
pool note), stated only where it is needed. -/
def OffEventHeightUpper {Ω : Type*} [Fintype Ω] (_μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ ω : Ω, ¬ E n ω → Z n ω ≤ Real.exp (c * scale n)

/-! ## 2. Elementary finite-`PMF` lemmas -/

/-- An expectation of a nonnegative random variable is nonnegative. -/
theorem pmfExpect_nonneg {Ω : Type*} [Fintype Ω] (μ : PMF Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ pmfExpect μ X := by
  unfold pmfExpect
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (pmfWeight_nonneg μ ω) (hX ω)

/-- The restricted weight is at most the unrestricted one. -/
theorem condWeight_le_pmfWeight {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (E : Ω → Prop) (ω : Ω) : condWeight μ E ω ≤ pmfWeight μ ω := by
  classical
  unfold condWeight
  split_ifs with h
  · exact le_rfl
  · exact pmfWeight_nonneg μ ω

/-- **Conditioning cannot increase a nonnegative moment.**  Dividing by the
event mass gives the sharp bound in the direction used below. -/
theorem condExpect_le_pmfExpect_div {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (E : Ω → Prop) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (hPr : 0 < pmfProb μ E) :
    condExpect μ E X ≤ pmfExpect μ X / pmfProb μ E := by
  classical
  unfold condExpect pmfExpect
  have hsum : (∑ ω, condWeight μ E ω * X ω) ≤ ∑ ω, pmfWeight μ ω * X ω :=
    Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_right (condWeight_le_pmfWeight μ E ω) (hX ω)
  exact (div_le_div_iff_of_pos_right hPr).mpr hsum

/-- The restricted sum over the event is the ordinary sum over its indicator. -/
theorem sum_condWeight_mul_eq_filter {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (E : Ω → Prop) [DecidablePred E] (X : Ω → ℝ) :
    (∑ ω, condWeight μ E ω * X ω) =
      ∑ ω ∈ Finset.univ.filter E, pmfWeight μ ω * X ω := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  unfold condWeight
  split_ifs with h
  · rfl
  · simp

/-- Splitting an expectation over an event and its complement. -/
theorem pmfExpect_eq_filter_add_filter_not {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (E : Ω → Prop) [DecidablePred E] (X : Ω → ℝ) :
    pmfExpect μ X =
      (∑ ω ∈ Finset.univ.filter E, pmfWeight μ ω * X ω) +
        ∑ ω ∈ Finset.univ.filter (fun ω => ¬ E ω), pmfWeight μ ω * X ω := by
  classical
  unfold pmfExpect
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := E)
    (f := fun ω => pmfWeight μ ω * X ω)]

/-- The complement contribution is at most the height bound times the complement
mass. -/
theorem sum_compl_mul_le {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    [DecidablePred E] (Z : Ω → ℝ) {V : ℝ} (hZ : ∀ ω, ¬ E ω → Z ω ≤ V) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ¬ E ω), pmfWeight μ ω * Z ω) ≤
      V * pmfProb μ (fun ω => ¬ E ω) := by
  classical
  rw [pmfProb_eq_sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω hω
  have hw : 0 ≤ pmfWeight μ ω := pmfWeight_nonneg μ ω
  have hZle : Z ω ≤ V := hZ ω (Finset.mem_filter.mp hω).2
  calc pmfWeight μ ω * Z ω ≤ pmfWeight μ ω * V :=
        mul_le_mul_of_nonneg_left hZle hw
    _ = V * pmfWeight μ ω := by ring

/-- `exp ((c_V - c_B) H) ≤ z / 2` eventually when `c_V < c_B` and `z > 0`.
This is the scalar comparison that lets the off-event contribution be absorbed. -/
theorem eventually_exp_sub_mul_le_half {cV cB z : ℝ} (hlt : cV < cB) (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((cV - cB) * scale n) ≤ z / 2 := by
  have hd : 0 < cB - cV := sub_pos.mpr hlt
  have hz2 : 0 < z / 2 := by positivity
  filter_upwards [scale_grows.eventually_ge_atTop (-Real.log (z / 2) / (cB - cV))]
    with n hn
  rw [← Real.exp_log hz2]
  apply Real.exp_le_exp.mpr
  have h1 : (cB - cV) * (-Real.log (z / 2) / (cB - cV)) ≤ (cB - cV) * scale n :=
    mul_le_mul_of_nonneg_left hn hd.le
  have h2 : (cB - cV) * (-Real.log (z / 2) / (cB - cV)) = -Real.log (z / 2) := by
    field_simp
  rw [h2] at h1
  have h3 : (cV - cB) * scale n = -((cB - cV) * scale n) := by ring
  rw [h3]
  linarith

/-! ## 3. The conditioned moment reductions -/

/-- **Conditioned two-point bound from the ordinary two-point bound.**  The
ordinary second moment `≤ D^{c_U}` and the event mass `≥ D^{-c_E}` give the
conditioned second moment `≤ D^{c_U + c_E}`.  The exponent `c_E` is the
explicit conditioning loss; it is not absorbed into the constant. -/
theorem conditionedTwoPoint_of_unconditioned {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {cU cE : ℝ}
    (h2 : UnconditionedTwoPoint μ Z cU) (hE : EventMassLower μ E cE) :
    ConditionedTwoPoint μ E Z (cU + cE) := by
  unfold ConditionedTwoPoint UnconditionedTwoPoint EventMassLower at *
  filter_upwards [h2, hE] with n h2' hE'
  have hPr : 0 < pmfProb (μ n) (E n) := lt_of_lt_of_le (Real.exp_pos _) hE'
  have hX : ∀ ω, 0 ≤ Z n ω ^ 2 := fun ω => sq_nonneg _
  have h1 : condExpect (μ n) (E n) (fun ω => Z n ω ^ 2) ≤
      pmfExpect (μ n) (fun ω => Z n ω ^ 2) / pmfProb (μ n) (E n) :=
    condExpect_le_pmfExpect_div (μ n) (E n) (fun ω => Z n ω ^ 2) hX hPr
  have h2nn : 0 ≤ pmfExpect (μ n) (fun ω => Z n ω ^ 2) := pmfExpect_nonneg _ hX
  have hdiv : pmfExpect (μ n) (fun ω => Z n ω ^ 2) / pmfProb (μ n) (E n) ≤
      Real.exp (cU * scale n) / Real.exp (-cE * scale n) :=
    div_le_div₀ (Real.exp_pos _).le h2' (Real.exp_pos _) hE'
  have heq : Real.exp (cU * scale n) / Real.exp (-cE * scale n) =
      Real.exp ((cU + cE) * scale n) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  exact h1.trans (hdiv.trans (le_of_eq heq))

/-- **Conditioned mean lower bound from the ordinary one-point bound.**  This is
the elementary form of the balanced-strip-transfer comparison (2): the ordinary
mean `a₀`, the polynomial height cut `D^{c_V}` off the event, the conditioning
mass `D^{-c_E}` and the complement mass `D^{-c_B}` (with `c_V < c_B`) give a
fixed conditioned mean `a` for every `a ≤ a₀ / 2`.  No term is dropped: the
complement contribution is charged explicitly to `D^{c_V - c_B}`. -/
theorem conditionedMeanLower_of_unconditioned {Ω : Type*} [Fintype Ω]
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {a a₀ cE cV cB : ℝ}
    (ha₀ : 0 < a₀) (haa : a ≤ a₀ / 2) (hVltB : cV < cB)
    (hE : EventMassLower μ E cE)
    (hcomp : ComplementMassUpper μ E cB)
    (hZ : OffEventHeightUpper μ E Z cV)
    (hmean : UnconditionedMeanLower μ Z a₀) :
    ConditionedMeanLower μ E Z a := by
  classical
  unfold ConditionedMeanLower EventMassLower ComplementMassUpper
    OffEventHeightUpper UnconditionedMeanLower at *
  filter_upwards [hE, hcomp, hZ, hmean,
    eventually_exp_sub_mul_le_half hVltB ha₀,
    scale_grows.eventually_ge_atTop 0] with n hE' hcomp' hZ' hmean' hshift hH0
  have hPr : 0 < pmfProb (μ n) (E n) := lt_of_lt_of_le (Real.exp_pos _) hE'
  have hP1 : pmfProb (μ n) (E n) ≤ 1 := pmfProb_le_one _ _
  have hV : 0 ≤ Real.exp (cV * scale n) := (Real.exp_pos _).le
  have hmass : Real.exp (cV * scale n) * pmfProb (μ n) (fun ω => ¬ E n ω) ≤ a₀ / 2 := by
    have h1 : Real.exp (cV * scale n) * pmfProb (μ n) (fun ω => ¬ E n ω) ≤
        Real.exp (cV * scale n) * Real.exp (-cB * scale n) :=
      mul_le_mul_of_nonneg_left hcomp' hV
    have h2 : Real.exp (cV * scale n) * Real.exp (-cB * scale n) =
        Real.exp ((cV - cB) * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2] at h1
    exact h1.trans hshift
  have hSE : (∑ ω, condWeight (μ n) (E n) ω * Z n ω) =
      ∑ ω ∈ Finset.univ.filter (E n), pmfWeight (μ n) ω * Z n ω :=
    sum_condWeight_mul_eq_filter (μ n) (E n) (Z n)
  have hsplit := pmfExpect_eq_filter_add_filter_not (μ n) (E n) (Z n)
  have hcompl : (∑ ω ∈ Finset.univ.filter (fun ω => ¬ E n ω),
        pmfWeight (μ n) ω * Z n ω) ≤
      Real.exp (cV * scale n) * pmfProb (μ n) (fun ω => ¬ E n ω) :=
    sum_compl_mul_le (μ n) (E n) (Z n) (V := Real.exp (cV * scale n))
      (fun ω hω => hZ' ω hω)
  have hA : a₀ - Real.exp (cV * scale n) * pmfProb (μ n) (fun ω => ¬ E n ω) ≤
      ∑ ω ∈ Finset.univ.filter (E n), pmfWeight (μ n) ω * Z n ω := by
    linarith
  have hTlow : a₀ / 2 ≤ ∑ ω, condWeight (μ n) (E n) ω * Z n ω := by
    rw [hSE]
    linarith
  have hdiv_ge : a₀ / 2 ≤ (a₀ / 2) / pmfProb (μ n) (E n) := by
    rw [le_div_iff₀ hPr]
    nlinarith
  have hquot : (a₀ / 2) / pmfProb (μ n) (E n) ≤
      (∑ ω, condWeight (μ n) (E n) ω * Z n ω) / pmfProb (μ n) (E n) :=
    div_le_div_of_nonneg_right hTlow hPr.le
  have hcond : condExpect (μ n) (E n) (Z n) =
      (∑ ω, condWeight (μ n) (E n) ω * Z n ω) / pmfProb (μ n) (E n) := rfl
  calc a ≤ a₀ / 2 := haa
    _ ≤ (a₀ / 2) / pmfProb (μ n) (E n) := hdiv_ge
    _ ≤ (∑ ω, condWeight (μ n) (E n) ω * Z n ω) / pmfProb (μ n) (E n) := hquot
    _ = condExpect (μ n) (E n) (Z n) := hcond.symm

/-! ## 4. Existing pool, Hasse and L21.2 estimates -/

/-- **Paley–Zygmund in the pool form.**  The ordinary first moment `≥ a` and the
ordinary second moment `≤ M` give the unconditional hit probability
`≥ a²/(4M)` at reference scale one.  This is the `τ = 1` case of the estimate
consumed by `RandomizedEpochPool.PoolCoverageInputs.moment_bounds`. -/
theorem paleyZygmund_lower_of_unconditioned {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (Z : Ω → ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hmean : a ≤ pmfExpect μ Z)
    (hsecond : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M) :
    a ^ 2 / (4 * M) ≤ pmfProb μ (fun ω => a / 2 ≤ Z ω) := by
  have hmean' : a * (1 : ℝ) ≤ pmfExpect μ Z := by rw [mul_one]; exact hmean
  have hsecond' : pmfExpect μ (fun ω => Z ω ^ 2) ≤ M * (1 : ℝ) ^ 2 := by
    rw [one_pow, mul_one]; exact hsecond
  simpa using pmf_paley_zygmund μ Z (τ := 1) ha hM one_pos hmean' hsecond'

/-- **Hasse incidence in fraction form.**  The number of `(P, 2P]` primes with at
least `k` Hasse-window witnesses is at most `(2√(8P)+1) · |W| / k`.  This is
`RandomizedHasseIncidence.rich_hasse_centres_mul_le` after dividing by `k`; it is
the deterministic prime count behind the dyadic trimming. -/
theorem hasse_rich_fraction_le (C W : Finset ℤ) (P k : ℕ) (hk : 0 < k)
    (hC : ∀ c ∈ C, c ≤ 2 * (P : ℤ) + 1) :
    ((C.filter fun c =>
        k ≤ (W.filter fun w => (w - c) ^ 2 ≤ 4 * (c - 1)).card).card : ℝ) ≤
      (((2 * Nat.sqrt (8 * P) + 1) * W.card : ℕ) : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [le_div_iff₀ hkR]
  exact_mod_cast Cogentic.RandomizedHasseIncidence.rich_hasse_centres_mul_le C W P k hC

/-- **The L21.2 elliptic deletion fraction is a `SubexpLoss`.**  The existing
smooth-number estimate `L21_2Inputs.loss_le_exp_neg` has exactly the pool-note
`D^{-B}` form, so it discharges the elliptic field of
`InteriorConcentration`. -/
theorem subexpLoss_of_L21_2 (I : Cogentic.RandomizedL21_2.L21_2Inputs) :
    SubexpLoss I.loss :=
  fun B hB => I.loss_le_exp_neg B hB

/-! ## 5. Splitting `InteriorConcentration` -/

/-- The four explicit `SubexpLoss` fields of `InteriorConcentration`: the G.11
base mass, the elliptic deletion fraction, the G.11 rational error and the G.12
incoming exception.  This is the smallest analytic sub-`Prop` set: each field is
a single `D^{-B}` statement. -/
structure InteriorSubProps (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (eta epsRat epsIn : ℕ → ℝ) : Prop where
  /-- Pool-note item 2: the G.11 internal base mass is `D^{-B}`. -/
  base_subexp : SubexpLoss fun n => interior n L
  /-- L21.2: the elliptic deletion fraction is `D^{-B}`. -/
  eta_subexp : SubexpLoss eta
  /-- The G.11 rational error is `D^{-B}`. -/
  epsRat_subexp : SubexpLoss epsRat
  /-- The G.12 incoming exceptional mass is `D^{-B}`. -/
  epsIn_subexp : SubexpLoss epsIn

/-- The four fields assemble the parent `InteriorConcentration`. -/
theorem interiorConcentration_of_subProps {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsRat epsIn : ℕ → ℝ} (h : InteriorSubProps interior L eta epsRat epsIn) :
    InteriorConcentration interior L eta epsRat epsIn :=
  ⟨h.base_subexp, h.eta_subexp, h.epsRat_subexp, h.epsIn_subexp⟩

/-- Conversely, the parent `InteriorConcentration` is exactly the four fields. -/
theorem subProps_of_interiorConcentration {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsRat epsIn : ℕ → ℝ} (h : InteriorConcentration interior L eta epsRat epsIn) :
    InteriorSubProps interior L eta epsRat epsIn :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `InteriorConcentration` is equivalent to its four explicit fields. -/
theorem interiorConcentration_iff_subProps {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {eta epsRat epsIn : ℕ → ℝ} :
    InteriorConcentration interior L eta epsRat epsIn ↔
      InteriorSubProps interior L eta epsRat epsIn :=
  ⟨subProps_of_interiorConcentration, interiorConcentration_of_subProps⟩

/-- **The elliptic field is discharged by L21.2.**  If the elliptic deletion
fraction `eta` is the L21.2 exceptional fraction `I.loss`, then the `eta` field
of `InteriorSubProps` is not a new analytic input: it is the existing
smooth-number estimate `L21_2Inputs.loss_le_exp_neg`. -/
theorem interiorSubProps_of_L21_2 {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {epsRat epsIn eta : ℕ → ℝ} (I : Cogentic.RandomizedL21_2.L21_2Inputs)
    (heta : ∀ n, eta n = I.loss n)
    (hbase : SubexpLoss fun n => interior n L)
    (hrat : SubexpLoss epsRat) (hin : SubexpLoss epsIn) :
    InteriorSubProps interior L eta epsRat epsIn where
  base_subexp := hbase
  eta_subexp := by
    intro B hB
    filter_upwards [subexpLoss_of_L21_2 I B hB] with n hn
    rwa [heta n]
  epsRat_subexp := hrat
  epsIn_subexp := hin

/-! ## 6. Explicit forms of `TopG12Comparison` -/

/-- The G.12 comparison with the internal mass `δ₀` replaced by its explicit
G.11 majorant `step^L (δ_L + L(η + ε_rat))`.  The majorant is at least `δ₀` by
`internal_linear_recurrence_bound`, so this form is *stronger* than
`TopG12Comparison`; it is proved from the latter below and separates the G.11
propagation from the G.12 square-root incidence step. -/
def TopG12LinearComparison (top Ctop : ℕ → ℝ) (interior : ℕ → ℕ → ℝ)
    (step eta epsRat epsIn : ℕ → ℝ) (L : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ Ctop n *
      (Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
        Real.sqrt (epsIn n) + eta n)

/-- **The G.12 comparison at the explicit G.11 majorant is a proved
consequence of `TopG12Comparison`.**  The linear recurrence algebra bounds `δ₀`
by `step^L (δ_L + L(η + ε_rat))`; monotonicity of the square root then gives the
majorant form.  This is the exact shape consumed by
`RandomizedL20_4Sub.G12TopInputs.top_bound`, and it shows that
`TopG12Comparison` is the minimal analytic input: the G.11 propagation is
already proved, and the only remaining analytic content is the G.12 incidence
comparison itself. -/
theorem topG12LinearComparison_of_comparison {interior : ℕ → ℕ → ℝ} {L : ℕ}
    {top Ctop step eta epsRat epsIn : ℕ → ℝ}
    (hcmp : TopG12Comparison top Ctop interior epsIn eta)
    (hrec : G11InteriorRecurrence interior L step eta epsRat)
    (hstep : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (hα : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (hCtop : ∀ᶠ n : ℕ in atTop, 0 ≤ Ctop n) :
    TopG12LinearComparison top Ctop interior step eta epsRat epsIn L := by
  filter_upwards [hcmp, hrec, hstep, hα, hCtop] with n hcmp' hrec' hstep' hα' hCtop'
  have hint := Cogentic.RandomizedFieldPoolDescent.internal_linear_recurrence_bound
    (interior n) L hstep' hα' hrec'
  have hsqrt : Real.sqrt (interior n 0) ≤
      Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) :=
    Real.sqrt_le_sqrt hint
  have hsum : Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n ≤
      Real.sqrt (step n ^ L * (interior n L + (L : ℝ) * (eta n + epsRat n))) +
        Real.sqrt (epsIn n) + eta n := by linarith
  exact hcmp'.trans (mul_le_mul_of_nonneg_left hsum hCtop')

/-- **The G.12 comparison in additive form.**  The G.54--G.55 incidence argument
produces three separate nonnegative contributions — the internal square root,
the incoming square root and the elliptic fraction.  The additive form below is
the smallest explicit form of the analytic input: it assumes no cancellation
between the three terms, and the factored `TopG12Comparison` follows by
distributivity. -/
theorem topG12Comparison_of_additive {interior : ℕ → ℕ → ℝ} {top Ctop : ℕ → ℝ}
    {epsIn eta : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      top n ≤ Ctop n * Real.sqrt (interior n 0) +
        Ctop n * Real.sqrt (epsIn n) + Ctop n * eta n) :
    TopG12Comparison top Ctop interior epsIn eta := by
  filter_upwards [h] with n hn
  calc top n ≤ Ctop n * Real.sqrt (interior n 0) +
        Ctop n * Real.sqrt (epsIn n) + Ctop n * eta n := hn
    _ = Ctop n * (Real.sqrt (interior n 0) + Real.sqrt (epsIn n) + eta n) := by ring

/-! ## 7. The reduced input bundle -/

/-- The child-root pair data with the two conditioned moment `Prop`s replaced by
their ordinary counterparts and the explicit conditioning loss.  The fields
`twoPoint` and `meanLower` below derive the parent `ConditionedTwoPoint` and
`ConditionedMeanLower`; `toPairData` realizes the parent `PairData`. -/
structure PairConditionedData (Ω : Type*) [Fintype Ω] where
  /-- The field/trial law. -/
  μ : ℕ → PMF Ω
  /-- Rational-good environments. -/
  good : ℕ → Ω → Prop
  /-- The prescribed child root event `R_{q,s}`. -/
  childRoot : ℕ → Ω → Prop
  /-- The normalized top height `H^det_{0,J}/B₁(q)`. -/
  Z : ℕ → Ω → ℝ
  /-- The fixed Paley--Zygmund mean constant. -/
  a : ℝ
  a_pos : 0 < a
  /-- The ordinary first-moment constant. -/
  a₀ : ℝ
  a₀_pos : 0 < a₀
  /-- The target conditioned mean is at most half the ordinary mean. -/
  a_le : a ≤ a₀ / 2
  /-- Exponent of the ordinary second moment. -/
  cU : ℝ
  cU_nonneg : 0 ≤ cU
  /-- Exponent of the conditioning event mass lower bound. -/
  cE : ℝ
  cE_nonneg : 0 ≤ cE
  /-- Exponent of the off-event height cut. -/
  cV : ℝ
  /-- Exponent of the complement mass upper bound. -/
  cB : ℝ
  /-- The complement decays faster than the height grows. -/
  cV_lt_cB : cV < cB
  /-- Exponent of the dyad cardinality. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cU + cE + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  /-- The incoming event has positive mass at every scale. -/
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEvent good childRoot n)
  /-- The ordinary (unconditioned) second moment. -/
  uncond_two_point : UnconditionedTwoPoint μ Z cU
  /-- The conditioning event mass lower bound. -/
  event_mass_lower : EventMassLower μ (fun n => pairEvent good childRoot n) cE
  /-- The ordinary one-point lower bound. -/
  uncond_mean_lower : UnconditionedMeanLower μ Z a₀
  /-- The off-event height cut. -/
  off_event_height : OffEventHeightUpper μ (fun n => pairEvent good childRoot n) Z cV
  /-- The complement mass upper bound. -/
  complement_mass_upper : ComplementMassUpper μ (fun n => pairEvent good childRoot n) cB

namespace PairConditionedData

variable {Ω : Type*} [Fintype Ω]

/-- The conditioned two-point bound derived from the ordinary bound and the
explicit conditioning loss `cE`. -/
theorem twoPoint (S : PairConditionedData Ω) :
    ConditionedTwoPoint S.μ (fun n => pairEvent S.good S.childRoot n) S.Z
      (S.cU + S.cE) :=
  conditionedTwoPoint_of_unconditioned S.μ _ S.Z S.uncond_two_point S.event_mass_lower

/-- The conditioned mean lower bound derived from the ordinary one-point bound,
the off-event height cut and the explicit event/complement masses. -/
theorem meanLower (S : PairConditionedData Ω) :
    ConditionedMeanLower S.μ (fun n => pairEvent S.good S.childRoot n) S.Z S.a :=
  conditionedMeanLower_of_unconditioned S.μ _ S.Z S.a₀_pos S.a_le S.cV_lt_cB
    S.event_mass_lower S.complement_mass_upper S.off_event_height S.uncond_mean_lower

/-- The reduced pair data realize the parent `PairData`. -/
noncomputable def toPairData (S : PairConditionedData Ω) : PairData Ω where
  μ := S.μ
  good := S.good
  childRoot := S.childRoot
  Z := S.Z
  a := S.a
  a_pos := S.a_pos
  cPair := S.cU + S.cE
  cPair_nonneg := add_nonneg S.cU_nonneg S.cE_nonneg
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := S.poolSize_ge
  event_pos := S.event_pos
  mean_lower := S.meanLower
  two_point := S.twoPoint

end PairConditionedData

/-- The G.11/G.12 top data with the interior concentration split into its four
explicit `SubexpLoss` fields.  `comparison` remains the minimal G.12 analytic
input; its G.11-majorant consequence is recorded separately above. -/
structure TopConditionedData where
  L : ℕ
  interior : ℕ → ℕ → ℝ
  step : ℕ → ℝ
  eta : ℕ → ℝ
  epsRat : ℕ → ℝ
  epsIn : ℕ → ℝ
  top : ℕ → ℝ
  Ctop : ℕ → ℝ
  cTop : ℝ
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- The G.12 top square-root comparison (minimal analytic input). -/
  comparison : TopG12Comparison top Ctop interior epsIn eta
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  /-- The four explicit interior `SubexpLoss` fields. -/
  concentration : InteriorSubProps interior L eta epsRat epsIn

namespace TopConditionedData

/-- The four interior fields realize the parent `InteriorConcentration`. -/
theorem interiorConcentration (S : TopConditionedData) :
    InteriorConcentration S.interior S.L S.eta S.epsRat S.epsIn :=
  interiorConcentration_of_subProps S.concentration

/-- The G.11-majorant form of the top comparison, derived from `comparison` and
the recurrence.  This is the shape consumed by the existing G.12 consumer. -/
theorem linearComparison (S : TopConditionedData) :
    TopG12LinearComparison S.top S.Ctop S.interior S.step S.eta S.epsRat S.epsIn S.L :=
  topG12LinearComparison_of_comparison S.comparison S.recurrence S.step_ge_one
    S.alpha_nonneg (Eventually.of_forall S.Ctop_nonneg)

/-- The reduced top data realize the parent `TopData`. -/
noncomputable def toTopData (S : TopConditionedData) : TopData where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  comparison := S.comparison
  Ctop_le := S.Ctop_le
  concentration := S.interiorConcentration

end TopConditionedData

/-- **The conditioned L20.4 inputs, reduced.**  The pair part carries the
ordinary moment estimates plus the explicit conditioning loss; the top part
carries the four interior `SubexpLoss` fields and the minimal G.12 comparison;
the dyad part is the already-reduced `DyadData`. -/
structure L20_4ConditionedInputs (Ω P : Type*) [Fintype Ω] [DecidableEq P] where
  pair : PairConditionedData Ω
  top : TopConditionedData
  dyad : DyadData P

namespace L20_4ConditionedInputs

variable {Ω P : Type*} [Fintype Ω] [DecidableEq P]

/-- The reduced bundle realizes `L20_4SubInputs`. -/
noncomputable def toSubInputs (S : L20_4ConditionedInputs Ω P) : L20_4SubInputs Ω P where
  pair := S.pair.toPairData
  top := S.top.toTopData
  dyad := S.dyad

/-- The reduced deficit is exactly the parent deficit: pool miss mass, dyad
Markov fraction and G.12 top mass.  Nothing is set to zero. -/
noncomputable def loss (S : L20_4ConditionedInputs Ω P) (n : ℕ) : ℝ :=
  S.toSubInputs.loss n

theorem loss_nonneg (S : L20_4ConditionedInputs Ω P) (n : ℕ) : 0 ≤ S.loss n :=
  S.toSubInputs.loss_nonneg n

/-- **The L20.4 reduction from the conditioned inputs.**  The pool union bound,
the dyad Markov trimming and the G.12 top step are each `D^{-B}`, hence the sum
is. -/
theorem subexpLoss (S : L20_4ConditionedInputs Ω P) : SubexpLoss S.loss :=
  S.toSubInputs.subexpLoss

/-- The `SubexpLeaf` for the reduced L20.4 inputs. -/
noncomputable def toSubexpLeaf (S : L20_4ConditionedInputs Ω P) : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The `B = 2` C5 ledger slot for the reduced inputs. -/
theorem slot_le (S : L20_4ConditionedInputs Ω P) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toSubexpLeaf.slot

/-- The reduced bundle realizes the parent `L20_4Inputs` through
`L20_4SubInputs`. -/
noncomputable def toPaper (S : L20_4ConditionedInputs Ω P) : L20_4Inputs Ω P :=
  S.toSubInputs.toPaper

/-- The parent realization carries exactly the same deficit. -/
theorem toPaper_loss_eq (S : L20_4ConditionedInputs Ω P) (n : ℕ) :
    S.toPaper.loss n = S.loss n := rfl

end L20_4ConditionedInputs

/-! ## Axiom audit -/

#print axioms conditionedTwoPoint_of_unconditioned
#print axioms conditionedMeanLower_of_unconditioned
#print axioms paleyZygmund_lower_of_unconditioned
#print axioms hasse_rich_fraction_le
#print axioms subexpLoss_of_L21_2
#print axioms interiorConcentration_of_subProps
#print axioms subProps_of_interiorConcentration
#print axioms interiorConcentration_iff_subProps
#print axioms interiorSubProps_of_L21_2
#print axioms topG12Comparison_of_additive
#print axioms topG12LinearComparison_of_comparison
#print axioms PairConditionedData.twoPoint
#print axioms PairConditionedData.meanLower
#print axioms PairConditionedData.toPairData
#print axioms TopConditionedData.interiorConcentration
#print axioms TopConditionedData.linearComparison
#print axioms TopConditionedData.toTopData
#print axioms L20_4ConditionedInputs.toSubInputs
#print axioms L20_4ConditionedInputs.subexpLoss
#print axioms L20_4ConditionedInputs.slot_le
#print axioms L20_4ConditionedInputs.toPaper
#print axioms L20_4ConditionedInputs.toPaper_loss_eq

end Cogentic.RandomizedL20_4Conditioned
