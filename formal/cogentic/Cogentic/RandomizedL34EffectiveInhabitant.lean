import Cogentic.RandomizedL34EffectiveChebotarev

/-!
# L34: an explicit inhabitant of the effective-Chebotarev bundle

This file is a non-vacuity / consistency check for
`L34EffectiveChebotarevInputs`, not a proof of Chebotarev.  It fixes the concrete
toy parameters

* `T n = n + 2`, `F = 1`, `degree = 1`, `discLog = 1`,
* `beta0 = 3/4`, `zeroRealPart = 1/2`,
* `K = 1/2`, `cbr = 128`, `csel = 1/16`, `Ch = 1`,
* `C = 10^{-100}`, `cZ = 1`, `cz = 1`,
* `R n = (n+2)^10`, `pTrial = 1/2`, `actualMiss n = (1/2)^(R n)`,

and proves every field of the bundle at these parameters, except that the
log-integral bracket is supplied by the *free* placeholder fields `liX` and
`liBeta0`.  Those two fields are not constrained by the bundle.

## What is genuine and what is a placeholder

* The range input, the Stark input, both logarithmic budgets, the class-count
  input, the probe budget, the union bound and the eventual `T^3` domination are
  proved for the concrete parameters above.
* The zero-free field is the **vacuous** `DedekindZeroFreeInput` obtained from
  the explicit zero sequence with real part `1/2`: since `3/4 < 1/2` is false,
  the implication is empty.  This is exactly the mechanism documented in
  `Cogentic.RandomizedL34ZeroFaithful`; it is labelled as vacuous here and is
  not evidence for a real zero-free region.
* `liX` and `liBeta0` are chosen as `bracketTerm 128 ... + 1` and `1`.  This
  makes the bracket field definitional.  The bundle does not require them to be
  the genuine `Li x` and `Li x^{β₀}`.

## The one field that cannot be made faithful

With the genuine sequences `paperLiX T` and `paperLiBeta0 beta0 T`, the bracket
at `cbr = 128` is **false**, not merely unproved:
`¬ LogIntegralBracket 128 (cutoff T) 1 T (paperLiX T) (paperLiBeta0 beta0 T)`.
Indeed `Li x - Li x^{3/4} ≤ x / ((3/4) log x) = x/(48 log 2)`, while the
bracket asks for `128 x / T^6 = 128 x / 64 = 2x` at `n = 0`.  Thus

`no_faithful_inhabitant` shows that no inhabitant of the full bundle can have
both the genuine `Li` sequences and `cbr = 128`.  The bracket is the unique
remaining field under the faithful reading; at `cbr = 1/16` (the constant proved
by `logIntegralBracket_paper`) it is available.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and the loss is the
actual positive probe miss `(1/2)^R`, not zero.
-/

namespace Cogentic.RandomizedL34EffectiveInhabitant

open Filter Real MeasureTheory intervalIntegral
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Range
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34EffectiveChebotarev
open Cogentic.RandomizedL34LogIntegral
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The concrete parameters -/

/-- `T n = n + 2`. -/
def cT : ℕ → ℝ := fun n => (n : ℝ) + 2

/-- The factorial factor, taken to be `1`. -/
def cF : ℕ → ℝ := fun _ => 1

/-- The absolute degree, taken to be `1`. -/
def cDegree : ℕ → ℝ := fun _ => 1

/-- The exceptional real zero, taken to be `3/4`. -/
def cBeta0 : ℕ → ℝ := fun _ => 3 / 4

/-- The explicit zero sequence real part, taken to be `1/2`. -/
def cZeroRealPart : ℕ → ℝ := fun _ => 1 / 2

/-- `log |Δ_E|`, taken to be `1`. -/
def cDiscLog : ℕ → ℝ := fun _ => 1

/-- `C = 10^{-100}`. -/
def cC : ℝ := (1 : ℝ) / 10 ^ 100

/-- The range constant `K = 1/2`. -/
def cK : ℝ := 1 / 2

/-- The effective-error exponent `cZ = 1`. -/
def cCZ : ℝ := 1

/-- The zero-free constant `cz = 1`. -/
def cCz : ℝ := 1

/-- The bracket constant `cbr = 128`. -/
def cCbr : ℝ := 128

/-- The per-ideal selection constant `csel = 1/16`. -/
def cCsel : ℝ := 1 / 16

/-- The class-count polynomial constant `Ch = 1`. -/
def cCh : ℝ := 1

/-- The probe count `R n = (n+2)^10`. -/
def cR : ℕ → ℕ := fun n => (n + 2) ^ 10

/-- The class count `2^{Ch T^3} = 2^{T^3}`. -/
def cClassCount : ℕ → ℝ := fun n => (2 : ℝ) ^ (cT n) ^ 3

/-- The per-trial detection probability `1/2`. -/
def cPTrial : ℕ → ℝ := fun _ => 1 / 2

/-- The actual probe miss `(1/2)^{R n}`. -/
def cActualMiss : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (cR n)

/-- The placeholder `Li x` sequence.  It is chosen so that the bracket is
definitional; it is *not* the genuine logarithmic integral. -/
def cLiX : ℕ → ℝ := fun n => bracketTerm cCbr (cutoff cT) cF cT n + 1

/-- The placeholder `Li x^{β₀}` sequence. -/
def cLiBeta0 : ℕ → ℝ := fun _ => 1

/-- The cumulative Chebotarev count, chosen as the main term. -/
def cCount : ℕ → ℝ := fun n => mainOf cLiX cLiBeta0 n

/-- The inert count, chosen equal to the Chebotarev count. -/
def cInertCount : ℕ → ℝ := cCount

/-- The degree-one inert count, chosen equal to the inert count. -/
def cDegreeOneInert : ℕ → ℝ := cCount

/-! ## 2. Elementary positivity and arithmetic -/

theorem cC_pos : 0 < cC := by
  unfold cC
  positivity

theorem cC_le_one : cC ≤ 1 := by
  unfold cC
  rw [div_le_one (by positivity : (0 : ℝ) < 10 ^ 100)]
  simpa using one_le_pow₀ (a := (10 : ℝ)) (n := 100) (by norm_num)

theorem cC_le_inv256 : cC ≤ (1 : ℝ) / 256 := by
  unfold cC
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 256)
  have h256 : (256 : ℝ) ≤ 10 ^ 3 := by norm_num
  have hpow : (10 : ℝ) ^ 3 ≤ 10 ^ 100 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : 3 ≤ 100)
  linarith

theorem cC_log_nonpos : Real.log cC ≤ 0 :=
  Real.log_nonpos (le_of_lt cC_pos) cC_le_one

theorem cT_pos (n : ℕ) : 0 < cT n := by
  unfold cT
  positivity

theorem cT_two_le (n : ℕ) : 2 ≤ cT n := by
  unfold cT
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

theorem cCbr_pos : 0 < cCbr := by
  norm_num [cCbr]

theorem sqrt_half_le_sqrt_log_two_div_two :
    (1 / 2 : ℝ) ≤ Real.sqrt (Real.log 2 / 2) := by
  have hsq : ((1 / 2 : ℝ)) ^ 2 ≤ Real.log 2 / 2 := by
    nlinarith [Real.log_two_gt_d9]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h

/-! ## 3. The range input -/

theorem rangeInput : ChebotarevT6RangeInput cK cT cDegree cDiscLog := by
  refine chebotarevT6RangeInput_of_le_one_of_two_le ?hK0 ?hK1 ?hdeg ?hD ?hdegT
    ?hDT ?hT
  · norm_num [cK]
  · norm_num [cK]
  · intro n
    norm_num [cDegree]
  · intro n
    norm_num [cDiscLog]
  · intro n
    unfold cDegree cT
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  · intro n
    unfold cDiscLog cT
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  · intro n
    exact cT_two_le n

/-! ## 4. The vacuous zero-free field and the Stark field

The zero-free field is the explicit vacuous instance of
`Cogentic.RandomizedL34ZeroFaithful`: the zero sequence has real part `1/2`,
which never exceeds `beta0 = 3/4`, so the "above `beta0`" implication is
empty. -/

theorem zeroFreeInput : DedekindZeroFreeInput cBeta0 cZeroRealPart cCz cDiscLog where
  cz_pos := by norm_num [cCz]
  above_beta := by
    intro n hb
    unfold cBeta0 cZeroRealPart at hb
    norm_num at hb

theorem starkInput : StarkExceptionalZeroInput cBeta0 cF cDiscLog where
  F_pos := fun _ => one_pos
  discLog_pos := fun _ => one_pos
  no_exceptional_above := by
    intro n h
    unfold starkLine cBeta0 cF cDiscLog at h
    norm_num at h

/-! ## 5. The two logarithmic budgets at the concrete parameters -/

/-- The error budget at `C = 10^{-100}`, `cZ = 1`, `cbr = 128`, `F = 1`,
`T = n+2`, `degree = 1`. -/
theorem errorBudget_pointwise (n : ℕ) :
    Real.log (cC * (1 * (cT n) ^ 6) / (128 / 8)) ≤
      1 * Real.sqrt ((cT n) ^ 6 * Real.log 2 / (2 * 1)) := by
  by_cases hn : n ≤ 2
  · have hTle4 : cT n ≤ 4 := by
      unfold cT
      have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
      linarith
    have hTnonneg : 0 ≤ cT n := le_of_lt (cT_pos n)
    have hT6le : (cT n) ^ 6 ≤ (4 : ℝ) ^ 6 :=
      pow_le_pow_left₀ hTnonneg hTle4 6
    have hnum : cC * (cT n) ^ 6 ≤ 16 := by
      calc
        cC * (cT n) ^ 6 ≤ (1 / 256 : ℝ) * (cT n) ^ 6 :=
          mul_le_mul_of_nonneg_right cC_le_inv256 (pow_nonneg hTnonneg 6)
        _ ≤ (1 / 256 : ℝ) * (4 : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_left hT6le (by norm_num)
        _ = 16 := by norm_num
    have harg_le : cC * (1 * (cT n) ^ 6) / (128 / 8) ≤ 1 := by
      norm_num at hnum ⊢
      nlinarith
    have harg_nonneg : 0 ≤ cC * (1 * (cT n) ^ 6) / (128 / 8) := by
      apply div_nonneg
      · exact mul_nonneg (le_of_lt cC_pos)
          (mul_nonneg zero_le_one (pow_nonneg hTnonneg 6))
      · norm_num
    have hlog_le : Real.log (cC * (1 * (cT n) ^ 6) / (128 / 8)) ≤ 0 :=
      Real.log_nonpos harg_nonneg harg_le
    have hrhs_nonneg :
        0 ≤ 1 * Real.sqrt ((cT n) ^ 6 * Real.log 2 / (2 * 1)) := by
      have := Real.sqrt_nonneg ((cT n) ^ 6 * Real.log 2 / (2 * 1))
      linarith
    linarith
  · have hn3 : 3 ≤ n := by omega
    have ht4 : 4 ≤ cT n := by
      unfold cT
      have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have htpos : 0 < cT n := by linarith
    have hlog_eq :
        Real.log (cC * (1 * (cT n) ^ 6) / (128 / 8)) =
          Real.log cC + 6 * Real.log (cT n) - Real.log 16 := by
      simp only [one_mul]
      rw [show (128 / 8 : ℝ) = 16 by norm_num]
      rw [Real.log_div (mul_ne_zero (ne_of_gt cC_pos)
          (pow_ne_zero 6 (ne_of_gt htpos))) (by norm_num : (16 : ℝ) ≠ 0)]
      rw [Real.log_mul (ne_of_gt cC_pos) (pow_ne_zero 6 (ne_of_gt htpos))]
      rw [Real.log_pow]
      ring
    have h1 : Real.log cC + 6 * Real.log (cT n) - Real.log 16 ≤
        6 * Real.log (cT n) := by
      have h16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
      linarith [cC_log_nonpos]
    have h2 : 6 * Real.log (cT n) ≤ 12 * Real.sqrt (cT n) := by
      have hlr := Real.log_le_rpow_div (x := cT n) (ε := (1 / 2 : ℝ))
        (le_of_lt htpos) (by norm_num)
      have hsqrt : (cT n) ^ (1 / 2 : ℝ) = Real.sqrt (cT n) :=
        (Real.sqrt_eq_rpow (cT n)).symm
      have hlog_le : Real.log (cT n) ≤ 2 * Real.sqrt (cT n) := by
        calc
          Real.log (cT n) ≤ (cT n) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlr
          _ = 2 * (cT n) ^ (1 / 2 : ℝ) := by ring
          _ = 2 * Real.sqrt (cT n) := by rw [hsqrt]
      nlinarith
    have h3 : 12 * Real.sqrt (cT n) ≤ 6 * (cT n) := by
      have hs : Real.sqrt (cT n) ≤ cT n / 2 := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · nlinarith
      nlinarith
    have h4 : 6 * (cT n) ≤ (cT n) ^ 3 * Real.sqrt (Real.log 2 / 2) := by
      have hc : (2⁻¹ : ℝ) ≤ Real.sqrt (Real.log 2 / 2) := by
        simpa using sqrt_half_le_sqrt_log_two_div_two
      have ht2 : (16 : ℝ) ≤ (cT n) ^ 2 := by nlinarith
      have h6 : 6 * (cT n) ≤ (cT n) ^ 3 / 2 := by
        have hstep : 8 * (cT n) ≤ (cT n) ^ 3 / 2 := by
          rw [show (cT n) ^ 3 = (cT n) * (cT n) ^ 2 by ring]
          nlinarith [mul_le_mul_of_nonneg_left ht2 (le_of_lt htpos)]
        linarith
      have hstep : (cT n) ^ 3 / 2 ≤ (cT n) ^ 3 * Real.sqrt (Real.log 2 / 2) :=
        mul_le_mul_of_nonneg_left hc (pow_nonneg (le_of_lt htpos) 3)
      linarith
    have hrhs :
        Real.sqrt ((cT n) ^ 6 * Real.log 2 / (2 * 1)) =
          (cT n) ^ 3 * Real.sqrt (Real.log 2 / 2) := by
      have hsq : (cT n) ^ 6 * Real.log 2 / (2 * 1) =
          ((cT n) ^ 3) ^ 2 * (Real.log 2 / 2) := by ring
      rw [hsq, Real.sqrt_mul (sq_nonneg ((cT n) ^ 3)),
        Real.sqrt_sq (by positivity)]
    rw [hlog_eq, hrhs]
    simp only [one_mul]
    linarith

theorem errorLogBudget : ChebotarevErrorLogBudget cC cCZ cCbr cF cT cDegree := by
  intro n
  simpa [ChebotarevErrorLogBudget, cCZ, cCbr, cF, cDegree] using
    errorBudget_pointwise n

/-- The discarded-ideal budget at `cbr = 128`, `degree = F = 1`, `T = n+2`. -/
theorem degreeLossLogBudget_pointwise (n : ℕ) :
    Real.log (1 * 1 * (cT n) ^ 6 / (128 / 8)) ≤
      (cT n) ^ 6 / 2 * Real.log 2 := by
  have ht2 : 2 ≤ cT n := cT_two_le n
  have htpos : 0 < cT n := cT_pos n
  have hlog_eq : Real.log (1 * 1 * (cT n) ^ 6 / (128 / 8)) =
      6 * Real.log (cT n) - Real.log 16 := by
    simp only [one_mul]
    rw [show (128 / 8 : ℝ) = 16 by norm_num]
    rw [Real.log_div (pow_ne_zero 6 (ne_of_gt htpos))
      (by norm_num : (16 : ℝ) ≠ 0)]
    rw [Real.log_pow]
    ring
  rw [hlog_eq]
  have h1 : 6 * Real.log (cT n) - Real.log 16 ≤ 6 * Real.log (cT n) := by
    have h16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : 6 * Real.log (cT n) ≤ 6 * (cT n) := by
    nlinarith [Real.log_le_self (le_of_lt htpos)]
  have h3 : 6 * (cT n) ≤ (cT n) ^ 6 / 4 := by
    have ht5 : (24 : ℝ) ≤ (cT n) ^ 5 := by
      have hpow : (2 : ℝ) ^ 5 ≤ (cT n) ^ 5 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ht2 5
      norm_num at hpow ⊢
      linarith
    rw [show (cT n) ^ 6 = (cT n) * (cT n) ^ 5 by ring]
    nlinarith [mul_le_mul_of_nonneg_left ht5 (le_of_lt htpos)]
  have h4 : (cT n) ^ 6 / 4 ≤ (cT n) ^ 6 / 2 * Real.log 2 := by
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have ht6nonneg : 0 ≤ (cT n) ^ 6 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hl2 ht6nonneg]
  linarith

theorem degreeLogBudget : DegreeLossLogBudget cCbr cDegree cF cT := by
  intro n
  simpa [DegreeLossLogBudget, cCbr, cF, cDegree] using
    degreeLossLogBudget_pointwise n

/-! ## 6. The effective-Chebotarev statement -/

theorem residualInput :
    ChebotarevResidualInput cC cCZ (cutoff cT) cDegree cCount cLiX cLiBeta0 where
  C_pos := cC_pos
  cZ_pos := by norm_num [cCZ]
  residual := by
    intro n
    have herr_nonneg : 0 ≤ lagariasOdlyzkoError cC cCZ (cutoff cT) cDegree n :=
      lagariasOdlyzkoError_nonneg (le_of_lt cC_pos)
        (fun m => (cutoff_pos cT m).le) n
    have hzero : cCount n - mainOf cLiX cLiBeta0 n = 0 := by
      unfold cCount
      ring
    rw [hzero, abs_zero]
    exact herr_nonneg

theorem effectiveStatement :
    EffectiveChebotarevStatement cK cC cCZ (cutoff cT) cDegree cDiscLog
      cCount cLiX cLiBeta0 :=
  effectiveChebotarevStatement_of_residual_of_rangeInput
    (K := cK) (C := cC) (cZ := cCZ) (T := cT) (degree := cDegree)
    (discLog := cDiscLog) (count := cCount) (liX := cLiX) (liBeta0 := cLiBeta0)
    (by norm_num [cK]) residualInput rangeInput
    (fun n => by norm_num [cDegree])

/-! ## 7. The bracket placeholder and its faithful failure -/

theorem bracketSynthetic :
    LogIntegralBracket cCbr (cutoff cT) cF cT cLiX cLiBeta0 := by
  refine ⟨cCbr_pos, ?_⟩
  intro n
  unfold cLiX cLiBeta0
  have h : bracketTerm cCbr (cutoff cT) cF cT n + 1 - 1 =
      bracketTerm cCbr (cutoff cT) cF cT n := by ring
  rw [h]

/-- **The upper bound for `Li b - Li a`.**  On `[a,b]`, `1/log t ≤ 1/log a`. -/
theorem Li_sub_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Li b - Li a ≤ (b - a) / Real.log a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hfi_b := intervalIntegrable_inv_log_two hb
  have hfi_a := intervalIntegrable_inv_log_two ha
  have hsub : Li b - Li a = ∫ t in a..b, (Real.log t)⁻¹ := by
    unfold Li
    exact integral_interval_sub_left hfi_b hfi_a
  have hfi_ab := intervalIntegrable_inv_log_of_one_lt ha hab
  have hpoint : ∀ t ∈ Set.Icc a b, (Real.log t)⁻¹ ≤ (Real.log a)⁻¹ := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hloga : 0 < Real.log a := Real.log_pos ha
    have hle : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    simpa [one_div] using one_div_le_one_div_of_le hloga hle
  have hmono : (∫ t in a..b, (Real.log t)⁻¹) ≤ ∫ t in a..b, (Real.log a)⁻¹ :=
    integral_mono_on (μ := volume) (a := a) (b := b) hab hfi_ab
      intervalIntegrable_const hpoint
  have hconst : (∫ t in a..b, (Real.log a)⁻¹) = (b - a) * (Real.log a)⁻¹ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hsub]
  calc
    ∫ t in a..b, (Real.log t)⁻¹ ≤ ∫ t in a..b, (Real.log a)⁻¹ := hmono
    _ = (b - a) * (Real.log a)⁻¹ := hconst
    _ = (b - a) / Real.log a := by rw [div_eq_mul_inv]

/-- **The faithful bracket at `cbr = 128` is false.**  With the genuine
logarithmic integral, `Li x - Li x^{3/4} ≤ x/(48 log 2)`, while at `n = 0` the
bracket demands `2x`. -/
theorem bracketPaper_fails :
    ¬ LogIntegralBracket cCbr (cutoff cT) cF cT
      (paperLiX cT) (paperLiBeta0 cBeta0 cT) := by
  rintro ⟨_, h⟩
  let x : ℝ := cutoff cT 0
  have hxpos : 0 < x := cutoff_pos cT 0
  have hT0 : cT 0 = 2 := by norm_num [cT]
  have hxlog : Real.log x = 64 * Real.log 2 := by
    unfold x
    rw [cutoff_log]
    unfold cT
    norm_num
  have hx1 : 1 < x := by
    have hlogpos : 0 < Real.log x := by
      rw [hxlog]
      positivity
    exact (Real.log_pos_iff (le_of_lt hxpos)).mp hlogpos
  have hbeta_pos : 0 < cBeta0 0 := by norm_num [cBeta0]
  have hbeta_le_one : cBeta0 0 ≤ 1 := by norm_num [cBeta0]
  have hY1 : 1 < x ^ cBeta0 0 := Real.one_lt_rpow hx1 hbeta_pos
  have hYX : x ^ cBeta0 0 ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hbeta_le_one
  have hupper0 : Li x - Li (x ^ cBeta0 0) ≤
      (x - x ^ cBeta0 0) / Real.log (x ^ cBeta0 0) :=
    Li_sub_le hY1 hYX
  have hdenpos : 0 < Real.log (x ^ cBeta0 0) := Real.log_pos hY1
  have hYnonneg : 0 ≤ x ^ cBeta0 0 := le_of_lt (Real.rpow_pos_of_pos hxpos _)
  have hfrac : (x - x ^ cBeta0 0) / Real.log (x ^ cBeta0 0) ≤
      x / Real.log (x ^ cBeta0 0) := by
    apply div_le_div_of_nonneg_right _ hdenpos.le
    linarith
  have hlogY : Real.log (x ^ cBeta0 0) = 48 * Real.log 2 := by
    rw [Real.log_rpow hxpos]
    unfold cBeta0
    rw [hxlog]
    ring
  have hupper : Li x - Li (x ^ cBeta0 0) ≤ x / (48 * Real.log 2) := by
    calc
      Li x - Li (x ^ cBeta0 0)
          ≤ (x - x ^ cBeta0 0) / Real.log (x ^ cBeta0 0) := hupper0
      _ ≤ x / Real.log (x ^ cBeta0 0) := hfrac
      _ = x / (48 * Real.log 2) := by rw [hlogY]
  have hbracket : bracketTerm cCbr (cutoff cT) cF cT 0 = 2 * x := by
    unfold bracketTerm cF cCbr x
    rw [hT0]
    norm_num
    ring
  have h0 := h 0
  have hle : 2 * x ≤ x / (48 * Real.log 2) := by
    calc
      2 * x = bracketTerm cCbr (cutoff cT) cF cT 0 := hbracket.symm
      _ ≤ paperLiX cT 0 - paperLiBeta0 cBeta0 cT 0 := h0
      _ = Li x - Li (x ^ cBeta0 0) := rfl
      _ ≤ x / (48 * Real.log 2) := hupper
  have hdiv : 2 ≤ 1 / (48 * Real.log 2) := by
    have hle' : x * 2 ≤ x * (1 / (48 * Real.log 2)) := by
      calc
        x * 2 = 2 * x := by ring
        _ ≤ x / (48 * Real.log 2) := hle
        _ = x * (1 / (48 * Real.log 2)) := by rw [div_eq_mul_inv, one_div]
    exact (mul_le_mul_iff_of_pos_left hxpos).mp hle'
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h96 : 96 * Real.log 2 ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 48 * Real.log 2)).mp hdiv
    nlinarith
  nlinarith [Real.log_two_gt_d9]

/-! ## 8. Probe selection, budget, class count and union bound -/

theorem degreeOneReduction :
    DegreeOneInertReduction cInertCount cDegreeOneInert cDegree (cutoff cT) := by
  intro n
  unfold cInertCount cDegreeOneInert cDegree
  simp only [one_mul]
  linarith [Real.sqrt_nonneg (cutoff cT n)]

theorem selectionInput :
    ProbeSelectionLowerBound cCsel (cutoff cT) cDegree cDegreeOneInert cPTrial where
  left := by norm_num [cCsel]
  right := by
    intro n
    have hmain : mainOf cLiX cLiBeta0 n =
        bracketTerm cCbr (cutoff cT) cF cT n / 2 := by
      unfold mainOf cLiX cLiBeta0 cCbr
      ring
    have hcut : cutoff cT n ≠ 0 := ne_of_gt (cutoff_pos cT n)
    have hTne : cT n ≠ 0 := ne_of_gt (cT_pos n)
    have heq : (1 / 16 : ℝ) *
          (bracketTerm cCbr (cutoff cT) cF cT n / 2) / (1 * cutoff cT n) =
        4 / (cT n) ^ 6 := by
      unfold bracketTerm cF cCbr
      field_simp [hcut, hTne]
      ring
    unfold cCsel cPTrial cDegreeOneInert cCount cDegree
    rw [hmain, heq]
    have hT6 : (64 : ℝ) ≤ (cT n) ^ 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (cT n) ^ 6 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (cT_two_le n) 6
      norm_num at hpow ⊢
      linarith
    rw [div_le_iff₀ (pow_pos (cT_pos n) 6)]
    nlinarith

theorem budgetInput : ProbeBudget cR cF cT := by
  intro n
  unfold cR cF cT
  push_cast
  ring

theorem classCountPos (n : ℕ) : 0 < cClassCount n := by
  unfold cClassCount
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem classCubicInput : ClassCountCubicInput cCh cClassCount cT where
  Ch_pos := by norm_num [cCh]
  cubic := by
    intro n
    unfold cClassCount cCh
    norm_num

theorem constantMargin : cCh * Real.log 2 < cCsel * cCbr / 4 := by
  norm_num [cCh, cCsel, cCbr]
  nlinarith [Real.log_two_lt_d9]

theorem scaleCubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (cCsel * cCbr / 4 - cCh * Real.log 2) * (cT n) ^ 3 := by
  have hcoef : (1 : ℝ) ≤ cCsel * cCbr / 4 - cCh * Real.log 2 := by
    norm_num [cCsel, cCbr, cCh]
    nlinarith [Real.log_two_lt_d9]
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog3 : 1 ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      Real.exp_one_lt_three.le
  have hlogn_ge3 : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlog1 : 1 ≤ Real.log n := le_trans hlog3 hlogn_ge3
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le zero_lt_one hlog1
  have hloglog : Real.log (Real.log n) ≤ Real.log n :=
    Real.log_le_self (le_of_lt hlogpos)
  have hloglog_nonneg : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1
  have hscale : scale n ≤ Real.log n := by
    unfold scale
    calc
      (Real.log n) ^ (1 / 3 : ℝ) * (Real.log (Real.log n)) ^ (2 / 3 : ℝ)
          ≤ (Real.log n) ^ (1 / 3 : ℝ) * (Real.log n) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hloglog_nonneg hloglog (by norm_num))
          (Real.rpow_nonneg (le_of_lt hlogpos) _)
      _ = Real.log n := by
        rw [← Real.rpow_add hlogpos]
        norm_num
  have hlog_le_n : Real.log n ≤ n := Real.log_le_self (by positivity)
  have h2 : 2 * scale n ≤ 2 * n := by nlinarith
  have h3 : 2 * n ≤ (cT n) ^ 3 := by
    unfold cT
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have h4 : (cT n) ^ 3 ≤
      (cCsel * cCbr / 4 - cCh * Real.log 2) * (cT n) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef
      (pow_nonneg (le_of_lt (cT_pos n)) 3)]
  linarith

theorem actualMissNonneg (n : ℕ) : 0 ≤ cActualMiss n := by
  unfold cActualMiss
  positivity

theorem unionBoundInput :
    ProbeMissUnionBound cActualMiss cPTrial cClassCount cR := by
  intro n
  have hclass : (1 : ℝ) ≤ cClassCount n := by
    unfold cClassCount
    exact Real.one_le_rpow (by norm_num) (pow_nonneg (le_of_lt (cT_pos n)) 3)
  have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (cR n) := pow_nonneg (by norm_num) _
  have hstep : (1 : ℝ) ≤ (2 : ℝ) ^ (cT n) ^ 3 := by
    simpa [cClassCount] using hclass
  unfold cActualMiss cPTrial cClassCount
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hsub]
  nlinarith [mul_le_mul_of_nonneg_right hstep hpow_nonneg]

theorem pTrialNonneg (n : ℕ) : 0 ≤ cPTrial n := by
  unfold cPTrial
  norm_num

theorem pTrialLeOne (n : ℕ) : cPTrial n ≤ 1 := by
  unfold cPTrial
  norm_num

/-! ## 9. The full inhabitant -/

/-- **The explicit inhabitant.**  Every field is proved at the concrete toy
parameters.  The `bracket` field uses the free placeholder sequences `cLiX` and
`cLiBeta0`; the faithful version of that single field is false
(`bracketPaper_fails`). -/
noncomputable def effectiveInhabitant : L34EffectiveChebotarevInputs where
  beta0 := cBeta0
  zeroRealPart := cZeroRealPart
  degree := cDegree
  discLog := cDiscLog
  F := cF
  T := cT
  count := cCount
  inertCount := cInertCount
  degreeOneInert := cDegreeOneInert
  liX := cLiX
  liBeta0 := cLiBeta0
  pTrial := cPTrial
  actualMiss := cActualMiss
  classCount := cClassCount
  R := cR
  K := cK
  C := cC
  cZ := cCZ
  cz := cCz
  cbr := cCbr
  csel := cCsel
  Ch := cCh
  zeroFree := zeroFreeInput
  stark := starkInput
  range := rangeInput
  T_ge_one := fun n => le_of_lt (by
    unfold cT
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith)
  effective := effectiveStatement
  inert_ge_count := fun _ => le_rfl
  bracket := bracketSynthetic
  error_log := errorLogBudget
  degree_log := degreeLogBudget
  degree_one_reduction := degreeOneReduction
  selection := selectionInput
  budget := budgetInput
  classCount_pos := classCountPos
  classCubic := classCubicInput
  constant_margin := constantMargin
  scale_cubic := scaleCubic
  actualMiss_nonneg := actualMissNonneg
  union_bound := unionBoundInput
  pTrial_nonneg := pTrialNonneg
  pTrial_le_one := pTrialLeOne

/-! ## 10. The faithful obstruction and the non-zero loss -/

/-- **No faithful inhabitant at these constants.**  If the free `Li` fields are
the genuine `paperLiX`/`paperLiBeta0` and `cbr = 128`, the bundle is
uninhabited: its bracket field would contradict `bracketPaper_fails`. -/
theorem no_faithful_inhabitant :
    ¬ ∃ S : L34EffectiveChebotarevInputs,
        S.beta0 = cBeta0 ∧ S.zeroRealPart = cZeroRealPart ∧
        S.degree = cDegree ∧ S.discLog = cDiscLog ∧ S.F = cF ∧ S.T = cT ∧
        S.liX = paperLiX cT ∧ S.liBeta0 = paperLiBeta0 cBeta0 cT ∧
        S.cbr = cCbr := by
  rintro ⟨S, _hβ, _hZ, _hd, _hD, hF, hT, hliX, hliB, hcbr⟩
  have hb := S.bracket
  rw [hcbr, hT, hF, hliX, hliB] at hb
  exact bracketPaper_fails hb

/-- The assembled core's loss is exactly the actual probe miss. -/
theorem inhabitant_loss_eq (n : ℕ) :
    effectiveInhabitant.toL34ChebotarevSidesInputs.toL34SidesCore.loss n =
      cActualMiss n :=
  effectiveInhabitant.toL34ChebotarevSidesInputs.toL34SidesCore_loss n

/-- **The loss is positive, not zero.**  It equals the actual probe miss
`(1/2)^{R n}`. -/
theorem inhabitant_loss_pos (n : ℕ) :
    0 < effectiveInhabitant.toL34ChebotarevSidesInputs.toL34SidesCore.loss n := by
  rw [inhabitant_loss_eq]
  unfold cActualMiss
  exact pow_pos (by norm_num) _

/-- The loss satisfies the ledger bound through the reduced bundle. -/
theorem inhabitant_loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      effectiveInhabitant.toL34ChebotarevSidesInputs.toL34SidesCore.loss n ≤
        exp (-(2 : ℝ) * scale n) :=
  effectiveInhabitant.toL34ChebotarevSidesInputs.loss_le_ledger

/-! ## Axiom audit -/

#print axioms rangeInput
#print axioms zeroFreeInput
#print axioms starkInput
#print axioms errorLogBudget
#print axioms degreeLogBudget
#print axioms residualInput
#print axioms effectiveStatement
#print axioms bracketSynthetic
#print axioms Li_sub_le
#print axioms bracketPaper_fails
#print axioms degreeOneReduction
#print axioms selectionInput
#print axioms budgetInput
#print axioms classCubicInput
#print axioms constantMargin
#print axioms scaleCubic
#print axioms unionBoundInput
#print axioms effectiveInhabitant
#print axioms no_faithful_inhabitant
#print axioms inhabitant_loss_eq
#print axioms inhabitant_loss_pos
#print axioms inhabitant_loss_le_ledger

end

end Cogentic.RandomizedL34EffectiveInhabitant
