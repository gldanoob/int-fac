import Cogentic.RandomizedPaperEndpointWave14
import Cogentic.RandomizedL30Sharp
import Cogentic.RandomizedL30GlobalLower

set_option maxHeartbeats 2000000

/-!
# A non-vacuous witness for the sharp L30 counts

`RandomizedPaperEndpointWave14.Wave14L30Counts` now carries the *sharp*
density fields `YounisOddPaperSharpIntervalCount c p ε` and
`GlobalOddUpperDensitySharp C p ε`, i.e. the true Dickman factor
`exp (-(u log u))`.  This file constructs an explicit inhabitant at the
constant scale `p = 4` and records that both sharp fields are satisfied by
genuine, strictly positive counts (the central odd count is `1`, the global odd
count is `4`).

The witness normalises the paper cutoff to `768`, so
`(1+ε) t_p = log 768` and
`u = 2 log 4 / log 768 ∈ (1/4, 1)`.  The constants are

```
A = 1/4,   B = 16,   c = 1/16,   C = 1/4 .
```

The sharp local bound is `(1/16) · 5 · exp (-(u log u)) ≤ 1`, which follows
from `u ∈ [1/4, 1]`, `-(u log u) ≤ 1 - u ≤ 3/4` and
`exp (3/4) < exp 1 < 16/5`.  The sharp global bound is
`4 / 16 ≤ (1/4) exp (-(u log u))`, which follows from
`exp (-(u log u)) ≥ 1`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count or loss
is set to zero.
-/

namespace Cogentic.RandomizedL30SharpWitness

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedPaperEndpointWave14

noncomputable section

/-- The constant prime scale of the witness. -/
def wP : ℕ → ℝ := fun _ => 4

/-- The paper scale `t_p` at `p = 4`. -/
def wT0 : ℝ := Real.sqrt (Real.log 4 * Real.log (Real.log 4))

/-- The relative error normalising the paper cutoff to `768`. -/
def wEps : ℝ := Real.log 768 / wT0 - 1

/-- The witness relative-error sequence. -/
def wErr : ℕ → ℝ := fun _ => wEps

lemma log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  nlinarith [Real.log_two_gt_d9]

theorem wT0_pos : 0 < wT0 := by
  unfold wT0
  exact Real.sqrt_pos_of_pos
    (mul_pos (by linarith [log_four_gt_one]) (Real.log_pos log_four_gt_one))

theorem wT0_ne_zero : wT0 ≠ 0 := wT0_pos.ne'

/-- The paper scale at the witness is the constant `wT0`. -/
theorem w_paperT (n : ℕ) : paperT wP n = wT0 := rfl

/-- The witness normalisation `(1+ε)t = log 768`. -/
theorem w_one_add_err_mul (n : ℕ) :
    (1 + wErr n) * paperT wP n = Real.log 768 := by
  rw [w_paperT]
  unfold wErr wEps
  field_simp [wT0_ne_zero]
  ring

/-- The paper cutoff at the witness is exactly `768`. -/
theorem w_cutoff (n : ℕ) : smoothCutoff (paperT wP) wErr n = 768 := by
  unfold smoothCutoff
  rw [w_one_add_err_mul, Real.exp_log (by norm_num)]

/-- The exponential factor at the witness is `1/768`. -/
theorem w_exp_neg (n : ℕ) :
    Real.exp (-(1 + wErr n) * paperT wP n) = 1 / 768 := by
  rw [show -(1 + wErr n) * paperT wP n =
      -((1 + wErr n) * paperT wP n) by ring]
  rw [w_one_add_err_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- The Dickman parameter at the witness. -/
theorem w_paperDensityU (n : ℕ) :
    paperDensityU wP wEps n = 2 * Real.log 4 / Real.log 768 := by
  unfold paperDensityU
  rw [w_paperT]
  have h : (1 + wEps) * wT0 = Real.log 768 := by
    simpa only [wErr, w_paperT] using w_one_add_err_mul n
  rw [h]
  norm_num [wP]

theorem w_log768_pos : 0 < Real.log 768 := Real.log_pos (by norm_num)

theorem w_two_log_four_pos : 0 < 2 * Real.log 4 := by
  nlinarith [log_four_gt_one]

theorem wU_pos (n : ℕ) : 0 < paperDensityU wP wEps n := by
  rw [w_paperDensityU]
  exact div_pos w_two_log_four_pos w_log768_pos

/-- `2 log 4 ≤ log 768`. -/
theorem w_two_log_four_le_log768 : 2 * Real.log 4 ≤ Real.log 768 := by
  have h16 : (16 : ℝ) ≤ 768 := by norm_num
  have hlog : Real.log 16 ≤ Real.log 768 :=
    Real.log_le_log (by norm_num) h16
  have h16eq : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- `log 768 ≤ 8 log 4`. -/
theorem w_log768_le_eight : Real.log 768 ≤ 8 * Real.log 4 := by
  have hpow : (768 : ℝ) ≤ 4 ^ 8 := by norm_num
  have hlog : Real.log 768 ≤ Real.log (4 ^ 8) :=
    Real.log_le_log (by norm_num) hpow
  have h4 : Real.log (4 ^ 8) = 8 * Real.log 4 := by
    rw [Real.log_pow]
    norm_num
  linarith

theorem wU_le_one (n : ℕ) : paperDensityU wP wEps n ≤ 1 := by
  rw [w_paperDensityU]
  rw [div_le_iff₀ w_log768_pos]
  linarith [w_two_log_four_le_log768]

theorem wU_ge_quarter (n : ℕ) : (1 : ℝ) / 4 ≤ paperDensityU wP wEps n := by
  rw [w_paperDensityU]
  rw [le_div_iff₀ w_log768_pos]
  linarith [w_log768_le_eight]

/-- `-(u log u) ≥ 0` at the witness. -/
theorem w_neg_u_log_nonneg (n : ℕ) :
    0 ≤ -(paperDensityU wP wEps n * Real.log (paperDensityU wP wEps n)) := by
  have hu0 := wU_pos n
  have hu1 := wU_le_one n
  have hlog : Real.log (paperDensityU wP wEps n) ≤ 0 :=
    Real.log_nonpos hu0.le hu1
  have : paperDensityU wP wEps n * Real.log (paperDensityU wP wEps n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu0.le hlog
  linarith

/-- `exp (-(u log u)) ≥ 1` at the witness. -/
theorem w_exp_ge_one (n : ℕ) :
    1 ≤ Real.exp (-(paperDensityU wP wEps n *
      Real.log (paperDensityU wP wEps n))) := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (w_neg_u_log_nonneg n)

/-- The elementary bound `-(u log u) ≤ 1 - u`. -/
theorem w_neg_u_log_le_one_sub (n : ℕ) :
    -(paperDensityU wP wEps n * Real.log (paperDensityU wP wEps n)) ≤
      1 - paperDensityU wP wEps n := by
  have hu0 := wU_pos n
  have hlog : Real.log (1 / paperDensityU wP wEps n) ≤
      1 / paperDensityU wP wEps n - 1 :=
    Real.log_le_sub_one_of_pos (one_div_pos.mpr hu0)
  have hmul := mul_le_mul_of_nonneg_left hlog hu0.le
  have hrewrite : paperDensityU wP wEps n *
      Real.log (1 / paperDensityU wP wEps n) =
        -(paperDensityU wP wEps n * Real.log (paperDensityU wP wEps n)) := by
    rw [Real.log_div one_ne_zero hu0.ne', Real.log_one]
    ring
  have hone : paperDensityU wP wEps n *
      (1 / paperDensityU wP wEps n - 1) = 1 - paperDensityU wP wEps n := by
    field_simp [hu0.ne']
  calc
    -(paperDensityU wP wEps n * Real.log (paperDensityU wP wEps n))
        = paperDensityU wP wEps n *
            Real.log (1 / paperDensityU wP wEps n) := hrewrite.symm
    _ ≤ paperDensityU wP wEps n *
          (1 / paperDensityU wP wEps n - 1) := hmul
    _ = 1 - paperDensityU wP wEps n := hone

/-- `exp (-(u log u)) ≤ exp (3/4)` at the witness. -/
theorem w_exp_le_three_quarters (n : ℕ) :
    Real.exp (-(paperDensityU wP wEps n *
      Real.log (paperDensityU wP wEps n))) ≤ Real.exp ((3 : ℝ) / 4) := by
  apply Real.exp_le_exp.mpr
  have h := w_neg_u_log_le_one_sub n
  have hq := wU_ge_quarter n
  linarith

/-- The numeric bound `exp (-(u log u)) < 16/5`. -/
theorem w_exp_lt_sixteen_fifths (n : ℕ) :
    Real.exp (-(paperDensityU wP wEps n *
      Real.log (paperDensityU wP wEps n))) < (16 : ℝ) / 5 := by
  calc
    Real.exp (-(paperDensityU wP wEps n *
        Real.log (paperDensityU wP wEps n)))
        ≤ Real.exp ((3 : ℝ) / 4) := w_exp_le_three_quarters n
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    _ < 3 := Real.exp_one_lt_three
    _ < (16 : ℝ) / 5 := by norm_num

/-- A number at most `y` is `y`-smooth. -/
lemma smooth_of_le {y : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ y) : IsSmoothUpTo y m := by
  intro q hq
  have hdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
  have hmne : m ≠ 0 := (Nat.mem_primeFactors.mp hq).2.2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
  have hqm : q ≤ m := Nat.le_of_dvd hmpos hdvd
  have hqmR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hqm
  exact hqmR.trans hm

/-- The odd-half filter is the arithmetic progression `m % 4 = 2`. -/
lemma oddHalf_filter_eq (s : Finset ℕ) :
    s.filter IsOddHalfOrder = s.filter (fun m => m % 4 = 2) := by
  apply Finset.filter_congr
  intro x _
  rfl

theorem w_centralInterval (n : ℕ) :
    centralOrderInterval wP n = Finset.Icc 12 16 := by
  simp [centralOrderInterval, wP]
  norm_num

theorem w_centralSmooth (n : ℕ) :
    centralSmoothOrders wP (paperT wP) wErr n = Finset.Icc 12 16 := by
  classical
  rw [centralSmoothOrders, w_centralInterval]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [w_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

theorem w_centralOdd (n : ℕ) :
    centralOddSmoothOrders wP (paperT wP) wErr n = ({14} : Finset ℕ) := by
  rw [centralOddSmoothOrders, w_centralSmooth, oddHalf_filter_eq]
  decide

theorem w_centralOddCount (n : ℕ) :
    centralOddSmoothCount wP (paperT wP) wErr n = 1 := by
  unfold centralOddSmoothCount
  rw [w_centralOdd]
  norm_num

theorem w_globalSmooth (n : ℕ) :
    globalSmoothOrders wP (paperT wP) wErr n = Finset.Icc 1 16 := by
  classical
  unfold globalSmoothOrders
  rw [show ⌊wP n ^ 2⌋₊ = 16 by norm_num [wP]]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [w_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

theorem w_globalOdd (n : ℕ) :
    globalOddSmoothOrders wP (paperT wP) wErr n = ({2, 6, 10, 14} : Finset ℕ) := by
  rw [globalOddSmoothOrders, w_globalSmooth, oddHalf_filter_eq]
  decide

theorem w_globalOddCount (n : ℕ) :
    globalOddSmoothCount wP (paperT wP) wErr n = 4 := by
  unfold globalOddSmoothCount
  rw [w_globalOdd]
  norm_num

theorem w_p_ge_two (n : ℕ) : 2 ≤ wP n := by norm_num [wP]

theorem w_err_ge_neg_one (n : ℕ) : -1 ≤ wErr n := by
  unfold wErr wEps
  have h : 0 ≤ Real.log 768 / wT0 :=
    div_nonneg (Real.log_nonneg (by norm_num)) wT0_pos.le
  linarith

/-- **The explicit sharp `Wave14L30Counts` inhabitant.** -/
noncomputable def witnessL30Counts : Wave14L30Counts where
  p := wP
  err := wErr
  ε := wEps
  err_eq := rfl
  p_ge_two := w_p_ge_two
  err_ge_neg_one := w_err_ge_neg_one
  fibreModels := lppModelMultiples wP
  A := 1 / 4
  B := 16
  c := 1 / 16
  C := 1 / 4
  A_pos := by norm_num
  B_pos := by norm_num
  AB_ge_four := by norm_num
  AC_le := by norm_num
  short_interval := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hcount : centralOddSmoothCount wP (paperT wP) (paperError wEps) n = 1 := by
      rw [show paperError wEps = wErr from rfl]
      exact w_centralOddCount n
    rw [hcount, w_centralInterval]
    have hcard : ((Finset.Icc 12 16).card : ℝ) = 5 := by norm_num
    rw [hcard]
    have hE := (w_exp_lt_sixteen_fifths n).le
    nlinarith
  global_upper := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hcount : globalOddSmoothCount wP (paperT wP) (paperError wEps) n = 4 := by
      rw [show paperError wEps = wErr from rfl]
      exact w_globalOddCount n
    rw [hcount]
    have hp2 : wP n ^ 2 = 16 := by norm_num [wP]
    rw [hp2]
    have hE := w_exp_ge_one n
    nlinarith
  global_binomial := by
    intro n
    have hcut : smoothCutoff (paperT wP) wErr n = 768 := w_cutoff n
    refine ⟨?_, {3}, 0, ?_, ?_, ?_⟩
    · rw [hcut]
      norm_num
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst q
      exact ⟨Nat.prime_three, by norm_num, by rw [hcut]; norm_num⟩
    · rw [hcut]
      norm_num [wP]
    · rw [w_exp_neg]
      norm_num [wP]
  lpp_superset := lppModelSuperset_multiples wP (paperT wP) wErr

/-- **The sharp L30 count bundle is inhabited.** -/
theorem nonempty_wave14L30Counts : Nonempty Wave14L30Counts :=
  ⟨witnessL30Counts⟩

/-- The witness keeps the genuine central odd count `1`. -/
theorem witness_centralCount (n : ℕ) :
    centralOddSmoothCount wP (paperT wP) wErr n = 1 :=
  w_centralOddCount n

/-- The witness keeps the genuine global odd count `4`. -/
theorem witness_globalCount (n : ℕ) :
    globalOddSmoothCount wP (paperT wP) wErr n = 4 :=
  w_globalOddCount n

/-- The sharp upper field is satisfied, hence it is not refuted. -/
theorem witness_sharpUpper :
    GlobalOddUpperDensitySharp (1 / 4) wP wEps :=
  witnessL30Counts.global_upper

/-- The sharp local field is satisfied, hence it is not refuted. -/
theorem witness_sharpLocal :
    YounisOddPaperSharpIntervalCount (1 / 16) wP wEps :=
  witnessL30Counts.short_interval

/-! ## Axiom audit -/

#print axioms witnessL30Counts
#print axioms nonempty_wave14L30Counts
#print axioms witness_sharpUpper
#print axioms witness_sharpLocal

end

end Cogentic.RandomizedL30SharpWitness
