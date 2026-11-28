import Cogentic.RandomizedPaperEndpointWave14

/-!
# L30 non-vacuity after the density repair

`Cogentic/RandomizedPaperEndpointWave14.lean` repaired the L30 count bundle by
replacing the fixed-density short-interval count

```
YounisOddShortIntervalCount c p (paperT p) err :
  ∀ n, c * p_n^{3/2} ≤ centralOddSmoothCount p (paperT p) err n
```

with the paper-scale density form

```
YounisOddPaperShortCount c p (paperT p) err :
  ∀ n, c * p_n^{3/2} * exp (-(1+ε_n) t_{p_n})
        ≤ centralOddSmoothCount p (paperT p) err n .
```

This file records two things.

## 1. The repair is a genuine repair

The old bundle is refuted in the isolated namespace
`OldFixedDensityObstruction`: the fixed-density count forces `c ≤ 1` (the
central interval has at most `p^{3/2}` integers), while the global binomial
lower bound and the global upper density force `B ≤ C`, hence
`4 ≤ A B ≤ A C ≤ c`.  The exact theorem is
`OldFixedDensityObstruction.fixedDensity_obstruction`, and the old count
record is shown empty.

The repaired paper-scale bundle is *inhabited*.  The witness is the constant
scale `p = 4` (the formal record only requires `p ≥ 2`), with the paper cutoff
normalised to `Y = 768`:

```
p n = 4,      t = t_p,      (1 + ε_n) t_p = log 768,
A = 1/8,  B = 48,  c = 24,  C = 192 .
```

At this scale the central interval is `(12, 16]`, whose only odd-half order is
`14`, and the global odd-half smooth range below `p^2 = 16` is
`{2, 6, 10, 14}`.  Thus the two count fields are the genuine nonzero numbers
`1` and `4`, the short-count lower side is `1/4`, and the global upper side is
the equality `4/16 = 192/768`.  The global binomial count is supplied by the
single odd prime `3` with exponent `0`: its binomial coefficient is `1`, and
the target is `48 · 16 / 768 = 1`.

## 2. `FailureData` and the L30 inputs are inhabited

`Wave14L30Counts` is nonempty.  The guarded tree-size bound
`FactorTreeNodes nodes := ∀ n, 1 ≤ n → nodes n ≤ 2 n` no longer forces
`nodes 0 = 0`, so the `n = 0` union bound no longer contradicts `failure_pos`.
The explicit witness `witnessFailureData` takes `nodes n = 1` everywhere and a
strictly positive failure probability at every index.

Combining `witnessL30Counts`, `witnessCantor` and `witnessFailureData` gives
`Nonempty Wave14L30Inputs`.

For `Wave14Inputs`, the remaining fields outside L30 still need explicit
witnesses: L18.4, L19, L20.2, L20.4, L21.2, L27, L34, P1, C1–C5, the L4
modulus, and the concrete/C5 adapter data.  These are not constructed here.

**Scope of the count witness.**  The witness `p = 4` is a constant-scale
instance.  It proves that the formal record has an inhabitant and that the
repaired fields are mutually consistent; it does not assert the paper's
asymptotic density estimate as `p → ∞`.  The large-cutoff witness family
`witnessP` of `RandomizedL30ShortInterval` cannot be substituted here: its
cutoff is `p³ exp (t_p)`, so the global odd count is bounded below by the whole
central witness set while `GlobalOddUpperDensity` asks for `C p² exp (-(1+ε)t)`;
at that cutoff the latter target is far smaller than the former.  The genuine
asymptotic density estimate at the paper cutoff therefore remains the separate
analytic input, exactly as documented in `RandomizedL30SmoothDensity`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count, loss or
error is set to zero.
-/

namespace Cogentic.RandomizedL30CountsNonvacuous

open Filter Real
open scoped Classical
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpointWave14

noncomputable section

/-! ## 1. The explicit count witness at `p = 4` -/

/-- The constant prime scale of the witness. -/
def cnsP : ℕ → ℝ := fun _ => 4

/-- The paper scale `t_p` at the constant scale `p = 4`. -/
def cnsT0 : ℝ := Real.sqrt (Real.log 4 * Real.log (Real.log 4))

/-- The relative error that normalises the paper cutoff to `exp ((1+ε)t) = 768`. -/
def cnsErr : ℕ → ℝ := fun _ => Real.log 768 / cnsT0 - 1

lemma log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num
  nlinarith [Real.log_two_gt_d9]

theorem cnsT0_pos : 0 < cnsT0 := by
  unfold cnsT0
  exact Real.sqrt_pos_of_pos
    (mul_pos (by linarith [log_four_gt_one]) (Real.log_pos log_four_gt_one))

theorem cnsT0_ne_zero : cnsT0 ≠ 0 := cnsT0_pos.ne'

/-- The paper scale at the witness is the constant `cnsT0`. -/
theorem cns_paperT (n : ℕ) : paperT cnsP n = cnsT0 := rfl

/-- The witness normalisation `(1+ε)t = log 768`. -/
theorem cns_one_add_err_mul (n : ℕ) :
    (1 + cnsErr n) * paperT cnsP n = Real.log 768 := by
  rw [cns_paperT]
  unfold cnsErr
  field_simp [cnsT0_ne_zero]
  ring

/-- The paper cutoff at the witness is exactly `768`. -/
theorem cns_cutoff (n : ℕ) : smoothCutoff (paperT cnsP) cnsErr n = 768 := by
  unfold smoothCutoff
  rw [cns_one_add_err_mul, Real.exp_log (by norm_num)]

/-- The exponential factor at the witness is `1/768`. -/
theorem cns_exp_neg (n : ℕ) :
    Real.exp (-(1 + cnsErr n) * paperT cnsP n) = 1 / 768 := by
  rw [show -(1 + cnsErr n) * paperT cnsP n =
      -((1 + cnsErr n) * paperT cnsP n) by ring]
  rw [cns_one_add_err_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]

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

/-- The central order interval at `p = 4` is `(12, 16]`. -/
theorem cns_centralInterval (n : ℕ) :
    centralOrderInterval cnsP n = Finset.Icc 12 16 := by
  simp [centralOrderInterval, cnsP]
  norm_num

/-- Every order in the central interval is smooth at the witness cutoff `768`. -/
theorem cns_centralSmooth (n : ℕ) :
    centralSmoothOrders cnsP (paperT cnsP) cnsErr n = Finset.Icc 12 16 := by
  classical
  rw [centralSmoothOrders, cns_centralInterval]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [cns_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

/-- The central odd smooth orders are exactly `{14}`. -/
theorem cns_centralOdd (n : ℕ) :
    centralOddSmoothOrders cnsP (paperT cnsP) cnsErr n = ({14} : Finset ℕ) := by
  rw [centralOddSmoothOrders, cns_centralSmooth, oddHalf_filter_eq]
  decide

/-- **The central odd count at the witness is the genuine nonzero number `1`.** -/
theorem cns_centralOddCount (n : ℕ) :
    centralOddSmoothCount cnsP (paperT cnsP) cnsErr n = 1 := by
  unfold centralOddSmoothCount
  rw [cns_centralOdd]
  norm_num

/-- The global smooth range up to `p^2 = 16` is the whole interval `[1,16]`. -/
theorem cns_globalSmooth (n : ℕ) :
    globalSmoothOrders cnsP (paperT cnsP) cnsErr n = Finset.Icc 1 16 := by
  classical
  unfold globalSmoothOrders
  rw [show ⌊cnsP n ^ 2⌋₊ = 16 by norm_num [cnsP]]
  rw [Finset.filter_true_of_mem]
  intro m hm
  rw [cns_cutoff]
  apply smooth_of_le
  have hm16 : m ≤ 16 := (Finset.mem_Icc.mp hm).2
  have hm16R : (m : ℝ) ≤ 16 := by exact_mod_cast hm16
  linarith

/-- The global odd-half smooth orders are exactly `{2, 6, 10, 14}`. -/
theorem cns_globalOdd (n : ℕ) :
    globalOddSmoothOrders cnsP (paperT cnsP) cnsErr n =
      ({2, 6, 10, 14} : Finset ℕ) := by
  rw [globalOddSmoothOrders, cns_globalSmooth, oddHalf_filter_eq]
  decide

/-- **The global odd count at the witness is the genuine nonzero number `4`.** -/
theorem cns_globalOddCount (n : ℕ) :
    globalOddSmoothCount cnsP (paperT cnsP) cnsErr n = 4 := by
  unfold globalOddSmoothCount
  rw [cns_globalOdd]
  norm_num

theorem cns_p_ge_two (n : ℕ) : 2 ≤ cnsP n := by norm_num [cnsP]

theorem cns_err_ge_neg_one (n : ℕ) : -1 ≤ cnsErr n := by
  unfold cnsErr
  have h : 0 ≤ Real.log 768 / cnsT0 :=
    div_nonneg (Real.log_nonneg (by norm_num)) cnsT0_pos.le
  linarith

/-! ## 2. The explicit `Wave14L30Counts` inhabitant -/

/-- **The repaired `Wave14L30Counts` is inhabited.**
The short-interval count is the paper-scale count, and all four constants are
genuine nonzero numbers.  The witness has `c = 24`, `B = 48`, `C = 192`, and the
count values are `1` (central) and `4` (global). -/
def witnessL30Counts : Wave14L30Counts where
  p := cnsP
  err := cnsErr
  p_ge_two := cns_p_ge_two
  err_ge_neg_one := cns_err_ge_neg_one
  fibreModels := lppModelMultiples cnsP
  A := 1 / 8
  B := 48
  c := 24
  C := 192
  A_pos := by norm_num
  B_pos := by norm_num
  AB_ge_four := by norm_num
  AC_le := by norm_num
  short_interval := by
    intro n
    rw [cns_centralOddCount, cns_exp_neg]
    norm_num [cnsP]
  global_upper := by
    intro n
    rw [cns_globalOddCount, cns_exp_neg]
    norm_num [cnsP]
  global_binomial := by
    intro n
    have hcut : smoothCutoff (paperT cnsP) cnsErr n = 768 := cns_cutoff n
    refine ⟨?_, {3}, 0, ?_, ?_, ?_⟩
    · rw [hcut]
      norm_num
    · intro q hq
      rw [Finset.mem_singleton] at hq
      subst q
      exact ⟨Nat.prime_three, by norm_num, by rw [hcut]; norm_num⟩
    · rw [hcut]
      norm_num [cnsP]
    · rw [cns_exp_neg]
      norm_num [cnsP]
  lpp_superset := lppModelSuperset_multiples cnsP (paperT cnsP) cnsErr

/-- **Non-vacuity of the repaired counts.** -/
theorem nonempty_wave14L30Counts : Nonempty Wave14L30Counts :=
  ⟨witnessL30Counts⟩

/-- The witness central count is strictly positive. -/
theorem witness_centralCount_pos (n : ℕ) :
    0 < centralOddSmoothCount cnsP (paperT cnsP) cnsErr n := by
  rw [cns_centralOddCount]
  norm_num

/-- The witness global count is strictly positive. -/
theorem witness_globalCount_pos (n : ℕ) :
    0 < globalOddSmoothCount cnsP (paperT cnsP) cnsErr n := by
  rw [cns_globalOddCount]
  norm_num

/-- The short-count lower bound is exactly `1/4` at every scale. -/
theorem witness_shortCount_lower_eq (n : ℕ) :
    (24 : ℝ) * cnsP n ^ ((3 : ℝ) / 2) *
        Real.exp (-(1 + cnsErr n) * paperT cnsP n) = 1 / 4 := by
  rw [cns_exp_neg]
  norm_num [cnsP]

/-- The global upper-density right-hand side is exactly `1/4` at every scale. -/
theorem witness_globalUpper_rhs_eq (n : ℕ) :
    (192 : ℝ) * Real.exp (-(1 + cnsErr n) * paperT cnsP n) = 1 / 4 := by
  rw [cns_exp_neg]
  norm_num

/-- The global upper-density left-hand side is exactly `1/4` at every scale. -/
theorem witness_globalUpper_lhs_eq (n : ℕ) :
    globalOddSmoothCount cnsP (paperT cnsP) cnsErr n / cnsP n ^ 2 = 1 / 4 := by
  rw [cns_globalOddCount]
  norm_num [cnsP]

/-- The binomial-count target is exactly `1` at every scale. -/
theorem witness_binomial_target_eq (n : ℕ) :
    (48 : ℝ) * cnsP n ^ 2 *
        Real.exp (-(1 + cnsErr n) * paperT cnsP n) = 1 := by
  rw [cns_exp_neg]
  norm_num [cnsP]

/-! ## 3. `FailureData` is inhabited

The two `/-- ... -/` guards on `FactorTreeNodes` and `nodes_pos` leave the
zero index outside the tree-size constraint, while `FailureUnionBound` and
`failure_pos` remain unguarded.  The explicit witness below therefore takes
`nodes n = 1` for every `n` and a positive failure probability
`failure n = (1/2)^{Rcurve n} / 2`, which is at most the union-bound
right-hand side `(1/2)^{Rcurve n}` and is strictly positive at every index,
including `n = 0`.

The witness data are

```
k = 1200,   pTrial = 1/2,
Lc n = (n+1)(|scale n| + 1) + |log (2n)| + 2,
Rcurve n = max 1 ⌈exp ((101/100) log 2 · 1200) · Lc n⌉,
nodes n = 1,
failure n = (1/2)^{Rcurve n} / 2 .
```

The old fixed-density obstruction is unaffected and remains isolated in §5. -/

/-- The H.5 Cantor cost data at the unit parameters.  The cost is positive and
the correctness proposition is `True`. -/
def witnessCantor : CantorCostInputs :=
  cantorCostInputsOf (fun _ => 0) (fun _ => 1) (fun _ => 1)
    (fun _ => le_rfl) (fun _ => zero_le_one) (fun _ => le_rfl) True trivial

/-- The constant `k_y = 1200`, the smallest value in the documented range. -/
def fdK : ℕ → ℝ := fun _ => 1200

/-- A confidence parameter that dominates `|scale n|`, `|log (2n)|` and every
fixed multiple of the scale in the limit. -/
def fdLc (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (|scale n| + 1) + |Real.log (2 * (n : ℝ))| + 2

/-- The per-trial success probability `1/2`. -/
def fdP : ℕ → ℝ := fun _ => 1 / 2

/-- The trial cap, rounded up to an integer. -/
def fdRcurve (n : ℕ) : ℕ :=
  max 1 ⌈Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n⌉₊

/-- The compressed-tree node count: one node at every index. -/
def fdNodes : ℕ → ℕ := fun _ => 1

/-- The failure probability, half of the union-bound right-hand side.  It is
strictly positive at every index. -/
def fdFailure (n : ℕ) : ℝ :=
  (1 - fdP n) ^ (fdRcurve n) / 2

theorem fdLc_ge_one (n : ℕ) : 1 ≤ fdLc n := by
  unfold fdLc
  have h1 : (0 : ℝ) ≤ |scale n| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |Real.log (2 * (n : ℝ))| := abs_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
    (by linarith : (0 : ℝ) ≤ |scale n| + 1)]

theorem fdLc_confidence (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      B * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * fdLc n := by
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (B / 64))] with n hn
  have hnR : B ≤ 64 * (n : ℝ) := by
    have hc : B / 64 ≤ (Nat.ceil (B / 64) : ℝ) := Nat.le_ceil _
    have hn' : (Nat.ceil (B / 64) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hcoef : B ≤ 64 * ((n : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hscale_abs : B * scale n ≤ 64 * ((n : ℝ) + 1) * |scale n| := by
    have h1 : B * scale n ≤ B * |scale n| := by
      nlinarith [le_abs_self (scale n), hB.le]
    have h2 : B * |scale n| ≤ (64 * ((n : ℝ) + 1)) * |scale n| :=
      mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    calc
      B * scale n ≤ B * |scale n| := h1
      _ ≤ (64 * ((n : ℝ) + 1)) * |scale n| := h2
      _ = 64 * ((n : ℝ) + 1) * |scale n| := by ring
  have hlog_abs : Real.log (2 * (n : ℝ)) ≤ 64 * |Real.log (2 * (n : ℝ))| := by
    have h1 : Real.log (2 * (n : ℝ)) ≤ |Real.log (2 * (n : ℝ))| := le_abs_self _
    have h2 : (0 : ℝ) ≤ |Real.log (2 * (n : ℝ))| := abs_nonneg _
    nlinarith
  have hEq : 64 * fdLc n =
      64 * ((n : ℝ) + 1) * |scale n| + 64 * ((n : ℝ) + 1) +
        64 * |Real.log (2 * (n : ℝ))| + 128 := by
    unfold fdLc
    ring
  rw [hEq]
  linarith [hscale_abs, hlog_abs]

theorem fd_useful : UsefulPrimeSplitBound fdK fdP := by
  intro n
  unfold fdK fdP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbig : Real.log 2 ≤ ((201 : ℝ) / 200) * (Real.log 2 * 1200) := by
    nlinarith
  have hneg : -(((201 : ℝ) / 200) * (Real.log 2 * 1200)) ≤ -Real.log 2 := by
    nlinarith
  calc
    Real.exp (-(((201 : ℝ) / 200) * (Real.log 2 * 1200)))
        ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hneg
    _ = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]

theorem fd_curve : CurveTrialCap fdK fdLc fdRcurve := by
  intro n
  unfold fdRcurve
  have hx : Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n ≤
      ((⌈Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : ((⌈Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n⌉₊ : ℕ) : ℝ) ≤
      ((max 1 ⌈Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right (1 : ℕ)
      ⌈Real.exp (((101 : ℝ) / 100) * (Real.log 2 * fdK n)) * fdLc n⌉₊
  exact hx.trans hle

theorem fd_nodes_pos (n : ℕ) (_hn : 1 ≤ n) : 0 < fdNodes n := by
  unfold fdNodes
  norm_num

theorem fd_nodes_factor : FactorTreeNodes fdNodes := by
  intro n hn
  unfold fdNodes
  omega

theorem fd_failure_pos (n : ℕ) : 0 < fdFailure n := by
  unfold fdFailure fdP
  positivity

theorem fd_failure_union : FailureUnionBound fdP fdRcurve fdNodes fdFailure := by
  intro n
  unfold fdFailure fdNodes fdP
  norm_num

/-- **The explicit `FailureData` witness.**  All fields are literal:
`k = 1200`, `pTrial = 1/2`,
`Lc n = (n+1)(|scale n|+1) + |log (2n)| + 2`, `Rcurve` is the rounded-up
trial cap, `nodes n = 1`, and `failure n = (1/2)^{Rcurve n} / 2`.  The failure
probability is strictly positive at every index, including `n = 0`. -/
def witnessFailureData : FailureData where
  k := fdK
  k_nonneg := by intro n; norm_num [fdK]
  k_large := by intro n; norm_num [fdK]
  Lc := fdLc
  Lc_ge_one := fdLc_ge_one
  confidence_dominates := fdLc_confidence
  pTrial := fdP
  pTrial_nonneg := by intro n; norm_num [fdP]
  pTrial_le_one := by intro n; norm_num [fdP]
  useful_prime_split := fd_useful
  Rcurve := fdRcurve
  curve_trial_cap := fd_curve
  nodes := fdNodes
  nodes_pos := fd_nodes_pos
  factor_tree_nodes := fd_nodes_factor
  failure := fdFailure
  failure_pos := fd_failure_pos
  failure_union := fd_failure_union

theorem nonempty_failureData : Nonempty FailureData :=
  ⟨witnessFailureData⟩

/-- The witness failure probability is strictly positive at every index. -/
theorem witness_failure_pos (n : ℕ) : 0 < witnessFailureData.failure n :=
  witnessFailureData.failure_pos n

/-- The witness node count is one at every index. -/
theorem witness_nodes_eq_one (n : ℕ) : witnessFailureData.nodes n = 1 := rfl

/-! ## 4. The L30 inputs are inhabited

The explicit counts, the Cantor cost data and the explicit failure data combine
directly. -/

/-- **The explicit `Wave14L30Inputs` witness.** -/
def witnessL30Inputs : Wave14L30Inputs :=
  ⟨witnessL30Counts, witnessCantor, witnessFailureData⟩

theorem nonempty_wave14L30Inputs : Nonempty Wave14L30Inputs :=
  ⟨witnessL30Inputs⟩

/-- The L30 ledger loss of the explicit input is the genuine positive failure
probability, not zero. -/
theorem witnessL30Inputs_loss_pos (n : ℕ) :
    0 < witnessL30Inputs.toSubexpLeaf.loss n := by
  rw [Wave14L30Inputs.loss_eq]
  exact witness_failure_pos n

/-! ## 5. The old fixed-density obstruction, isolated

The following namespace is deliberately independent of the repaired structure.
It records exactly why the fixed-density count cannot coexist with the three
constant relations used by the wave-14 ledger. -/

namespace OldFixedDensityObstruction

/-- The central odd count is at most the cardinality of the central interval. -/
theorem centralOddSmoothCount_le_interval_card
    (p t err : ℕ → ℝ) (n : ℕ) :
    centralOddSmoothCount p t err n ≤ ((centralOrderInterval p n).card : ℝ) := by
  have hsub : centralOddSmoothOrders p t err n ⊆ centralOrderInterval p n := by
    intro m hm
    simp only [centralOddSmoothOrders, centralSmoothOrders, Finset.mem_filter] at hm
    exact hm.1.1
  unfold centralOddSmoothCount
  exact_mod_cast Finset.card_le_card hsub

/-- **The exact obstruction of the old fixed-density form.**  A fixed-density
short-interval count, `4 ≤ A B`, `A C ≤ c` and `B ≤ C` are inconsistent. -/
theorem fixedDensity_obstruction
    {A B c C : ℝ} {p t err : ℕ → ℝ}
    (hp : ∀ n, 2 ≤ p n) (hA : 0 < A)
    (hAB : 4 ≤ A * B) (hAC : A * C ≤ c) (hBC : B ≤ C)
    (hshort : YounisOddShortIntervalCount c p t err) : False := by
  have hc_le_one : c ≤ 1 := by
    have hshort0 := hshort 0
    have hcard := centralOrderInterval_card_le_three_halves (p := p) (n := 0) (hp 0)
    have hmono := centralOddSmoothCount_le_interval_card p t err 0
    have hp_pos : (0 : ℝ) < p 0 ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by linarith [hp 0]) _
    have hle : c * p 0 ^ ((3 : ℝ) / 2) ≤ p 0 ^ ((3 : ℝ) / 2) :=
      hshort0.trans (hmono.trans hcard)
    exact (mul_le_mul_iff_of_pos_right hp_pos).mp (by simpa using hle)
  have hc_ge_four : 4 ≤ c := by
    have hABC : A * B ≤ A * C := mul_le_mul_of_nonneg_left hBC hA.le
    linarith
  linarith

/-- The old `Wave14L30Counts` field set, with the fixed-density short count. -/
structure OldWave14L30Counts where
  p : ℕ → ℝ
  err : ℕ → ℝ
  p_ge_two : ∀ n, 2 ≤ p n
  err_ge_neg_one : ∀ n, -1 ≤ err n
  fibreModels : ℕ → ℕ → Finset ℕ
  A : ℝ
  B : ℝ
  c : ℝ
  C : ℝ
  A_pos : 0 < A
  B_pos : 0 < B
  AB_ge_four : 4 ≤ A * B
  AC_le : A * C ≤ c
  short_interval : YounisOddShortIntervalCount c p (paperT p) err
  global_upper : GlobalOddUpperDensity C p (paperT p) err
  global_binomial : GlobalOddBinomialCount B p (paperT p) err
  lpp_superset : LPPModelSuperset p (paperT p) err fibreModels

/-- **The old fixed-density count bundle has no inhabitant.** -/
theorem oldWave14L30Counts_false (S : OldWave14L30Counts) : False := by
  have hBC : S.B ≤ S.C :=
    globalOddLower_le_upper S.p_ge_two
      (younisOddGlobalLower_of_binomialCount S.global_binomial) S.global_upper
  exact fixedDensity_obstruction S.p_ge_two S.A_pos S.AB_ge_four S.AC_le hBC
    S.short_interval

theorem not_nonempty_oldWave14L30Counts : ¬ Nonempty OldWave14L30Counts :=
  fun ⟨S⟩ => oldWave14L30Counts_false S

end OldFixedDensityObstruction

/-! ## Axiom audit -/

#print axioms cns_centralOddCount
#print axioms cns_globalOddCount
#print axioms witnessL30Counts
#print axioms nonempty_wave14L30Counts
#print axioms witness_shortCount_lower_eq
#print axioms witness_globalUpper_lhs_eq
#print axioms witness_binomial_target_eq
#print axioms witnessCantor
#print axioms witnessFailureData
#print axioms nonempty_failureData
#print axioms witness_failure_pos
#print axioms witnessL30Inputs
#print axioms nonempty_wave14L30Inputs
#print axioms witnessL30Inputs_loss_pos
#print axioms OldFixedDensityObstruction.fixedDensity_obstruction
#print axioms OldFixedDensityObstruction.oldWave14L30Counts_false

end

end Cogentic.RandomizedL30CountsNonvacuous
