import Cogentic.RandomizedL30ShortInterval

set_option maxHeartbeats 4000000

/-!
# L30: the paper-regime smooth-number density bound

`Cogentic/RandomizedL30ShortInterval.lean` reduced the paper-regime central odd
count to the explicit prime-bin count of `centeredBinProducts`.  This file
supplies the smooth-number density half of that count at the paper parameters.

The paper scale is

`t_n = sqrt (log p_n * log log p_n)`,    `Y_n = exp ((1 + ε) t_n)`,

so that the logarithmic ratio is

`u_n = log (p_n^2) / log Y_n = 2 log p_n / ((1 + ε) t_n)`.

At this scale `u_n * log u_n = t_n * (1 - o(1))`, and the prime-bin strip
construction of `Cogentic.RandomizedSmoothDensity` gives a positive lower bound
of the shape

`(1/8) * p_n^2 * exp (-(1+ε) t_n)`

on the number of `Y_n`-smooth odd orders.  The construction is the concrete
balanced strip `centeredBinProducts P δ J m a` with

* `m = ⌈u (1 + 1/log u)⌉`,
* `J` chosen large enough that `m δ ≤ log 2` while `δ J = (1/2) (1+ε) t / log u`,
* `P = (p^2/4)^(1/m)`.

The upper strip endpoint is at most `p^2/2`, so doubling every odd product
gives an odd-half order `2x ≡ 2 (mod 4)` below `p^2`; hence the prime-bin count
transfers to `globalOddSmoothCount`.

Because the `centeredBinProducts` density theorem is asymptotic in `u`, the
statements below are eventual, with the threshold hidden in a filter.  No
count, mass, or error is set to zero.
-/

namespace Cogentic.RandomizedL30SmoothDensity

open Filter Real
open Asymptotics
open scoped Classical
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL30Relative
open Cogentic.RandomizedL30Interval
open Cogentic.Randomized
open Cogentic.RandomizedL30ShortInterval

noncomputable section

/-! ## 1. The paper schedule -/

/-- The paper error sequence at a fixed positive error `ε`. -/
def paperError (ε : ℝ) : ℕ → ℝ := fun _ => ε

/-- The paper logarithmic ratio `u = log (p^2) / log Y` for the cutoff
`Y = exp ((1 + ε) t)`. -/
def paperDensityU (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  2 * Real.log (p n) / ((1 + ε) * paperT p n)

/-- The number of prime bins `m = ⌈u (1 + 1/log u)⌉`. -/
def paperDensityM (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n))⌉₊

/-- The number of bins `J`, large enough that `m δ ≤ log 2` while keeping
`δ J = (1/2) (1+ε) t / log u`. -/
def paperDensityJ (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℕ :=
  max (paperDensityM p ε n + 1)
    ⌈(1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ)) /
        (Real.log (paperDensityU p ε n) * Real.log 2)⌉₊

/-- The bin width `δ`. -/
def paperDensityDelta (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (1 / 2) * ((1 + ε) * paperT p n) /
    ((paperDensityJ p ε n : ℝ) * Real.log (paperDensityU p ε n))

/-- The geometric bin centre `P = (p^2 / 4)^(1/m)`. -/
def paperDensityP (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (p n ^ 2 / 4) ^ (1 / (paperDensityM p ε n : ℝ))

/-- The paper cutoff `Y = exp ((1 + ε) t)`. -/
def paperDensityY (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((1 + ε) * paperT p n)

/-- The cutoff is exactly `smoothCutoff` at the paper scale. -/
theorem paperDensityY_eq_smoothCutoff (p : ℕ → ℝ) (ε : ℝ) :
    paperDensityY p ε = smoothCutoff (paperT p) (paperError ε) := by
  funext n
  rfl

/-! ## 2. Growth hypotheses -/

/-- The elementary growth needed for the paper schedule: `p` is eventually at
least `16` and `log p` tends to infinity. -/
def PaperDensityGrowth (p : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 16 ≤ p n) ∧
    Tendsto (fun n => Real.log (p n)) atTop atTop

theorem PaperDensityGrowth.eventually_sixteen {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) : ∀ᶠ n in atTop, 16 ≤ p n := h.1

theorem PaperDensityGrowth.tendsto_log {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    Tendsto (fun n => Real.log (p n)) atTop atTop := h.2

/-- The witness scale `p_n = 4^{n+4}` satisfies the growth hypothesis. -/
theorem witnessP_paperDensityGrowth : PaperDensityGrowth witnessP := by
  constructor
  · exact Filter.Eventually.of_forall fun n => by linarith [witnessP_ge_256 n]
  · have h : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hmul : Tendsto (fun n : ℕ => ((n : ℝ) + 4) * Real.log 4) atTop atTop :=
      h.atTop_mul_const (Real.log_pos (by norm_num))
    refine hmul.congr fun n => ?_
    unfold witnessP
    rw [Real.log_pow]
    push_cast
    ring

/-! ## 3. Elementary eventual positivity -/

theorem eventually_log_pos_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p) :
    ∀ᶠ n in atTop, 0 < Real.log (p n) := by
  filter_upwards [h.eventually_sixteen] with n hn
  have h16 : (1 : ℝ) < p n := by linarith
  exact Real.log_pos h16

theorem eventually_log_log_pos_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p) :
    ∀ᶠ n in atTop, 0 < Real.log (Real.log (p n)) := by
  filter_upwards [h.eventually_sixteen] with n hn
  have h16 : (1 : ℝ) < p n := by linarith
  have hL1 : (1 : ℝ) < Real.log (p n) := by
    have hlog16 : (1 : ℝ) < Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    have hle : Real.log 16 ≤ Real.log (p n) :=
      Real.log_le_log (by norm_num) hn
    linarith
  exact Real.log_pos hL1

theorem eventually_paperT_pos_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p) :
    ∀ᶠ n in atTop, 0 < paperT p n := by
  filter_upwards [eventually_log_pos_of_growth h,
    eventually_log_log_pos_of_growth h] with n hL hl
  unfold paperT
  exact Real.sqrt_pos_of_pos (mul_pos hL hl)

theorem eventually_paperDensityU_pos {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop, 0 < paperDensityU p ε n := by
  filter_upwards [eventually_log_pos_of_growth h,
    eventually_paperT_pos_of_growth h] with n hL ht
  unfold paperDensityU
  positivity

theorem eventually_paperDensityU_gt_one_of_tendsto {p : ℕ → ℝ} {ε : ℝ}
    (hu : Tendsto (fun n => paperDensityU p ε n) atTop atTop) :
    ∀ᶠ n in atTop, 1 < paperDensityU p ε n :=
  hu.eventually_gt_atTop 1

/-! ## 4. Basic algebra of the schedule -/

theorem paperDensityU_le_paperDensityM (p : ℕ → ℝ) (ε : ℝ) (n : ℕ)
    (hu : 0 < paperDensityU p ε n)
    (hlogu : 0 < Real.log (paperDensityU p ε n)) :
    paperDensityU p ε n ≤ (paperDensityM p ε n : ℝ) := by
  have hle : paperDensityU p ε n ≤
      paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n)) := by
    have hpos : 0 ≤ 1 / Real.log (paperDensityU p ε n) := by positivity
    nlinarith [hu]
  exact hle.trans (by
    simpa only [paperDensityM] using
      (Nat.le_ceil (paperDensityU p ε n *
        (1 + 1 / Real.log (paperDensityU p ε n)))))

theorem paperDensityM_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hu1 : 1 < paperDensityU p ε n) :
    0 < paperDensityM p ε n := by
  have hu : 0 < paperDensityU p ε n := zero_lt_one.trans hu1
  have hlogu : 0 < Real.log (paperDensityU p ε n) := Real.log_pos hu1
  have h : (1 : ℝ) < (paperDensityM p ε n : ℝ) :=
    hu1.trans_le (paperDensityU_le_paperDensityM p ε n hu hlogu)
  have h0 : (0 : ℝ) < (paperDensityM p ε n : ℝ) := lt_trans zero_lt_one h
  exact_mod_cast h0

theorem paperDensityM_le_two_u {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hu : 1 < paperDensityU p ε n)
    (hlogu : 2 ≤ Real.log (paperDensityU p ε n)) :
    (paperDensityM p ε n : ℝ) ≤ 2 * paperDensityU p ε n := by
  set u := paperDensityU p ε n
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hlogpos : 0 < Real.log u := lt_of_lt_of_le (by norm_num) hlogu
  have hone : 1 ≤ u / Real.log u := by
    rw [one_le_div hlogpos]
    linarith [Real.log_le_sub_one_of_pos hu0]
  have hceil : (paperDensityM p ε n : ℝ) < u * (1 + 1 / Real.log u) + 1 := by
    simpa only [paperDensityM, u] using
      (Nat.ceil_lt_add_one (show 0 ≤ u * (1 + 1 / Real.log u) by positivity))
  have hstep : u * (1 + 1 / Real.log u) + 1 ≤ 2 * u := by
    have hratio_le : u / Real.log u ≤ u / 2 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [hu0, hlogu]
    have hdiff : 2 * u - (u * (1 + 1 / Real.log u) + 1) =
        u - u / Real.log u - 1 := by ring
    have hu2 : (2 : ℝ) ≤ u := by linarith [hu]
    linarith [hratio_le, hu2, hdiff]
  exact le_of_lt (hceil.trans_le hstep)

theorem paperDensityM_le_sharp {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hu : 1 < paperDensityU p ε n)
    (hlogu : 2 ≤ Real.log (paperDensityU p ε n)) :
    (paperDensityM p ε n : ℝ) ≤
      paperDensityU p ε n * (1 + 2 / Real.log (paperDensityU p ε n)) := by
  set u := paperDensityU p ε n
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hlogpos : 0 < Real.log u := lt_of_lt_of_le (by norm_num) hlogu
  have hone : 1 ≤ u / Real.log u := by
    rw [one_le_div hlogpos]
    linarith [Real.log_le_sub_one_of_pos hu0]
  have hceil : (paperDensityM p ε n : ℝ) < u * (1 + 1 / Real.log u) + 1 := by
    simpa only [paperDensityM, u] using
      (Nat.ceil_lt_add_one (show 0 ≤ u * (1 + 1 / Real.log u) by positivity))
  have hstep : u * (1 + 1 / Real.log u) + 1 ≤ u * (1 + 2 / Real.log u) := by
    have hd : 0 ≤ u / Real.log u - 1 := sub_nonneg.mpr hone
    have hdiff : u * (1 + 2 / Real.log u) - (u * (1 + 1 / Real.log u) + 1) =
        u / Real.log u - 1 := by ring
    linarith [hd, hdiff]
  exact le_of_lt (hceil.trans_le hstep)

theorem paperDensityJ_ge_m (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    paperDensityM p ε n + 1 ≤ paperDensityJ p ε n :=
  le_max_left _ _

theorem paperDensityJ_ge_ratio (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    (1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ)) /
        (Real.log (paperDensityU p ε n) * Real.log 2) ≤
      (paperDensityJ p ε n : ℝ) := by
  let ratio := (1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ)) /
    (Real.log (paperDensityU p ε n) * Real.log 2)
  have h : ⌈ratio⌉₊ ≤ paperDensityJ p ε n := by
    unfold paperDensityJ
    exact le_max_right _ _
  exact (Nat.le_ceil ratio).trans (Nat.cast_le.mpr h)

theorem paperDensityJ_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hm : 0 < paperDensityM p ε n) : 0 < paperDensityJ p ε n :=
  lt_of_lt_of_le (Nat.succ_pos _) (paperDensityJ_ge_m p ε n)

theorem paperDensityDelta_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (ht : 0 < paperT p n)
    (hJ : 0 < paperDensityJ p ε n)
    (hlogu : 0 < Real.log (paperDensityU p ε n)) :
    0 < paperDensityDelta p ε n := by
  unfold paperDensityDelta
  positivity

theorem paperDensityDelta_mul_J {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hJ : 0 < paperDensityJ p ε n)
    (hlogu : Real.log (paperDensityU p ε n) ≠ 0) :
    paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) =
      (1 / 2) * ((1 + ε) * paperT p n) / Real.log (paperDensityU p ε n) := by
  have hJne : (paperDensityJ p ε n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hJ)
  unfold paperDensityDelta
  field_simp

theorem paperDensityDelta_mul_m_le_log2 {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (ht : 0 < paperT p n)
    (hJ : 0 < paperDensityJ p ε n)
    (hlogu : 0 < Real.log (paperDensityU p ε n)) :
    (paperDensityM p ε n : ℝ) * paperDensityDelta p ε n ≤ Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio := paperDensityJ_ge_ratio p ε n
  have hden : 0 < Real.log (paperDensityU p ε n) * Real.log 2 :=
    mul_pos hlogu hlog2
  have hmul : (1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ)) ≤
      (paperDensityJ p ε n : ℝ) *
        (Real.log (paperDensityU p ε n) * Real.log 2) := by
    rw [div_le_iff₀ hden] at hratio
    exact hratio
  have hJne : (0 : ℝ) < (paperDensityJ p ε n : ℝ) := by exact_mod_cast hJ
  have hdelta : (paperDensityM p ε n : ℝ) * paperDensityDelta p ε n =
      ((1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ))) /
        ((paperDensityJ p ε n : ℝ) * Real.log (paperDensityU p ε n)) := by
    unfold paperDensityDelta
    field_simp
  rw [hdelta, div_le_iff₀ (mul_pos hJne hlogu)]
  nlinarith [hmul]

theorem paperDensityP_pos {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) : 0 < paperDensityP p ε n := by
  unfold paperDensityP
  exact Real.rpow_pos_of_pos (by positivity) _

theorem paperDensityP_pow {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < paperDensityM p ε n) :
    paperDensityP p ε n ^ paperDensityM p ε n = p n ^ 2 / 4 := by
  have hx : (0 : ℝ) ≤ p n ^ 2 / 4 := by positivity
  have hmne : ((paperDensityM p ε n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold paperDensityP
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  have : (1 / (paperDensityM p ε n : ℝ)) * (paperDensityM p ε n : ℝ) = 1 := by
    field_simp
  rw [this, Real.rpow_one]

theorem paperDensity_logP {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < paperDensityM p ε n) :
    Real.log (paperDensityP p ε n) =
      (2 * Real.log (p n) - Real.log 4) / (paperDensityM p ε n : ℝ) := by
  have hbase : 0 < p n ^ 2 / 4 := by positivity
  have hlogbase : Real.log (p n ^ 2 / 4) = 2 * Real.log (p n) - Real.log 4 := by
    rw [Real.log_div (pow_ne_zero 2 (ne_of_gt hp)) (by norm_num), Real.log_pow]
    push_cast
    ring
  unfold paperDensityP
  rw [Real.log_rpow hbase, hlogbase]
  ring

theorem paperDensity_strip_upper {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hm : 0 < paperDensityM p ε n)
    (hmδ : (paperDensityM p ε n : ℝ) * paperDensityDelta p ε n ≤
      Real.log 2) :
    paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) ≤
      p n ^ 2 / 2 := by
  rw [paperDensityP_pow hp hm]
  have hexp : Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) ≤ 2 := by
    calc
      Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr hmδ
      _ = 2 := Real.exp_log (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ p n ^ 2 / 4)]

theorem paperDensity_logP_ge_half {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 1 < p n) (hm : 0 < paperDensityM p ε n)
    (hu : 0 < paperDensityU p ε n)
    (hlogu : 0 < Real.log (paperDensityU p ε n))
    (hkm : (paperDensityM p ε n : ℝ) ≤ 2 * paperDensityU p ε n)
    (ht : 0 < paperT p n) (hε : 0 < ε) :
    (1 / 2) * ((1 + ε) * paperT p n) - Real.log 4 ≤
      Real.log (paperDensityP p ε n) := by
  have hp0 : 0 < p n := zero_lt_one.trans hp
  have hL : 0 < Real.log (p n) := Real.log_pos hp
  have hα : 0 < 1 + ε := by positivity
  have hden : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hm
  rw [paperDensity_logP hp0 hm]
  have htwoL : 2 * Real.log (p n) =
      (1 + ε) * paperT p n * paperDensityU p ε n := by
    unfold paperDensityU
    field_simp
  have hdiv : (1 + ε) * paperT p n / 2 ≤
      2 * Real.log (p n) / (paperDensityM p ε n : ℝ) := by
    rw [htwoL]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden]
    have hu : 0 < paperDensityU p ε n := by
      unfold paperDensityU
      positivity
    nlinarith [hkm, mul_nonneg (show 0 ≤ (1 + ε) * paperT p n by positivity) hu.le]
  have hlog4 : Real.log 4 / (paperDensityM p ε n : ℝ) ≤ Real.log 4 := by
    have h1 : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) := by exact_mod_cast hm
    have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact div_le_self hlog4pos h1
  calc
    (1 / 2) * ((1 + ε) * paperT p n) - Real.log 4 ≤
        2 * Real.log (p n) / (paperDensityM p ε n : ℝ) -
          Real.log 4 / (paperDensityM p ε n : ℝ) := by
      linarith [hdiv, hlog4]
    _ = (2 * Real.log (p n) - Real.log 4) /
          (paperDensityM p ε n : ℝ) := by rw [sub_div]

theorem paperDensity_bin_lower {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 0 < p n) (hp1 : 1 < p n) (hm : 0 < paperDensityM p ε n)
    (hkm : (paperDensityM p ε n : ℝ) ≤ 2 * paperDensityU p ε n)
    (hlogu : 2 ≤ Real.log (paperDensityU p ε n))
    (ht : 0 < paperT p n) (hε : 0 < ε)
    (hJ : 0 < paperDensityJ p ε n)
    (hlarge : Real.log 3 + Real.log 4 ≤
      (1 / 2) * ((1 + ε) * paperT p n) * (1 - 1 / Real.log (paperDensityU p ε n))) :
    3 ≤ paperDensityP p ε n *
      Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
  have hlogP := paperDensity_logP_ge_half hp1 hm
    (by
      unfold paperDensityU
      exact div_pos (mul_pos (by norm_num) (Real.log_pos hp1)) (by positivity))
    (lt_of_lt_of_le (by norm_num) hlogu) hkm ht hε
  have hlogu_pos : 0 < Real.log (paperDensityU p ε n) := lt_of_lt_of_le (by norm_num) hlogu
  have hdeltaJ := paperDensityDelta_mul_J hJ hlogu_pos.ne'
  have hexp_eq : paperDensityP p ε n *
      Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) =
        Real.exp (Real.log (paperDensityP p ε n) -
          paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
    have hPpos : 0 < paperDensityP p ε n := paperDensityP_pos hp
    calc
      paperDensityP p ε n *
          Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) =
          Real.exp (Real.log (paperDensityP p ε n)) *
            Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
              rw [Real.exp_log hPpos]
      _ = Real.exp (Real.log (paperDensityP p ε n) -
            paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
  rw [hexp_eq]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  have hlarge' : Real.log 3 + Real.log 4 ≤
      (1 / 2) * ((1 + ε) * paperT p n) -
        (1 / 2) * ((1 + ε) * paperT p n) /
          Real.log (paperDensityU p ε n) := by
    have hrew : (1 / 2) * ((1 + ε) * paperT p n) *
        (1 - 1 / Real.log (paperDensityU p ε n)) =
        (1 / 2) * ((1 + ε) * paperT p n) -
          (1 / 2) * ((1 + ε) * paperT p n) /
            Real.log (paperDensityU p ε n) := by ring
    rw [hrew] at hlarge
    exact hlarge
  rw [hdeltaJ]
  linarith [hlogP, hdeltaJ, hlarge']

theorem paperDensity_bin_upper {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 1 < p n) (hm : 0 < paperDensityM p ε n)
    (hkm : paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n)) ≤
      (paperDensityM p ε n : ℝ))
    (hlogu : 1 ≤ Real.log (paperDensityU p ε n))
    (ht : 0 < paperT p n) (hε : 0 < ε)
    (hJ : 0 < paperDensityJ p ε n) :
    paperDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
      paperDensityY p ε n := by
  have hp0 : 0 < p n := zero_lt_one.trans hp
  have hlogu_pos : 0 < Real.log (paperDensityU p ε n) := lt_of_lt_of_le (by norm_num) hlogu
  have hu_pos : 0 < paperDensityU p ε n := by
    unfold paperDensityU
    exact div_pos (mul_pos (by norm_num) (Real.log_pos hp)) (by positivity)
  have hu1 : 1 < paperDensityU p ε n := by
    by_contra h
    have hle : paperDensityU p ε n ≤ 1 := le_of_not_gt h
    have : Real.log (paperDensityU p ε n) ≤ 0 := Real.log_nonpos hu_pos.le hle
    linarith
  have hu : 0 < paperDensityU p ε n := hu_pos
  have hα : 0 < 1 + ε := by positivity
  have hL : 0 < Real.log (p n) := Real.log_pos hp
  have hden : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hm
  have hdeltaJ := paperDensityDelta_mul_J hJ hlogu_pos.ne'
  -- `u/m ≤ 1 - 1/(2 log u)`
  have hum : paperDensityU p ε n / (paperDensityM p ε n : ℝ) ≤
      1 - 1 / (2 * Real.log (paperDensityU p ε n)) := by
    have hbase : paperDensityU p ε n / (paperDensityM p ε n : ℝ) ≤
        1 / (1 + 1 / Real.log (paperDensityU p ε n)) := by
      rw [div_le_div_iff₀ hden
        (by positivity : 0 < 1 + 1 / Real.log (paperDensityU p ε n))]
      nlinarith [hkm]
    have hfrac : 1 / (1 + 1 / Real.log (paperDensityU p ε n)) ≤
        1 - 1 / (2 * Real.log (paperDensityU p ε n)) := by
      have hx : 1 ≤ Real.log (paperDensityU p ε n) := hlogu
      rw [div_le_iff₀ (by positivity : 0 < 1 + 1 / Real.log (paperDensityU p ε n))]
      have hx0 : 0 < Real.log (paperDensityU p ε n) := hlogu_pos
      field_simp
      nlinarith
    exact hbase.trans hfrac
  have htwoL : 2 * Real.log (p n) =
      (1 + ε) * paperT p n * paperDensityU p ε n := by
    unfold paperDensityU
    field_simp
  have hmain : Real.log (paperDensityP p ε n) ≤
      (1 + ε) * paperT p n - (1 + ε) * paperT p n /
        (2 * Real.log (paperDensityU p ε n)) - Real.log 4 / (paperDensityM p ε n : ℝ) := by
    rw [paperDensity_logP hp0 hm, htwoL, sub_div]
    have hrewrite : (1 + ε) * paperT p n * paperDensityU p ε n /
        (paperDensityM p ε n : ℝ) =
          (1 + ε) * paperT p n * (paperDensityU p ε n / (paperDensityM p ε n : ℝ)) := by
      ring
    rw [hrewrite]
    have h := mul_le_mul_of_nonneg_left hum (by positivity : 0 ≤ (1 + ε) * paperT p n)
    have h' : (1 + ε) * paperT p n * (1 - 1 / (2 * Real.log (paperDensityU p ε n))) =
        (1 + ε) * paperT p n - (1 + ε) * paperT p n /
          (2 * Real.log (paperDensityU p ε n)) := by ring
    rw [h'] at h
    linarith [h]
  have hsum : Real.log (paperDensityP p ε n) +
      paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) ≤
        (1 + ε) * paperT p n := by
    rw [hdeltaJ]
    have hrewrite : (1 / 2) * ((1 + ε) * paperT p n) / Real.log (paperDensityU p ε n) =
        (1 + ε) * paperT p n / (2 * Real.log (paperDensityU p ε n)) := by
      ring
    rw [hrewrite]
    have hY : 0 ≤ Real.log 4 / (paperDensityM p ε n : ℝ) := by positivity
    linarith [hmain, hY]
  have hPpos : 0 < paperDensityP p ε n := paperDensityP_pos hp0
  calc
    paperDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))
        = Real.exp (Real.log (paperDensityP p ε n) +
            paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
          rw [Real.exp_add, Real.exp_log hPpos]
    _ ≤ Real.exp ((1 + ε) * paperT p n) := Real.exp_le_exp.mpr hsum
    _ = paperDensityY p ε n := rfl

/-! ## 5. Asymptotics of the paper scale -/

private theorem one_lt_log_sixteen : (1 : ℝ) < Real.log 16 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num
  nlinarith [Real.log_two_gt_d9]

theorem one_lt_log_of_sixteen {p : ℕ → ℝ} {n : ℕ} (hp : 16 ≤ p n) :
    (1 : ℝ) < Real.log (p n) :=
  one_lt_log_sixteen.trans_le (Real.log_le_log (by norm_num) hp)

theorem one_lt_logLog_of_sixteen {p : ℕ → ℝ} {n : ℕ} (hp : 16 ≤ p n) :
    (1 : ℝ) < Real.log (Real.log (p n)) := by
  have hlog16 : Real.exp 1 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hloglog16 : (1 : ℝ) < Real.log (Real.log 16) := by
    have h := Real.log_lt_log (Real.exp_pos 1) hlog16
    rwa [Real.log_exp] at h
  have hL16 : Real.log 16 ≤ Real.log (p n) := Real.log_le_log (by norm_num) hp
  have hlog16pos : 0 < Real.log 16 := Real.log_pos (by norm_num : (1 : ℝ) < 16)
  exact hloglog16.trans_le (Real.log_le_log hlog16pos hL16)

/-- The elementary identity `a / sqrt (a b) = sqrt (a / b)`. -/
theorem div_sqrt_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (a * b) = Real.sqrt (a / b) := by
  have hnonneg : 0 ≤ a / Real.sqrt (a * b) :=
    div_nonneg ha.le (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hnonneg]
  congr 1
  rw [div_pow, Real.sq_sqrt (mul_nonneg ha.le hb.le)]
  field_simp

/-- `(log p / t) * log log p = t` at the paper scale. -/
theorem log_div_paperT_mul {p : ℕ → ℝ} {n : ℕ} (hp : 16 ≤ p n) :
    (Real.log (p n) / paperT p n) * Real.log (Real.log (p n)) = paperT p n := by
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hp)
  have ht2 : paperT p n ^ 2 =
      Real.log (p n) * Real.log (Real.log (p n)) := by
    unfold paperT
    exact Real.sq_sqrt (mul_nonneg hL.le hM.le)
  have htpos : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos (mul_pos hL hM)
  have htne : paperT p n ≠ 0 := htpos.ne'
  field_simp [htne]
  nlinarith [ht2]

theorem tendsto_paperT_of_growth {p : ℕ → ℝ} (h : PaperDensityGrowth p) :
    Tendsto (fun n => paperT p n) atTop atTop := by
  have hlogL : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  have hprod : Tendsto
      (fun n => Real.log (p n) * Real.log (Real.log (p n))) atTop atTop :=
    h.tendsto_log.atTop_mul_atTop₀ hlogL
  have hsqrt := Real.tendsto_sqrt_atTop.comp hprod
  refine hsqrt.congr fun n => ?_
  rfl

private theorem tendsto_log_div_id_atTop_zero :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  simpa only [Real.rpow_one] using
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero

theorem tendsto_log_div_paperT_of_growth {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    Tendsto (fun n => Real.log (p n) / paperT p n) atTop atTop := by
  have hratio0 := tendsto_log_div_id_atTop_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with x hlx hx
    exact div_pos hlx hx
  have hinv : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop :=
    Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratio0 hpos)
  have hcomp := hinv.comp h.tendsto_log
  have hdivlog : Tendsto
      (fun n => Real.log (p n) / Real.log (Real.log (p n))) atTop atTop := by
    refine hcomp.congr fun n => ?_
    simp only [Function.comp_def, inv_div]
  have hsqrt := Real.tendsto_sqrt_atTop.comp hdivlog
  refine hsqrt.congr' ?_
  filter_upwards [h.eventually_sixteen] with n hn
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hn)
  unfold paperT
  exact (div_sqrt_mul hL hM).symm

theorem tendsto_paperDensityU_of_growth {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    Tendsto (fun n => paperDensityU p ε n) atTop atTop := by
  have hbase := tendsto_log_div_paperT_of_growth h
  have hconst : 0 < 2 / (1 + ε) := by positivity
  have hmain := Filter.Tendsto.const_mul_atTop hconst hbase
  refine hmain.congr fun n => ?_
  unfold paperDensityU
  field_simp

/-- The exact asymptotic identity for the paper exponent:
`(1+ε) u log u = t - (log p / t) (log log log p + 2 log (1+ε) - 2 log 2)`. -/
theorem paperDensityU_mul_log_eq {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 16 ≤ p n) (hε : 0 < ε) :
    (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) =
      paperT p n - (Real.log (p n) / paperT p n) *
        (Real.log (Real.log (Real.log (p n))) +
          2 * Real.log (1 + ε) - 2 * Real.log 2) := by
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hp)
  have htpos : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos (mul_pos hL hM)
  have ht2 : paperT p n ^ 2 =
      Real.log (p n) * Real.log (Real.log (p n)) := by
    unfold paperT
    exact Real.sq_sqrt (mul_nonneg hL.le hM.le)
  have hα : 0 < 1 + ε := by positivity
  have hlogt : Real.log (paperT p n) =
      (Real.log (Real.log (p n)) +
        Real.log (Real.log (Real.log (p n)))) / 2 := by
    rw [paperT, Real.log_sqrt (mul_nonneg hL.le hM.le),
      Real.log_mul hL.ne' hM.ne']
  have hlogu : Real.log (paperDensityU p ε n) =
      Real.log 2 - Real.log (1 + ε) +
        (Real.log (Real.log (p n)) -
          Real.log (Real.log (Real.log (p n)))) / 2 := by
    unfold paperDensityU
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_mul (by norm_num) hL.ne']
    rw [Real.log_mul hα.ne' htpos.ne']
    rw [hlogt]
    ring
  calc
    (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n))
        = (2 * Real.log (p n) / paperT p n) *
            Real.log (paperDensityU p ε n) := by
          unfold paperDensityU
          field_simp [htpos.ne', hα.ne']
    _ = (2 * Real.log (p n) / paperT p n) *
          (Real.log 2 - Real.log (1 + ε) +
            (Real.log (Real.log (p n)) -
              Real.log (Real.log (Real.log (p n)))) / 2) := by
          rw [hlogu]
    _ = paperT p n - (Real.log (p n) / paperT p n) *
          (Real.log (Real.log (Real.log (p n))) +
            2 * Real.log (1 + ε) - 2 * Real.log 2) := by
          have htne : paperT p n ≠ 0 := htpos.ne'
          field_simp [htne]
          nlinarith [ht2]

private theorem tendsto_logLogLog_of_growth {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    Tendsto (fun n => Real.log (Real.log (Real.log (p n)))) atTop atTop := by
  have h1 : Tendsto (fun n => Real.log (p n)) atTop atTop := h.tendsto_log
  have h2 : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun n => Real.log (Real.log (Real.log (p n)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h2
  exact h3

theorem eventually_K_nonneg {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      0 ≤ Real.log (Real.log (Real.log (p n))) +
        2 * Real.log (1 + ε) - 2 * Real.log 2 := by
  have hLLL := tendsto_logLogLog_of_growth h
  filter_upwards [hLLL.eventually_ge_atTop
    (2 * Real.log 2 - 2 * Real.log (1 + ε))] with n hn
  linarith

/-- The positive exponent bound `(1+ε) u log u ≤ t` at the paper scale. -/
theorem eventually_paperDensityU_mul_log_le_paperT {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) ≤
        paperT p n := by
  filter_upwards [h.eventually_sixteen, eventually_K_nonneg h hε] with n hp hK
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hid := paperDensityU_mul_log_eq hp hε
  rw [hid]
  have hcoef : 0 ≤ Real.log (p n) / paperT p n :=
    div_nonneg hL.le (Real.sqrt_nonneg _)
  have hprod : 0 ≤ (Real.log (p n) / paperT p n) *
      (Real.log (Real.log (Real.log (p n))) +
        2 * Real.log (1 + ε) - 2 * Real.log 2) :=
    mul_nonneg hcoef hK
  linarith

/-- The matching lower exponent bound `t ≤ 2 (1+ε) u log u`. -/
theorem eventually_paperT_le_two_mul_paperDensityU_log {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      paperT p n ≤ 2 * (1 + ε) *
        (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
  have hM : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  have hratio : Tendsto
      (fun n => Real.log (Real.log (Real.log (p n))) /
        Real.log (Real.log (p n))) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM
  let c : ℝ := 2 * Real.log (1 + ε) - 2 * Real.log 2
  filter_upwards [h.eventually_sixteen,
    hM.eventually_ge_atTop (max 8 (8 * |c|)),
    hM.eventually_gt_atTop 0,
    (tendsto_order.mp hratio).2 (1 / 4) (by norm_num)] with n hp hMbig hMpos hsmall
  have hMge : (8 : ℝ) ≤ Real.log (Real.log (p n)) :=
    (le_max_left _ _).trans hMbig
  have hcab : |c| ≤ Real.log (Real.log (p n)) / 8 := by
    have h8 : 8 * |c| ≤ Real.log (Real.log (p n)) :=
      (le_max_right _ _).trans hMbig
    nlinarith
  have hc_le : c ≤ Real.log (Real.log (p n)) / 8 :=
    (le_abs_self c).trans hcab
  have hlogM_le : Real.log (Real.log (Real.log (p n))) ≤
      Real.log (Real.log (p n)) / 4 := by
    change Real.log (Real.log (Real.log (p n))) /
      Real.log (Real.log (p n)) < 1 / 4 at hsmall
    have hlt : Real.log (Real.log (Real.log (p n))) <
        (1 / 4) * Real.log (Real.log (p n)) :=
      (div_lt_iff₀ hMpos).mp hsmall
    linarith
  have hK : Real.log (Real.log (Real.log (p n))) + c ≤
      Real.log (Real.log (p n)) / 2 := by
    linarith
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hid := paperDensityU_mul_log_eq hp hε
  rw [show 2 * (1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) =
      2 * ((1 + ε) * (paperDensityU p ε n * Real.log (paperDensityU p ε n))) by ring, hid]
  have hprod : (Real.log (p n) / paperT p n) *
      Real.log (Real.log (p n)) = paperT p n :=
    log_div_paperT_mul hp
  have hcoef : 0 ≤ Real.log (p n) / paperT p n :=
    div_nonneg hL.le (Real.sqrt_nonneg _)
  have hLK : (Real.log (p n) / paperT p n) *
      (Real.log (Real.log (Real.log (p n))) + c) ≤
        (Real.log (p n) / paperT p n) *
          (Real.log (Real.log (p n)) / 2) :=
    mul_le_mul_of_nonneg_left hK hcoef
  have hhalf : (Real.log (p n) / paperT p n) *
      (Real.log (Real.log (p n)) / 2) = paperT p n / 2 := by
    linarith
  linarith

theorem eventually_paperDensityM_le_two_u_of_growth {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (paperDensityM p ε n : ℝ) ≤ 2 * paperDensityU p ε n := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu,
    hu.eventually_ge_atTop (Real.exp 2)] with n hu1 hubig
  have hlogu : 2 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 2) hubig
    rw [Real.log_exp] at hlog
    exact hlog
  exact paperDensityM_le_two_u hu1 hlogu

theorem eventually_paperDensityM_le_four_log {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (paperDensityM p ε n : ℝ) ≤ 4 * Real.log (p n) := by
  filter_upwards [eventually_paperDensityM_le_two_u_of_growth h hε,
    h.eventually_sixteen,
    (tendsto_paperT_of_growth h).eventually_ge_atTop 1] with n hm2 hp ht1
  have hL : 0 < Real.log (p n) := Real.log_pos (by linarith)
  have hαt : 1 ≤ (1 + ε) * paperT p n := by
    have hε0 : 0 ≤ ε := hε.le
    nlinarith
  have hu_le : paperDensityU p ε n ≤ 2 * Real.log (p n) := by
    unfold paperDensityU
    rw [div_le_iff₀ (by positivity : 0 < (1 + ε) * paperT p n)]
    nlinarith [hL.le, hαt]
  nlinarith

theorem eventually_paperDensityJ_le_twelve_log {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (paperDensityJ p ε n : ℝ) ≤ 12 * Real.log (p n) := by
  filter_upwards [eventually_paperDensityM_le_two_u_of_growth h hε,
    eventually_paperDensityM_le_four_log h hε,
    h.eventually_sixteen,
    (tendsto_paperT_of_growth h).eventually_ge_atTop 1,
    (tendsto_paperDensityU_of_growth h hε).eventually_ge_atTop (Real.exp 1)] with n hm2 hm4 hp ht1 hubig
  have hL : 0 < Real.log (p n) := Real.log_pos (by linarith)
  have hlogu1 : 1 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hubig
    rw [Real.log_exp] at hlog
    exact hlog
  let ratio := (1 / 2) * ((1 + ε) * paperT p n * (paperDensityM p ε n : ℝ)) /
    (Real.log (paperDensityU p ε n) * Real.log 2)
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hJnat : paperDensityJ p ε n ≤ (paperDensityM p ε n + 1) + ⌈ratio⌉₊ := by
    unfold paperDensityJ
    exact (le_rfl.trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)))
  have hJreal : (paperDensityJ p ε n : ℝ) ≤
      (paperDensityM p ε n : ℝ) + 1 + ⌈ratio⌉₊ := by
    exact_mod_cast hJnat
  have hceil : (⌈ratio⌉₊ : ℝ) < ratio + 1 := Nat.ceil_lt_add_one hratio_nonneg
  have hratio_bound : ratio ≤ 4 * Real.log (p n) := by
    have hlog2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hcoef : 1 / (2 * Real.log 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hlog2
    have hratio_eq : ratio =
        ((1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ))) *
          (1 / (2 * Real.log 2)) / Real.log (paperDensityU p ε n) := by
      dsimp [ratio]
      ring
    rw [hratio_eq]
    have hu_eq : 2 * Real.log (p n) =
        (1 + ε) * paperT p n * paperDensityU p ε n := by
      unfold paperDensityU
      field_simp
    have htm : (1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ)) ≤
        4 * Real.log (p n) := by
      have h : paperT p n * (paperDensityM p ε n : ℝ) ≤
          paperT p n * (2 * paperDensityU p ε n) :=
        mul_le_mul_of_nonneg_left hm2 (by positivity)
      nlinarith [h, hu_eq]
    have hden : 0 < Real.log (paperDensityU p ε n) :=
      lt_of_lt_of_le (by norm_num) hlogu1
    have h1 : ((1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ))) *
        (1 / (2 * Real.log 2)) ≤
          (1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ)) :=
      mul_le_of_le_one_right (by positivity) hcoef
    have h2 : ((1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ))) *
        (1 / (2 * Real.log 2)) / Real.log (paperDensityU p ε n) ≤
          ((1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ))) /
            Real.log (paperDensityU p ε n) :=
      div_le_div_of_nonneg_right h1 hden.le
    have h3 : ((1 + ε) * (paperT p n * (paperDensityM p ε n : ℝ))) /
        Real.log (paperDensityU p ε n) ≤
          4 * Real.log (p n) / Real.log (paperDensityU p ε n) :=
      div_le_div_of_nonneg_right htm hden.le
    have h4 : 4 * Real.log (p n) / Real.log (paperDensityU p ε n) ≤
        4 * Real.log (p n) := by
      rw [div_le_iff₀ hden]
      nlinarith [hL.le, hlogu1]
    exact h2.trans (h3.trans h4)
  have hL1 : (1 : ℝ) ≤ Real.log (p n) := (one_lt_log_of_sixteen hp).le
  have hm_sum : (paperDensityM p ε n : ℝ) + 1 + ratio ≤ 12 * Real.log (p n) := by
    nlinarith [hm4, hratio_bound, hL1]
  linarith [hJreal, hceil, hm_sum]

theorem isLittleO_logLog_paperT_of_growth {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    IsLittleO atTop (fun n => Real.log (Real.log (p n))) (fun n => paperT p n) := by
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hcomp : Tendsto
      (fun n => Real.log (Real.log (p n)) / Real.log (p n)) atTop (nhds 0) :=
    tendsto_log_div_id_atTop_zero.comp h.tendsto_log
  have hsqrt : Tendsto
      (fun n => Real.sqrt (Real.log (Real.log (p n)) / Real.log (p n)))
        atTop (nhds 0) := by
    simpa using hcomp.sqrt
  have hev : ∀ᶠ n in atTop,
      Real.sqrt (Real.log (Real.log (p n)) / Real.log (p n)) < c :=
    (tendsto_order.mp hsqrt).2 c hc
  filter_upwards [hev, eventually_log_pos_of_growth h,
    eventually_log_log_pos_of_growth h] with n hn hL hM
  have hid : Real.log (Real.log (p n)) / paperT p n =
      Real.sqrt (Real.log (Real.log (p n)) / Real.log (p n)) := by
    unfold paperT
    rw [mul_comm]
    exact div_sqrt_mul hM hL
  have htnonneg : 0 ≤ paperT p n := by
    unfold paperT
    exact Real.sqrt_nonneg _
  have htpos : 0 < paperT p n := by
    unfold paperT
    exact Real.sqrt_pos_of_pos (mul_pos hL hM)
  rw [Real.norm_of_nonneg hM.le, Real.norm_of_nonneg htnonneg]
  calc
    Real.log (Real.log (p n)) = paperT p n *
        (Real.log (Real.log (p n)) / paperT p n) := by field_simp
    _ = paperT p n * Real.sqrt (Real.log (Real.log (p n)) / Real.log (p n)) := by
      rw [hid]
    _ ≤ paperT p n * c := by
      gcongr
    _ = c * paperT p n := by ring

theorem isLittleO_logLog_paperDensityU_log_of_growth {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    IsLittleO atTop (fun n => Real.log (Real.log (p n)))
      (fun n => paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
  refine (isLittleO_logLog_paperT_of_growth h).trans_isBigO ?_
  refine Asymptotics.IsBigO.of_bound (2 * (1 + ε)) ?_
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [eventually_paperT_le_two_mul_paperDensityU_log h hε,
    eventually_paperDensityU_gt_one_of_tendsto hu] with n hn hu1
  have ht_nonneg : 0 ≤ paperT p n := by
    unfold paperT
    exact Real.sqrt_nonneg _
  have hug_nonneg : 0 ≤ paperDensityU p ε n *
      Real.log (paperDensityU p ε n) :=
    mul_nonneg (zero_lt_one.trans hu1).le (Real.log_pos hu1).le
  rw [Real.norm_of_nonneg ht_nonneg, Real.norm_of_nonneg hug_nonneg]
  exact hn

theorem eventually_log_m_sq_J_le_four {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Real.log ((paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ)) ≤
        4 * Real.log (Real.log (p n)) := by
  filter_upwards [eventually_paperDensityM_le_four_log h hε,
    eventually_paperDensityJ_le_twelve_log h hε,
    h.eventually_sixteen,
    h.tendsto_log.eventually_ge_atTop 192,
    eventually_paperDensityU_pos h hε,
    eventually_paperDensityU_gt_one_of_tendsto (tendsto_paperDensityU_of_growth h hε)]
      with n hm hJ hp hL192 hu hu1
  have hL : 0 < Real.log (p n) := Real.log_pos (by linarith)
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hp)
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hJposNat : 0 < paperDensityJ p ε n := paperDensityJ_pos hmposNat
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
  have hJpos : 0 < (paperDensityJ p ε n : ℝ) := by exact_mod_cast hJposNat
  have hargpos : 0 < (paperDensityM p ε n : ℝ) ^ 2 *
      (paperDensityJ p ε n : ℝ) := by positivity
  have hle : (paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ) ≤
      (4 * Real.log (p n)) ^ 2 * (12 * Real.log (p n)) := by
    gcongr
  have hlogle := Real.log_le_log hargpos hle
  have hlogconst : Real.log ((4 * Real.log (p n)) ^ 2 *
      (12 * Real.log (p n))) =
        Real.log 192 + 3 * Real.log (Real.log (p n)) := by
    have harg : (4 * Real.log (p n)) ^ 2 * (12 * Real.log (p n)) =
        192 * (Real.log (p n)) ^ 3 := by ring
    rw [harg, Real.log_mul (by norm_num) (pow_ne_zero 3 hL.ne'), Real.log_pow]
    push_cast
    ring
  have h192 : Real.log 192 ≤ Real.log (Real.log (p n)) :=
    Real.log_le_log (by norm_num) hL192
  calc
    Real.log ((paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ))
        ≤ Real.log ((4 * Real.log (p n)) ^ 2 * (12 * Real.log (p n))) := hlogle
    _ = Real.log 192 + 3 * Real.log (Real.log (p n)) := hlogconst
    _ ≤ 4 * Real.log (Real.log (p n)) := by linarith

theorem isLittleO_log_m_sq_J_of_growth {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    IsLittleO atTop
      (fun n => Real.log
        ((paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ)))
      (fun n => paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
  have hbase := isLittleO_logLog_paperDensityU_log_of_growth h hε
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hc4 : 0 < c / 4 := by positivity
  have hev := hbase.def hc4
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [eventually_log_m_sq_J_le_four h hε, hev,
    eventually_paperDensityU_gt_one_of_tendsto hu,
    eventually_log_log_pos_of_growth h] with n hf hsmall hu1 hMpos
  have hu_pos : 0 < paperDensityU p ε n := zero_lt_one.trans hu1
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hJposNat : 0 < paperDensityJ p ε n := paperDensityJ_pos hmposNat
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
  have hJpos : 0 < (paperDensityJ p ε n : ℝ) := by exact_mod_cast hJposNat
  have harg : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) ^ 2 *
      (paperDensityJ p ε n : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
    have hJ1 : (1 : ℝ) ≤ (paperDensityJ p ε n : ℝ) := by exact_mod_cast hJposNat
    have hm1sq : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) ^ 2 := by nlinarith [hm1]
    nlinarith [mul_le_mul hm1sq hJ1 (by positivity) (by positivity)]
  have hf_nonneg : 0 ≤ Real.log
      ((paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ)) :=
    Real.log_nonneg harg
  have hug_nonneg : 0 ≤ paperDensityU p ε n *
      Real.log (paperDensityU p ε n) :=
    mul_nonneg hu_pos.le (Real.log_pos hu1).le
  rw [Real.norm_of_nonneg hf_nonneg, Real.norm_of_nonneg hug_nonneg]
  have hM_nonneg : 0 ≤ Real.log (Real.log (p n)) := hMpos.le
  have hsmall' : Real.log (Real.log (p n)) ≤
      (c / 4) * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by
    simpa [Real.norm_of_nonneg hM_nonneg, Real.norm_of_nonneg hug_nonneg] using hsmall
  calc
    Real.log ((paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ))
        ≤ 4 * Real.log (Real.log (p n)) := hf
    _ ≤ 4 * ((c / 4) * (paperDensityU p ε n *
          Real.log (paperDensityU p ε n))) := by gcongr
    _ = c * (paperDensityU p ε n * Real.log (paperDensityU p ε n)) := by ring

theorem eventually_paperDensityM_le_sharp_of_growth {p : ℕ → ℝ} {ε : ℝ}
    (h : PaperDensityGrowth p) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (paperDensityM p ε n : ℝ) ≤
      paperDensityU p ε n * (1 + 2 / Real.log (paperDensityU p ε n)) := by
  have hu := tendsto_paperDensityU_of_growth h hε
  filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu,
    hu.eventually_ge_atTop (Real.exp 2)] with n hu1 hubig
  have hlogu : 2 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 2) hubig
    rw [Real.log_exp] at hlog
    exact hlog
  exact paperDensityM_le_sharp hu1 hlogu

theorem paperDensity_logP_ge_sharp {p : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hp : 1 < p n) (hm : 0 < paperDensityM p ε n)
    (hkm : (paperDensityM p ε n : ℝ) ≤
      paperDensityU p ε n * (1 + 2 / Real.log (paperDensityU p ε n)))
    (ht : 0 < paperT p n) (hε : 0 < ε)
    (hlogu : 0 < Real.log (paperDensityU p ε n)) :
    (1 + ε) * paperT p n - 3 * ((1 + ε) * paperT p n) /
        Real.log (paperDensityU p ε n) - Real.log 4 /
          paperDensityU p ε n ≤ Real.log (paperDensityP p ε n) := by
  have hp0 : 0 < p n := zero_lt_one.trans hp
  have hL : 0 < Real.log (p n) := Real.log_pos hp
  have hu : 0 < paperDensityU p ε n := by
    unfold paperDensityU
    positivity
  have hα : 0 < 1 + ε := by positivity
  have hden : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hm
  rw [paperDensity_logP hp0 hm, sub_div]
  have htwoL : 2 * Real.log (p n) =
      (1 + ε) * paperT p n * paperDensityU p ε n := by
    unfold paperDensityU
    field_simp
  have hu_le_m : paperDensityU p ε n ≤ (paperDensityM p ε n : ℝ) :=
    paperDensityU_le_paperDensityM p ε n hu hlogu
  have hminv : (1 / paperDensityU p ε n) *
      (1 - 3 / Real.log (paperDensityU p ε n)) ≤
        1 / (paperDensityM p ε n : ℝ) := by
    have hfrac : 1 - 3 / Real.log (paperDensityU p ε n) ≤
        1 / (1 + 2 / Real.log (paperDensityU p ε n)) := by
      rw [le_div_iff₀ (by positivity : 0 < 1 + 2 / Real.log (paperDensityU p ε n))]
      field_simp
      nlinarith [sq_nonneg (Real.log (paperDensityU p ε n))]
    have hden2 : 0 < paperDensityU p ε n *
        (1 + 2 / Real.log (paperDensityU p ε n)) := by positivity
    calc
      (1 / paperDensityU p ε n) * (1 - 3 / Real.log (paperDensityU p ε n))
          ≤ (1 / paperDensityU p ε n) *
              (1 / (1 + 2 / Real.log (paperDensityU p ε n))) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 1 / (paperDensityU p ε n *
            (1 + 2 / Real.log (paperDensityU p ε n))) := by field_simp
      _ ≤ 1 / (paperDensityM p ε n : ℝ) :=
            one_div_le_one_div_of_le hden hkm
  have hmain : 2 * Real.log (p n) / (paperDensityM p ε n : ℝ) ≥
      (1 + ε) * paperT p n *
        (1 - 3 / Real.log (paperDensityU p ε n)) := by
    have hmul := mul_le_mul_of_nonneg_left hminv (show 0 ≤ 2 * Real.log (p n) by positivity)
    have hrewrite : 2 * Real.log (p n) * (1 / paperDensityU p ε n) =
        (1 + ε) * paperT p n := by
      calc
        2 * Real.log (p n) * (1 / paperDensityU p ε n) =
            (2 * Real.log (p n)) / paperDensityU p ε n := by ring
        _ = ((1 + ε) * paperT p n * paperDensityU p ε n) /
              paperDensityU p ε n := by rw [htwoL]
        _ = (1 + ε) * paperT p n := by field_simp
    have hmul' : (1 + ε) * paperT p n *
        (1 - 3 / Real.log (paperDensityU p ε n)) ≤
          2 * Real.log (p n) / (paperDensityM p ε n : ℝ) := by
      have hreq : 2 * Real.log (p n) *
          (1 / paperDensityU p ε n * (1 - 3 / Real.log (paperDensityU p ε n))) =
            (1 + ε) * paperT p n *
              (1 - 3 / Real.log (paperDensityU p ε n)) := by
        rw [show 2 * Real.log (p n) *
            (1 / paperDensityU p ε n * (1 - 3 / Real.log (paperDensityU p ε n))) =
              (2 * Real.log (p n) * (1 / paperDensityU p ε n)) *
                (1 - 3 / Real.log (paperDensityU p ε n)) by ring, hrewrite]
      rw [hreq] at hmul
      rw [show 2 * Real.log (p n) / (paperDensityM p ε n : ℝ) =
          2 * Real.log (p n) * (1 / (paperDensityM p ε n : ℝ)) by ring]
      exact hmul
    exact hmul'
  have hlog4 : Real.log 4 / (paperDensityM p ε n : ℝ) ≤
      Real.log 4 / paperDensityU p ε n := by
    have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact div_le_div_of_nonneg_left hlog4pos hu hu_le_m
  have hmain' : (1 + ε) * paperT p n - 3 * ((1 + ε) * paperT p n) /
      Real.log (paperDensityU p ε n) ≤
        2 * Real.log (p n) / (paperDensityM p ε n : ℝ) := by
    have hrew : (1 + ε) * paperT p n *
        (1 - 3 / Real.log (paperDensityU p ε n)) =
        (1 + ε) * paperT p n -
          3 * ((1 + ε) * paperT p n) / Real.log (paperDensityU p ε n) := by ring
    rwa [hrew] at hmain
  have hmain'' : (1 + ε) * paperT p n -
        3 * ((1 + ε) * paperT p n) / Real.log (paperDensityU p ε n) -
          Real.log 4 / paperDensityU p ε n ≤
      2 * Real.log (p n) / (paperDensityM p ε n : ℝ) -
        Real.log 4 / (paperDensityM p ε n : ℝ) := by
    linarith [hmain', hlog4]
  simpa [sub_div] using hmain''

private theorem isLittleO_logLogLog_paperT_of_growth {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    IsLittleO atTop
      (fun n => Real.log (Real.log (Real.log (p n)))) (fun n => paperT p n) := by
  have hM : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  have h1 : IsLittleO atTop
      (fun n => Real.log (Real.log (Real.log (p n))))
      (fun n => Real.log (Real.log (p n))) :=
    Real.isLittleO_log_id_atTop.comp_tendsto hM
  exact h1.trans_isBigO (isLittleO_logLog_paperT_of_growth h).isBigO

private theorem isLittleO_log_paperT_of_growth {p : ℕ → ℝ}
    (h : PaperDensityGrowth p) :
    IsLittleO atTop (fun n => Real.log (paperT p n)) (fun n => paperT p n) :=
  Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_paperT_of_growth h)

/-- The explicit supply guard of the prime-bin density theorem at the paper
schedule. -/
theorem eventually_paperDensity_guard (K : ℝ) (hK : 0 ≤ K)
    {p : ℕ → ℝ} (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      K * (1 + Real.log (3 * paperDensityY p ε n)) ^ 2 *
          Real.sqrt (paperDensityY p ε n) + 1 ≤
        (1 - (1 / 2)) * paperDensityDelta p ε n *
          (paperDensityP p ε n *
            Real.exp (-(paperDensityDelta p ε n *
              (paperDensityJ p ε n : ℝ)))) := by
  let α : ℝ := 1 + ε
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hα1 : 1 ≤ α := by dsimp [α]; linarith [hε.le]
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have ht_tend := tendsto_paperT_of_growth h
  have hMtend : Tendsto (fun n => Real.log (Real.log (p n))) atTop atTop :=
    Real.tendsto_log_atTop.comp h.tendsto_log
  let T0 : ℝ := max 256
    (32 * (Real.log 4 + Real.log (K + 1) + 2 * Real.log (α + 1) + 1))
  filter_upwards [
    h.eventually_sixteen,
    eventually_paperDensityU_pos h hε,
    eventually_paperDensityU_gt_one_of_tendsto hu_tend,
    hu_tend.eventually_ge_atTop (Real.exp 200),
    eventually_paperDensityM_le_sharp_of_growth h hε,
    eventually_paperDensityM_le_two_u_of_growth h hε,
    eventually_paperDensityM_le_four_log h hε,
    eventually_paperDensityJ_le_twelve_log h hε,
    eventually_log_m_sq_J_le_four h hε,
    h.tendsto_log.eventually_ge_atTop 192,
    ht_tend.eventually_ge_atTop T0,
    (isLittleO_logLog_paperT_of_growth h).def (show 0 < α / 128 by positivity),
    (isLittleO_logLogLog_paperT_of_growth h).def (show 0 < α / 128 by positivity),
    (isLittleO_log_paperT_of_growth h).def (show 0 < α / 128 by positivity)] with
      n hp16 hu hu1 hubig hmsharp hm2 hm4 hJ12 hlogmJ hL192 ht1 hMsmall hlogMsmall hlogtsmall
  have hp1 : (1 : ℝ) < p n := by linarith
  have hL : 0 < Real.log (p n) := Real.log_pos hp1
  have hM : 0 < Real.log (Real.log (p n)) := Real.log_pos (one_lt_log_of_sixteen hp16)
  have hT0ge : (256 : ℝ) ≤ T0 := by
    dsimp only [T0]
    exact le_max_left _ _
  have ht : 0 < paperT p n := by
    have hT0 : (1 : ℝ) ≤ T0 := le_trans (by norm_num) hT0ge
    linarith
  have hlogu_ge : 200 ≤ Real.log (paperDensityU p ε n) := by
    have hlog := Real.log_le_log (Real.exp_pos 200) hubig
    rwa [Real.log_exp] at hlog
  have hlogu : 0 < Real.log (paperDensityU p ε n) :=
    lt_of_lt_of_le (by norm_num) hlogu_ge
  have hlogu1 : 1 ≤ Real.log (paperDensityU p ε n) :=
    le_trans (by norm_num) hlogu_ge
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hJposNat : 0 < paperDensityJ p ε n := paperDensityJ_pos hmposNat
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
  have hJpos : 0 < (paperDensityJ p ε n : ℝ) := by exact_mod_cast hJposNat
  have hlogP := paperDensity_logP_ge_sharp hp1 hmposNat hmsharp ht hε hlogu
  have hdeltaJ := paperDensityDelta_mul_J hJposNat hlogu.ne'
  have hJlog : Real.log (paperDensityJ p ε n : ℝ) ≤
      4 * Real.log (Real.log (p n)) := by
    have hJle : (paperDensityJ p ε n : ℝ) ≤
        (paperDensityM p ε n : ℝ) ^ 2 * (paperDensityJ p ε n : ℝ) := by
      have hm1 : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) := by exact_mod_cast hmposNat
      have hm1sq : (1 : ℝ) ≤ (paperDensityM p ε n : ℝ) ^ 2 := by nlinarith [hm1]
      nlinarith [hm1sq, hJpos]
    exact (Real.log_le_log hJpos hJle).trans hlogmJ
  have hloglogu : Real.log (Real.log (paperDensityU p ε n)) ≤
      Real.log 2 + Real.log (Real.log (Real.log (p n))) := by
    have hu_le : paperDensityU p ε n ≤ 2 * Real.log (p n) := by
      unfold paperDensityU
      have hden : 0 < α * paperT p n := by dsimp [α]; positivity
      rw [div_le_iff₀ hden]
      have hαt : (1 : ℝ) ≤ α * paperT p n := by nlinarith [hα1, ht1]
      nlinarith [hL.le, hαt]
    have hlogu_le : Real.log (paperDensityU p ε n) ≤
        Real.log 2 + Real.log (Real.log (p n)) := by
      calc
        Real.log (paperDensityU p ε n) ≤
            Real.log (2 * Real.log (p n)) :=
              Real.log_le_log hu (by simpa [α] using hu_le)
        _ = Real.log 2 + Real.log (Real.log (p n)) :=
              Real.log_mul (by norm_num) hL.ne'
    have hMbig : (1 : ℝ) ≤ Real.log (Real.log (p n)) :=
      (one_lt_logLog_of_sixteen hp16).le
    calc
      Real.log (Real.log (paperDensityU p ε n)) ≤
          Real.log (Real.log 2 + Real.log (Real.log (p n))) :=
            Real.log_le_log (Real.log_pos hu1) hlogu_le
      _ ≤ Real.log (Real.log (Real.log (p n)) + Real.log (Real.log (p n))) := by
            apply Real.log_le_log
            · positivity
            · have hlog2le1 : Real.log 2 ≤ 1 := by
                linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
              linarith [hMbig, hlog2le1]
      _ = Real.log (2 * Real.log (Real.log (p n))) := by
            congr 1
            ring
      _ = Real.log 2 + Real.log (Real.log (Real.log (p n))) :=
            Real.log_mul (by norm_num) hM.ne'
  have hlogpoly : Real.log (4 * K * α ^ 2 * paperT p n ^ 2 + 1) ≤
      α * paperT p n / 16 := by
    have hKα : 0 ≤ 4 * K * α ^ 2 := by positivity
    have ht1' : (1 : ℝ) ≤ paperT p n := by linarith [hT0ge, ht1]
    have hbound : 4 * K * α ^ 2 * paperT p n ^ 2 + 1 ≤
        (4 * K * α ^ 2 + 1) * paperT p n ^ 2 := by
      have : (1 : ℝ) ≤ paperT p n ^ 2 := by nlinarith
      nlinarith [hKα, this]
    have hlogbound := Real.log_le_log (by positivity) hbound
    have hexpand : Real.log ((4 * K * α ^ 2 + 1) * paperT p n ^ 2) =
        Real.log (4 * K * α ^ 2 + 1) + 2 * Real.log (paperT p n) := by
      rw [Real.log_mul (by positivity) (pow_ne_zero 2 ht.ne'), Real.log_pow]
      push_cast
      ring
    have hconstsmall : Real.log (4 * K * α ^ 2 + 1) ≤ α * paperT p n / 32 := by
      have htsmall := hlogtsmall
      -- `T0` is chosen so that every fixed logarithmic constant is paid for
      have htbig : Real.log 4 + Real.log (K + 1) + 2 * Real.log (α + 1) + 1 ≤
          α * paperT p n / 32 := by
        have hT0le : T0 ≤ α * paperT p n := by
          dsimp only [T0]
          nlinarith [hα1, ht1]
        have hT0C : 32 * (Real.log 4 + Real.log (K + 1) +
            2 * Real.log (α + 1) + 1) ≤ T0 := by
          dsimp only [T0]
          exact le_max_right _ _
        nlinarith [hT0le, hT0C]
      have hlogarg : Real.log (4 * K * α ^ 2 + 1) ≤
          Real.log 4 + Real.log (K + 1) + 2 * Real.log (α + 1) + 1 := by
        have hle : 4 * K * α ^ 2 + 1 ≤ 4 * (K + 1) * (α + 1) ^ 2 := by
          nlinarith [sq_nonneg (α + 1), hK]
        calc
          Real.log (4 * K * α ^ 2 + 1) ≤ Real.log (4 * (K + 1) * (α + 1) ^ 2) :=
            Real.log_le_log (by positivity) hle
          _ = Real.log 4 + Real.log (K + 1) + 2 * Real.log (α + 1) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity), Real.log_pow]
            push_cast
            ring
          _ ≤ Real.log 4 + Real.log (K + 1) + 2 * Real.log (α + 1) + 1 := by linarith
      exact hlogarg.trans htbig
    have htlogsmall : 2 * Real.log (paperT p n) ≤ α * paperT p n / 32 := by
      have h := hlogtsmall
      change ‖Real.log (paperT p n)‖ ≤ (α / 128) * ‖paperT p n‖ at h
      have hpos : 0 ≤ paperT p n := ht.le
      have ht1' : (1 : ℝ) ≤ paperT p n := by linarith [hT0ge, ht1]
      rw [Real.norm_of_nonneg (Real.log_nonneg ht1'),
        Real.norm_of_nonneg hpos] at h
      nlinarith
    calc
      Real.log (4 * K * α ^ 2 * paperT p n ^ 2 + 1)
          ≤ Real.log ((4 * K * α ^ 2 + 1) * paperT p n ^ 2) := hlogbound
      _ = Real.log (4 * K * α ^ 2 + 1) + 2 * Real.log (paperT p n) := hexpand
      _ ≤ α * paperT p n / 32 + α * paperT p n / 32 :=
            add_le_add hconstsmall htlogsmall
      _ = α * paperT p n / 16 := by ring
  have hLHS_le : K * (1 + Real.log (3 * paperDensityY p ε n)) ^ 2 *
      Real.sqrt (paperDensityY p ε n) + 1 ≤
        (4 * K * α ^ 2 * paperT p n ^ 2 + 1) *
          Real.exp (α * paperT p n / 2) := by
    have hYeq : paperDensityY p ε n = Real.exp (α * paperT p n) := by
      dsimp [paperDensityY, α]
    have hsqrteq : Real.sqrt (paperDensityY p ε n) =
        Real.exp (α * paperT p n / 2) := by
      rw [hYeq, Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring
    have hlog3 : Real.log (3 * paperDensityY p ε n) =
        Real.log 3 + α * paperT p n := by
      rw [hYeq, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have hsum : 1 + Real.log (3 * paperDensityY p ε n) ≤ 2 * α * paperT p n := by
      rw [hlog3]
      have hαt256 : (256 : ℝ) ≤ α * paperT p n := by nlinarith [hα1, ht1, hT0ge]
      have hlog3le : Real.log 3 ≤ 2 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hαt256, hlog3le]
    have hsum_nonneg : 0 ≤ 1 + Real.log (3 * paperDensityY p ε n) := by
      rw [hlog3]
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith [hα1, ht1]
    have hsquare : (1 + Real.log (3 * paperDensityY p ε n)) ^ 2 ≤
        (2 * α * paperT p n) ^ 2 := by
      nlinarith [hsum, hsum_nonneg]
    have hexp1 : (1 : ℝ) ≤ Real.exp (α * paperT p n / 2) :=
      Real.one_le_exp (by positivity)
    calc
      K * (1 + Real.log (3 * paperDensityY p ε n)) ^ 2 *
          Real.sqrt (paperDensityY p ε n) + 1
          ≤ K * (2 * α * paperT p n) ^ 2 *
              Real.exp (α * paperT p n / 2) + 1 := by
            rw [hsqrteq]
            gcongr
      _ ≤ (4 * K * α ^ 2 * paperT p n ^ 2 + 1) *
            Real.exp (α * paperT p n / 2) := by
            have hKnonneg : 0 ≤ K := hK
            have hrewrite : K * (2 * α * paperT p n) ^ 2 = 4 * K * α ^ 2 * paperT p n ^ 2 := by
              ring
            rw [hrewrite]
            nlinarith [hexp1, mul_nonneg (by positivity : 0 ≤ 4 * K * α ^ 2 * paperT p n ^ 2)
              (sub_nonneg.mpr hexp1)]
  have hRHS_log : Real.log ((1 - (1 / 2)) * paperDensityDelta p ε n *
      (paperDensityP p ε n * Real.exp (-(paperDensityDelta p ε n *
        (paperDensityJ p ε n : ℝ))))) =
      Real.log (α * paperT p n) - Real.log 4 -
        Real.log (paperDensityJ p ε n : ℝ) - Real.log (Real.log (paperDensityU p ε n)) +
          Real.log (paperDensityP p ε n) -
            paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) := by
    have hcoef : (1 - (1 / 2)) * paperDensityDelta p ε n =
        (α * paperT p n / 4) / ((paperDensityJ p ε n : ℝ) *
          Real.log (paperDensityU p ε n)) := by
      dsimp [paperDensityDelta, α]
      field_simp
      ring
    have hPposn : 0 < paperDensityP p ε n :=
      paperDensityP_pos (by linarith : 0 < p n)
    have hJne : (paperDensityJ p ε n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hJposNat)
    have hcoefpos : 0 < (α * paperT p n / 4) /
        ((paperDensityJ p ε n : ℝ) * Real.log (paperDensityU p ε n)) := by positivity
    rw [hcoef]
    rw [Real.log_mul hcoefpos.ne' (mul_pos hPposn (Real.exp_pos _)).ne']
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_mul hαpos.ne' ht.ne']
    rw [Real.log_mul hJne hlogu.ne']
    rw [Real.log_mul hPposn.ne' (Real.exp_pos _).ne']
    rw [Real.log_exp]
    ring
  have hlogRHS_lower : α * paperT p n - (7 / 2) * (α * paperT p n) /
        Real.log (paperDensityU p ε n) - Real.log 4 / paperDensityU p ε n +
          Real.log (α * paperT p n) - Real.log 4 -
            Real.log (paperDensityJ p ε n : ℝ) -
              Real.log (Real.log (paperDensityU p ε n)) ≤
      Real.log ((1 - (1 / 2)) * paperDensityDelta p ε n *
        (paperDensityP p ε n * Real.exp (-(paperDensityDelta p ε n *
          (paperDensityJ p ε n : ℝ))))) := by
    rw [hRHS_log]
    have hdeltaJ' : paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ) =
        α * paperT p n / (2 * Real.log (paperDensityU p ε n)) := by
      rw [hdeltaJ]
      dsimp [α]
      ring
    rw [hdeltaJ']
    have hlogP' : α * paperT p n - 3 * (α * paperT p n) /
        Real.log (paperDensityU p ε n) - Real.log 4 / paperDensityU p ε n ≤
          Real.log (paperDensityP p ε n) := by
      simpa [α] using hlogP
    have hlogu_ne : Real.log (paperDensityU p ε n) ≠ 0 := hlogu.ne'
    have h7 : (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) =
        3 * (α * paperT p n) / Real.log (paperDensityU p ε n) +
          α * paperT p n / (2 * Real.log (paperDensityU p ε n)) := by ring
    rw [h7]
    linarith [hlogP']
  have hbudget : Real.log (4 * K * α ^ 2 * paperT p n ^ 2 + 1) +
      (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) +
        Real.log 4 / paperDensityU p ε n + Real.log 4 +
          Real.log (paperDensityJ p ε n : ℝ) +
            Real.log (Real.log (paperDensityU p ε n)) ≤
      α * paperT p n / 2 := by
    have hlogusmall : (7 / 2) * (α * paperT p n) /
        Real.log (paperDensityU p ε n) ≤ α * paperT p n / 32 := by
      rw [div_le_iff₀ hlogu]
      have hcoef : (7 / 2 : ℝ) ≤ (1 / 32) * Real.log (paperDensityU p ε n) := by
        nlinarith [hlogu_ge]
      nlinarith [mul_le_mul_of_nonneg_left hcoef (mul_nonneg hαpos.le ht.le)]
    have hlog4u : Real.log 4 / paperDensityU p ε n ≤ α * paperT p n / 32 := by
      have hu128 : (128 : ℝ) ≤ paperDensityU p ε n := by
        have hge1 : (1 : ℝ) ≤ Real.exp 200 := Real.one_le_exp (by norm_num)
        have h201 : (201 : ℝ) ≤ Real.exp 200 := by
          linarith [Real.add_one_le_exp 200]
        linarith
      rw [div_le_iff₀ hu]
      have hlog4le : Real.log 4 ≤ 4 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
      have hαt1 : (1 : ℝ) ≤ α * paperT p n := by nlinarith [hα1, ht1]
      nlinarith [hlog4le, hu128, hαt1, hαpos.le, ht.le]
    have hlog4small : Real.log 4 ≤ α * paperT p n / 32 := by
      have hlog4le : Real.log 4 ≤ 4 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
      have hαt256 : (256 : ℝ) ≤ α * paperT p n := by nlinarith [hα1, ht1, hT0ge]
      nlinarith [hlog4le, hαt256]
    have hJsmall : Real.log (paperDensityJ p ε n : ℝ) ≤ α * paperT p n / 32 := by
      have hMle : Real.log (Real.log (p n)) ≤ α * paperT p n / 128 := by
        change ‖Real.log (Real.log (p n))‖ ≤ (α / 128) * ‖paperT p n‖ at hMsmall
        rw [Real.norm_of_nonneg hM.le, Real.norm_of_nonneg ht.le] at hMsmall
        linarith
      linarith [hJlog]
    have hloglogusmall : Real.log (Real.log (paperDensityU p ε n)) ≤
        α * paperT p n / 32 := by
      have hlogMle : Real.log (Real.log (Real.log (p n))) ≤
          α * paperT p n / 128 := by
        change ‖Real.log (Real.log (Real.log (p n)))‖ ≤
          (α / 128) * ‖paperT p n‖ at hlogMsmall
        have hLLLnonneg : 0 ≤ Real.log (Real.log (Real.log (p n))) :=
          Real.log_nonneg (one_lt_logLog_of_sixteen hp16).le
        rw [Real.norm_of_nonneg hLLLnonneg, Real.norm_of_nonneg ht.le] at hlogMsmall
        linarith
      have hlog2small : Real.log 2 ≤ α * paperT p n / 128 := by
        have hαt256 : (256 : ℝ) ≤ α * paperT p n := by nlinarith [hα1, ht1, hT0ge]
        have hlog2le : Real.log 2 ≤ 1 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hαt256, hlog2le]
      have hsum : Real.log 2 + Real.log (Real.log (Real.log (p n))) ≤
          α * paperT p n / 64 := by linarith [hlog2small, hlogMle]
      calc
        Real.log (Real.log (paperDensityU p ε n)) ≤
            Real.log 2 + Real.log (Real.log (Real.log (p n))) := hloglogu
        _ ≤ α * paperT p n / 64 := hsum
        _ ≤ α * paperT p n / 32 := by
            have hαt_nonneg : 0 ≤ α * paperT p n := by positivity
            nlinarith [hαt_nonneg]
    nlinarith [hlogpoly, hlogusmall, hlog4u, hlog4small, hJsmall, hloglogusmall]
  have hLHS_le_exp : K * (1 + Real.log (3 * paperDensityY p ε n)) ^ 2 *
      Real.sqrt (paperDensityY p ε n) + 1 ≤
        Real.exp (α * paperT p n - (7 / 2) * (α * paperT p n) /
          Real.log (paperDensityU p ε n) - Real.log 4 / paperDensityU p ε n +
            Real.log (α * paperT p n) - Real.log 4 -
              Real.log (paperDensityJ p ε n : ℝ) -
                Real.log (Real.log (paperDensityU p ε n))) := by
    refine hLHS_le.trans ?_
    rw [← Real.exp_log (by positivity : 0 < 4 * K * α ^ 2 * paperT p n ^ 2 + 1)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hpoly : Real.log (4 * K * α ^ 2 * paperT p n ^ 2 + 1) ≤
        α * paperT p n / 2 -
          (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) -
            Real.log 4 / paperDensityU p ε n - Real.log 4 -
              Real.log (paperDensityJ p ε n : ℝ) -
                Real.log (Real.log (paperDensityU p ε n)) := by
      linarith [hbudget]
    have ht1' : (1 : ℝ) ≤ paperT p n := by
      have hT0 : (1 : ℝ) ≤ T0 := by
        dsimp only [T0]
        exact le_trans (by norm_num) (le_max_left _ _)
      linarith
    have hlogαt_nonneg : 0 ≤ Real.log (α * paperT p n) :=
      Real.log_nonneg (by nlinarith [hα1, ht1'])
    have hstep1 : Real.log (4 * K * α ^ 2 * paperT p n ^ 2 + 1) + α * paperT p n / 2 ≤
        α * paperT p n -
          (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) -
            Real.log 4 / paperDensityU p ε n - Real.log 4 -
              Real.log (paperDensityJ p ε n : ℝ) -
                Real.log (Real.log (paperDensityU p ε n)) := by
      linarith [hpoly]
    have hstep2 : α * paperT p n -
          (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) -
            Real.log 4 / paperDensityU p ε n - Real.log 4 -
              Real.log (paperDensityJ p ε n : ℝ) -
                Real.log (Real.log (paperDensityU p ε n)) ≤
        α * paperT p n -
          (7 / 2) * (α * paperT p n) / Real.log (paperDensityU p ε n) -
            Real.log 4 / paperDensityU p ε n + Real.log (α * paperT p n) - Real.log 4 -
              Real.log (paperDensityJ p ε n : ℝ) -
                Real.log (Real.log (paperDensityU p ε n)) := by
      linarith [hlogαt_nonneg]
    linarith [hstep1, hstep2, hlogRHS_lower]
  have hRHSpos : 0 < (1 - (1 / 2)) * paperDensityDelta p ε n *
      (paperDensityP p ε n * Real.exp (-(paperDensityDelta p ε n *
        (paperDensityJ p ε n : ℝ)))) := by
    have hε1 : (0 : ℝ) < 1 - (1 / 2) := by norm_num
    exact mul_pos (mul_pos hε1 (paperDensityDelta_pos hε ht hJposNat hlogu))
      (mul_pos (paperDensityP_pos (by linarith : 0 < p n)) (Real.exp_pos _))
  have hER := Real.exp_le_exp.mpr hlogRHS_lower
  rw [Real.exp_log hRHSpos] at hER
  exact hLHS_le_exp.trans hER

/-! ## 6. The global odd smooth count -/

/-- The doubled prime-bin products are global odd-half smooth orders. -/
theorem doubledCenteredBinProducts_subset_globalOddSmoothOrders
    {P δ : ℝ} {J k a : ℕ} {p t err : ℕ → ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hk : 0 < k)
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor P δ a k j)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) ≤ p n ^ 2 / 2)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤
      smoothCutoff t err n)
    (hy2 : 2 ≤ smoothCutoff t err n) :
    doubledCenteredBinProducts P δ J k a ⊆ globalOddSmoothOrders p t err n := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := mem_doubledCenteredBinProducts.mp hm
  have hxpos : 0 < x := by
    unfold centeredBinProducts primeBinPatternProducts at hx
    obtain ⟨s, hs, hprod⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hprod
    exact Finset.prod_pos fun i _ =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf i)).2.pos
  have hstrip := centeredBinProducts_mem_strip hP hk hx
  have hxhi : (x : ℝ) ≤ p n ^ 2 / 2 := hstrip.2.trans hhi
  have h2x : ((2 * x : ℕ) : ℝ) ≤ p n ^ 2 := by
    rw [Nat.cast_mul]
    norm_num
    linarith
  have h2xpos : (1 : ℕ) ≤ 2 * x := by omega
  have hsmooth : IsSmoothUpTo (smoothCutoff t err n) (2 * x) := by
    intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hdvd : q ∣ 2 * x := Nat.dvd_of_mem_primeFactors hq
    rcases hqprime.dvd_mul.mp hdvd with hq2 | hqx
    · have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp hq2
      rw [hqeq]
      exact hy2
    · have hxmem : q ∈ x.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqprime, hqx, hxpos.ne'⟩
      exact centeredBinProducts_smooth hfloor hx q hxmem
  have hoddhalf : IsOddHalfOrder (2 * x) :=
    two_mul_odd_mod_four (centeredBinProducts_odd_of_oddBins hodd hx)
  rw [globalOddSmoothOrders, Finset.mem_filter]
  constructor
  · rw [globalSmoothOrders, Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨h2xpos, Nat.le_floor h2x⟩
    · exact hsmooth
  · exact hoddhalf

theorem globalOddSmoothCount_lower_of_binCount
    {P δ : ℝ} {J k a : ℕ} {p t err : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (hP : 0 ≤ P) (hk : 0 < k)
    (hodd : ∀ j < J, 3 ≤ centeredBinFloor P δ a k j)
    (hhi : P ^ k * Real.exp ((k : ℝ) * δ) ≤ p n ^ 2 / 2)
    (hfloor : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤
      smoothCutoff t err n)
    (hy2 : 2 ≤ smoothCutoff t err n)
    (hcount : c ≤ ((centeredBinProducts P δ J k a).card : ℝ)) :
    c ≤ globalOddSmoothCount p t err n := by
  have hsub := doubledCenteredBinProducts_subset_globalOddSmoothOrders
    hP hk hodd hhi hfloor hy2
  have hcard : ((doubledCenteredBinProducts P δ J k a).card : ℝ) ≤
      globalOddSmoothCount p t err n := by
    unfold globalOddSmoothCount
    exact_mod_cast Finset.card_le_card hsub
  rw [doubledCenteredBinProducts_card] at hcard
  exact hcount.trans hcard

theorem paperDensityU_mul_le_M (p : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n)) ≤
      (paperDensityM p ε n : ℝ) :=
  Nat.le_ceil _

/-- **The explicit prime-bin count at the paper scale.** -/
theorem eventually_paperDensity_binCount (line : DirichletLZerosOnLine)
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∃ a ∈ Finset.range (paperDensityM p ε n * (paperDensityJ p ε n - 1) + 1),
        (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) ≤
          ((centeredBinProducts (paperDensityP p ε n)
            (paperDensityDelta p ε n) (paperDensityJ p ε n)
            (paperDensityM p ε n) a).card : ℝ) := by
  obtain ⟨K, hK, hmain⟩ := eventually_centeredBinProducts_density_from_critical_line line
  have hguard := eventually_paperDensity_guard K hK h hε
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have ht_tend := tendsto_paperT_of_growth h
  have hPpos : ∀ᶠ n in atTop, 0 < paperDensityP p ε n := by
    filter_upwards [h.eventually_sixteen] with n hp
    exact paperDensityP_pos (by linarith)
  have hδnonneg : ∀ᶠ n in atTop, 0 ≤ paperDensityDelta p ε n := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend] with n hp ht hu1
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    exact (paperDensityDelta_pos hε ht hJpos (Real.log_pos hu1)).le
  have hy1 : ∀ᶠ n in atTop, 1 < paperDensityY p ε n := by
    filter_upwards [eventually_paperT_pos_of_growth h] with n ht
    dsimp [paperDensityY]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hJδ : ∀ᶠ n in atTop,
      (1 / 2) * Real.log (paperDensityY p ε n) /
          Real.log (paperDensityU p ε n) ≤
        (paperDensityJ p ε n : ℝ) * paperDensityDelta p ε n := by
    filter_upwards [eventually_paperDensityU_gt_one_of_tendsto hu_tend] with n hu1
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    have hlogu : Real.log (paperDensityU p ε n) ≠ 0 := (Real.log_pos hu1).ne'
    have hy : Real.log (paperDensityY p ε n) = (1 + ε) * paperT p n := by
      dsimp [paperDensityY]
      rw [Real.log_exp]
    rw [hy]
    rw [mul_comm (paperDensityJ p ε n : ℝ) (paperDensityDelta p ε n)]
    rw [paperDensityDelta_mul_J hJpos hlogu]
  have hJm : ∀ᶠ n in atTop,
      ⌈paperDensityU p ε n * (1 + 1 / Real.log (paperDensityU p ε n))⌉₊ ≤
        paperDensityJ p ε n := by
    filter_upwards with n
    exact Nat.le_trans (Nat.le_succ _) (paperDensityJ_ge_m p ε n)
  have hlog := isLittleO_log_m_sq_J_of_growth h hε
  have hlarge : ∀ᶠ n in atTop,
      Real.log 3 + Real.log 4 ≤
        (1 / 2) * ((1 + ε) * paperT p n) *
          (1 - 1 / Real.log (paperDensityU p ε n)) := by
    filter_upwards [ht_tend.eventually_ge_atTop (4 * (Real.log 3 + Real.log 4)),
      hu_tend.eventually_ge_atTop (Real.exp 2)] with n htbig hubig
    have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 2) hubig
      rwa [Real.log_exp] at hlog
    have hinv : 1 / Real.log (paperDensityU p ε n) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogu2
    have hα1 : 1 ≤ 1 + ε := by linarith [hε.le]
    have hpos : 0 < 4 * (Real.log 3 + Real.log 4) := by positivity
    have htpos : 0 < paperT p n := by linarith
    have hαt : 4 * (Real.log 3 + Real.log 4) ≤ (1 + ε) * paperT p n := by
      have htle : paperT p n ≤ (1 + ε) * paperT p n := by nlinarith [hε.le, htpos.le]
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / Real.log (paperDensityU p ε n) := by linarith
    have hnonneg : 0 ≤ (1 / 2) * ((1 + ε) * paperT p n) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg, hαt]
  have hlo : ∀ᶠ n in atTop,
      (2 : ℝ) ≤ paperDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend,
      eventually_paperDensityM_le_two_u_of_growth h hε,
      hu_tend.eventually_ge_atTop (Real.exp 2), hlarge] with n hp ht hu1 hm2 hubig hlarge_n
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 2) hubig
      rwa [Real.log_exp] at hlog
    exact le_trans (by norm_num : (2:ℝ) ≤ 3)
      (paperDensity_bin_lower (by linarith : 0 < p n) (by linarith : 1 < p n) hmpos hm2 hlogu2 ht hε hJpos hlarge_n)
  have hhi : ∀ᶠ n in atTop,
      paperDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
          paperDensityY p ε n := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend,
      hu_tend.eventually_ge_atTop (Real.exp 1)] with n hp ht hu1 hubig
    have hlogu1 : 1 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 1) hubig
      rwa [Real.log_exp] at hlog
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    exact paperDensity_bin_upper (by linarith : 1 < p n) hmpos
      (paperDensityU_mul_le_M p ε n) hlogu1 ht hε hJpos
  have hconc := hmain (u := paperDensityU p ε) (P := paperDensityP p ε)
    (y := paperDensityY p ε) (δ := paperDensityDelta p ε)
    (J := paperDensityJ p ε) (c := (1 / 2 : ℝ)) (cH := (1 / 2 : ℝ)) (ε := ε)
    hu_tend (by norm_num) (by norm_num) hε hPpos hδnonneg hy1 hJδ hJm hlog hlo hhi hguard
  filter_upwards [hconc, eventually_paperDensityU_mul_log_le_paperT h hε,
    h.eventually_sixteen, eventually_paperDensityU_pos h hε,
    eventually_paperDensityU_gt_one_of_tendsto hu_tend,
    eventually_paperT_pos_of_growth h] with n hc hpowle hp hu hu1 ht
  dsimp only at hc
  obtain ⟨a, ha, hdens, _⟩ := hc
  refine ⟨a, ha, ?_⟩
  have hp0 : 0 < p n := by linarith
  have hmposNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hPposn : 0 < paperDensityP p ε n := paperDensityP_pos hp0
  have hPpow := paperDensityP_pow hp0 hmposNat
  have hdens'' : paperDensityP p ε n ^ paperDensityM p ε n *
      Real.exp (-(1 + ε) * paperDensityU p ε n * Real.log (paperDensityU p ε n)) ≤
      ((centeredBinProducts (paperDensityP p ε n)
        (paperDensityDelta p ε n) (paperDensityJ p ε n)
        (paperDensityM p ε n) a).card : ℝ) := by
    change Real.exp (-(1 + ε) * paperDensityU p ε n *
        Real.log (paperDensityU p ε n)) ≤
      ((centeredBinProducts (paperDensityP p ε n)
        (paperDensityDelta p ε n) (paperDensityJ p ε n)
        (paperDensityM p ε n) a).card : ℝ) /
        paperDensityP p ε n ^ paperDensityM p ε n at hdens
    rw [le_div_iff₀ (pow_pos hPposn (paperDensityM p ε n))] at hdens
    rw [mul_comm] at hdens
    exact hdens
  have hexp_le : Real.exp (-paperT p n) ≤
      Real.exp (-(1 + ε) * paperDensityU p ε n *
        Real.log (paperDensityU p ε n)) :=
    Real.exp_le_exp.mpr (by nlinarith [hpowle])
  have hstep : (p n ^ 2 / 4) * Real.exp (-paperT p n) ≤
      ((centeredBinProducts (paperDensityP p ε n)
        (paperDensityDelta p ε n) (paperDensityJ p ε n)
        (paperDensityM p ε n) a).card : ℝ) := by
    rw [← hPpow]
    have hmul : paperDensityP p ε n ^ paperDensityM p ε n *
        Real.exp (-paperT p n) ≤
        paperDensityP p ε n ^ paperDensityM p ε n *
          Real.exp (-(1 + ε) * paperDensityU p ε n *
            Real.log (paperDensityU p ε n)) :=
      mul_le_mul_of_nonneg_left hexp_le (pow_pos hPposn (paperDensityM p ε n)).le
    exact hmul.trans hdens''
  have hα1 : 1 ≤ 1 + ε := by linarith [hε.le]
  have hexp2 : Real.exp (-(1 + ε) * paperT p n) ≤ Real.exp (-paperT p n) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.le, hα1])
  have hp2 : 0 ≤ p n ^ 2 := by positivity
  have hfinal : (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) ≤
      (p n ^ 2 / 4) * Real.exp (-paperT p n) := by
    nlinarith [hexp2, hp2, Real.exp_pos (-(1 + ε) * paperT p n)]
  exact hfinal.trans hstep

/-- The prime-bin count becomes a global odd smooth count once the doubled
strip is below `p^2`. -/
theorem globalOddSmoothCount_lower_of_paperBin
    {p : ℕ → ℝ} {ε : ℝ} {n a : ℕ} {c : ℝ}
    (hp : 16 ≤ p n) (hε : 0 < ε)
    (ht : 0 < paperT p n)
    (hu1 : 1 < paperDensityU p ε n)
    (hJ : 0 < paperDensityJ p ε n)
    (hlogu : 0 < Real.log (paperDensityU p ε n))
    (ha : a ∈ Finset.range (paperDensityM p ε n *
      (paperDensityJ p ε n - 1) + 1))
    (hbin_lower : 3 ≤ paperDensityP p ε n *
      Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))))
    (hbin_upper : paperDensityP p ε n *
      Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
        paperDensityY p ε n)
    (hy2 : 2 ≤ smoothCutoff (paperT p) (paperError ε) n)
    (hcount : c ≤ ((centeredBinProducts (paperDensityP p ε n)
      (paperDensityDelta p ε n) (paperDensityJ p ε n)
      (paperDensityM p ε n) a).card : ℝ)) :
    c ≤ globalOddSmoothCount p (paperT p) (paperError ε) n := by
  have hmNat : 0 < paperDensityM p ε n := paperDensityM_pos hu1
  have hmpos : 0 < (paperDensityM p ε n : ℝ) := by exact_mod_cast hmNat
  have hp0 : 0 < p n := by linarith
  have hPpos : 0 < paperDensityP p ε n := paperDensityP_pos hp0
  have hPpow := paperDensityP_pow hp0 hmNat
  have hmδ : (paperDensityM p ε n : ℝ) * paperDensityDelta p ε n ≤ Real.log 2 :=
    paperDensityDelta_mul_m_le_log2 hε ht hJ hlogu
  have hstrip : paperDensityP p ε n ^ paperDensityM p ε n *
      Real.exp ((paperDensityM p ε n : ℝ) * paperDensityDelta p ε n) ≤
        p n ^ 2 / 2 :=
    paperDensity_strip_upper hp0 hmNat hmδ
  have hδnonneg : 0 ≤ paperDensityDelta p ε n :=
    (paperDensityDelta_pos hε ht hJ hlogu).le
  have hfloor : ∀ j < paperDensityJ p ε n,
      (centeredBinFloor (paperDensityP p ε n) (paperDensityDelta p ε n) a
        (paperDensityM p ε n) (j + 1) : ℝ) ≤
      smoothCutoff (paperT p) (paperError ε) n := by
    intro j hj
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (paperDensityJ p ε n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    have hle_endpoint : centeredBinEndpoint (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) ≤
          paperDensityP p ε n *
            Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) := by
      unfold centeredBinEndpoint
      apply mul_le_mul_of_nonneg_left _ hPpos.le
      apply Real.exp_le_exp.mpr
      have ha_nonneg : 0 ≤ (a : ℝ) / (paperDensityM p ε n : ℝ) := by positivity
      nlinarith [hj1, ha_nonneg, hδnonneg]
    have hfloor_le : ((centeredBinFloor (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) : ℕ) : ℝ) ≤
          centeredBinEndpoint (paperDensityP p ε n)
            (paperDensityDelta p ε n) a (paperDensityM p ε n) (j + 1) :=
      Nat.floor_le (mul_nonneg hPpos.le (Real.exp_pos _).le)
    have hcut : smoothCutoff (paperT p) (paperError ε) n = paperDensityY p ε n :=
      (paperDensityY_eq_smoothCutoff p ε).symm ▸ rfl
    rw [hcut]
    exact hfloor_le.trans (hle_endpoint.trans hbin_upper)
  have hodd : ∀ j < paperDensityJ p ε n,
      3 ≤ centeredBinFloor (paperDensityP p ε n)
        (paperDensityDelta p ε n) a (paperDensityM p ε n) j := by
    intro j hj
    have ha_le : (a : ℝ) / (paperDensityM p ε n : ℝ) ≤
        (paperDensityJ p ε n : ℝ) := by
      have ha1 : a ≤ paperDensityM p ε n * (paperDensityJ p ε n - 1) :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have ha2 : a ≤ paperDensityJ p ε n * paperDensityM p ε n := by
        rw [Nat.mul_comm]
        exact ha1.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      rw [div_le_iff₀ hmpos]
      exact_mod_cast ha2
    have hle_endpoint : paperDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) ≤
          centeredBinEndpoint (paperDensityP p ε n)
            (paperDensityDelta p ε n) a (paperDensityM p ε n) j := by
      unfold centeredBinEndpoint
      apply mul_le_mul_of_nonneg_left _ hPpos.le
      apply Real.exp_le_exp.mpr
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [hj0, ha_le, hδnonneg]
    exact Nat.le_floor (hbin_lower.trans hle_endpoint)
  exact globalOddSmoothCount_lower_of_binCount hPpos.le hmNat hodd hstrip hfloor hy2 hcount

/-- **The paper-regime global odd smooth lower bound** from the prime-bin
density construction. -/
theorem eventually_globalOddSmoothCount_paperLower (line : DirichletLZerosOnLine)
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 / 8) * p n ^ 2 * Real.exp (-(1 + ε) * paperT p n) ≤
        globalOddSmoothCount p (paperT p) (paperError ε) n := by
  have hbin := eventually_paperDensity_binCount line p h hε
  have hu_tend := tendsto_paperDensityU_of_growth h hε
  have ht_tend := tendsto_paperT_of_growth h
  have hlarge : ∀ᶠ n in atTop,
      Real.log 3 + Real.log 4 ≤
        (1 / 2) * ((1 + ε) * paperT p n) *
          (1 - 1 / Real.log (paperDensityU p ε n)) := by
    filter_upwards [ht_tend.eventually_ge_atTop (4 * (Real.log 3 + Real.log 4)),
      hu_tend.eventually_ge_atTop (Real.exp 2)] with n htbig hubig
    have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 2) hubig
      rwa [Real.log_exp] at hlog
    have hinv : 1 / Real.log (paperDensityU p ε n) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogu2
    have hα1 : 1 ≤ 1 + ε := by linarith [hε.le]
    have hpos : 0 < 4 * (Real.log 3 + Real.log 4) := by positivity
    have htpos : 0 < paperT p n := by linarith
    have hαt : 4 * (Real.log 3 + Real.log 4) ≤ (1 + ε) * paperT p n := by
      have htle : paperT p n ≤ (1 + ε) * paperT p n := by nlinarith [hε.le, htpos.le]
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / Real.log (paperDensityU p ε n) := by linarith
    have hnonneg : 0 ≤ (1 / 2) * ((1 + ε) * paperT p n) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hhalf hnonneg, hαt]
  have hlo : ∀ᶠ n in atTop,
      (3 : ℝ) ≤ paperDensityP p ε n *
        Real.exp (-(paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ))) := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend,
      eventually_paperDensityM_le_two_u_of_growth h hε,
      hu_tend.eventually_ge_atTop (Real.exp 2), hlarge] with n hp ht hu1 hm2 hubig hlarge_n
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    have hlogu2 : 2 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 2) hubig
      rwa [Real.log_exp] at hlog
    exact paperDensity_bin_lower (by linarith : 0 < p n) (by linarith : 1 < p n) hmpos hm2 hlogu2 ht hε hJpos hlarge_n
  have hhi : ∀ᶠ n in atTop,
      paperDensityP p ε n *
        Real.exp (paperDensityDelta p ε n * (paperDensityJ p ε n : ℝ)) ≤
          paperDensityY p ε n := by
    filter_upwards [h.eventually_sixteen, eventually_paperT_pos_of_growth h,
      eventually_paperDensityU_gt_one_of_tendsto hu_tend,
      hu_tend.eventually_ge_atTop (Real.exp 1)] with n hp ht hu1 hubig
    have hlogu1 : 1 ≤ Real.log (paperDensityU p ε n) := by
      have hlog := Real.log_le_log (Real.exp_pos 1) hubig
      rwa [Real.log_exp] at hlog
    have hmpos := paperDensityM_pos hu1
    have hJpos := paperDensityJ_pos hmpos
    exact paperDensity_bin_upper (by linarith : 1 < p n) hmpos
      (paperDensityU_mul_le_M p ε n) hlogu1 ht hε hJpos
  have hy2 : ∀ᶠ n in atTop, 2 ≤ smoothCutoff (paperT p) (paperError ε) n := by
    filter_upwards [eventually_paperT_pos_of_growth h,
      (tendsto_paperT_of_growth h).eventually_ge_atTop 1] with n ht ht1
    dsimp [smoothCutoff, paperError]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hαt : (1 : ℝ) ≤ (1 + ε) * paperT p n := by nlinarith [hε.le, ht1]
    nlinarith [Real.log_two_lt_d9]
  filter_upwards [hbin, h.eventually_sixteen, eventually_paperT_pos_of_growth h,
    eventually_paperDensityU_pos h hε, eventually_paperDensityU_gt_one_of_tendsto hu_tend,
    hlo, hhi, hy2] with n hbn hp ht hu hu1 hlo_n hhi_n hy2_n
  obtain ⟨a, ha, hcount⟩ := hbn
  have hmpos := paperDensityM_pos hu1
  have hJpos := paperDensityJ_pos hmpos
  have hlogu := Real.log_pos hu1
  exact globalOddSmoothCount_lower_of_paperBin hp hε ht hu1 hJpos hlogu ha
    hlo_n hhi_n hy2_n hcount

/-- The eventual form of the global odd smooth lower bound. -/
def EventuallyYounisOddGlobalLower (B : ℝ) (p t err : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop,
    B * p n ^ 2 * Real.exp (-(1 + err n) * t n) ≤
      globalOddSmoothCount p t err n

/-- **Eventually `YounisOddGlobalLower` at the paper scale**, with the explicit
constant `1/8` and the fixed paper error `ε > 0`. -/
theorem eventually_younisOddGlobalLower_paper (line : DirichletLZerosOnLine)
    (p : ℕ → ℝ) (h : PaperDensityGrowth p) {ε : ℝ} (hε : 0 < ε) :
    EventuallyYounisOddGlobalLower (1 / 8) p (paperT p) (paperError ε) :=
  eventually_globalOddSmoothCount_paperLower line p h hε

/-- The unconditional paper-regime global lower bound at the witness sequence
`p_n = 4^{n+4}`. -/
theorem eventually_witnessP_younisOddGlobalLower (line : DirichletLZerosOnLine)
    {ε : ℝ} (hε : 0 < ε) :
    EventuallyYounisOddGlobalLower (1 / 8) witnessP (paperT witnessP) (paperError ε) :=
  eventually_younisOddGlobalLower_paper line witnessP witnessP_paperDensityGrowth hε

end

end Cogentic.RandomizedL30SmoothDensity
