import Cogentic.RandomizedL20_2SmoothLower
import Cogentic.RandomizedL20_2SmoothMass

set_option linter.style.haveILetI false

/-!
# L20.2: the paper-regime smooth-number pair

`Cogentic.RandomizedL20_2Saddle` reduces the L20.2 saddle point to the two
explicit analytic inputs

* `SmoothNumberCountLower X y c`:
  `0 < c ∧ ∀ n, exp (c D log D) ≤ #(y-smooth integers in [1, X n])`;
* `SmoothNumberMassLogLower X y α Λ η`:
  `0 < η ∧ ∀ n, η Λ n ≤ log (∑ m^(-α n) over the same smooth set)`,

where `D = paperD n = exp (scale n)` and `D log D = paperD n * scale n`.

The preceding files prove these inputs for two *constructed* pairs: the
powers-of-two endpoint of `RandomizedL20_2SmoothLower` and the self-smooth
(`y = X`) and half-smooth (`y = X/2`) pairs of `RandomizedL20_2SmoothMass`.
The present file supplies the **paper-regime pair** itself.

## The pair

The manuscript uses the smooth-number range with upper endpoint

`X₀ n = exp (max 0 (paperD n * scale n))`

and a smoothness cutoff `y` that is a power of two.  The exact endpoint `X₀`
is smaller than `2` at the pre-asymptotic ledger indices (`n = 3` gives
`paperD n * scale n ≈ 0.263`, hence `X₀ ≈ 1.30`), and there the smooth set has
only one element while `exp (c D log D) > 1` for every `c > 0`.  Consequently no
positive constant `c` can work for the unclipped `X₀` at *every* `n`.

The smallest uniform repair is to floor the exponent at `log 2`, i.e.

`X n = exp (max (log 2) (paperD n * scale n)) = max 2 (X₀ n)`,

and to take `y n = 2 ^ ⌈log₂ (X n)⌉`, the least power of two at least `X n`.
We prove

* `paperSmoothX_ge_two`, `paperSmoothY_ge_two`, `paperSmoothY_ge_X`;
* `paperSmoothSet_eq_self`: since `y ≥ X`, the smooth set is the full interval
  `[1, ⌊X⌋]`, so `paperSmoothCount_eq_floor`;
* `paperSmoothNumberCountLower : SmoothNumberCountLower paperSmoothX
  paperSmoothY (1/2)`, with the honest constant `c = 1/2`;
* `paperSmoothMassLogLower : SmoothNumberMassLogLower paperSmoothX
  paperSmoothY (fun _ => 1/2) (smoothSaddleScale paperSmoothX paperSmoothY)
  (1/2)`, so the same pair also realizes the saddle mean;
* `eventually_paperSmoothLog_eq` and `eventually_paperSmoothX_eq_raw`: on the
  actual paper regime (`D log D ≥ log 2`, which holds eventually because
  `scale → ∞`), the clipped endpoint coincides with the paper endpoint;
* `eventually_rawCountLower` and `eventually_rawMassLogLower`: consequently the
  two target inputs hold eventually for the **unclipped** paper endpoint
  `X₀ n = exp (max 0 (paperD n * scale n))` as well.

Thus the only deviation from the paper pair is the explicit pre-asymptotic
floor `X ≥ 2` (equivalently `D log D ≥ log 2`), and the file records the exact
scale equality `paperSmoothLog n = paperD n * scale n` that removes it.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no count or mass
is set to zero.
-/

namespace Cogentic.RandomizedL20_2PaperSmooth

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_2SmoothMass
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The clipped paper endpoint and the power-of-two cutoff -/

/-- The exponent of the paper-regime endpoint, floored at `log 2` so that the
endpoint is always at least `2`.  On the genuine paper regime this is exactly
`paperD n * scale n = D log D`. -/
def paperSmoothLog (n : ℕ) : ℝ :=
  max (Real.log 2) (paperD n * scale n)

/-- The paper-regime upper endpoint `X n = exp (max (log 2) (D log D))`.  It is
the manuscript endpoint `exp (max 0 (D log D))` as soon as `D log D ≥ log 2`. -/
def paperSmoothX (n : ℕ) : ℝ :=
  Real.exp (paperSmoothLog n)

/-- The unclipped manuscript endpoint `X₀ n = exp (max 0 (D log D))`. -/
def paperSmoothRawX (n : ℕ) : ℝ :=
  Real.exp (max 0 (paperD n * scale n))

/-- The exponent `⌈log₂ (X n)⌉` of the least power of two at least `X n`. -/
def paperSmoothLevel (n : ℕ) : ℕ :=
  ⌈Real.log (paperSmoothX n) / Real.log 2⌉₊

/-- The smoothness cutoff: the least power of two at least `X n`. -/
def paperSmoothY (n : ℕ) : ℝ :=
  (2 : ℝ) ^ paperSmoothLevel n

/-- The exponent is at least `log 2`. -/
theorem paperSmoothLog_ge_log_two (n : ℕ) :
    Real.log 2 ≤ paperSmoothLog n :=
  le_max_left _ _

/-- The clipped paper endpoint is at least two. -/
theorem paperSmoothX_ge_two (n : ℕ) : 2 ≤ paperSmoothX n := by
  calc
    (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (paperSmoothLog n) :=
        Real.exp_le_exp.mpr (paperSmoothLog_ge_log_two n)
    _ = paperSmoothX n := rfl

/-- The clipped paper endpoint is positive. -/
theorem paperSmoothX_pos (n : ℕ) : 0 < paperSmoothX n :=
  Real.exp_pos _

/-- The clipped paper endpoint is at least one. -/
theorem paperSmoothX_ge_one (n : ℕ) : 1 ≤ paperSmoothX n :=
  le_trans (by norm_num) (paperSmoothX_ge_two n)

/-- The power-of-two level is at least one. -/
theorem paperSmoothLevel_ge_one (n : ℕ) : 1 ≤ paperSmoothLevel n := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX2 : 2 ≤ paperSmoothX n := paperSmoothX_ge_two n
  have hlog : Real.log 2 ≤ Real.log (paperSmoothX n) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2
    simpa using h
  have hratio : 1 ≤ Real.log (paperSmoothX n) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hceil : (1 : ℝ) ≤ (paperSmoothLevel n : ℝ) :=
    hratio.trans (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The cutoff is at least two. -/
theorem paperSmoothY_ge_two (n : ℕ) : 2 ≤ paperSmoothY n := by
  have hpow : (2 : ℕ) ≤ 2 ^ paperSmoothLevel n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (paperSmoothLevel_ge_one n)
  have hpowR : (2 : ℝ) ≤ (2 : ℝ) ^ paperSmoothLevel n := by
    exact_mod_cast hpow
  simpa [paperSmoothY] using hpowR

/-- **The cutoff dominates the endpoint.**  This is the defining property of
the least power of two at least `X n`. -/
theorem paperSmoothY_ge_X (n : ℕ) : paperSmoothX n ≤ paperSmoothY n := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : Real.log (paperSmoothX n) / Real.log 2 ≤
      (paperSmoothLevel n : ℝ) :=
    Nat.le_ceil _
  have hmul : Real.log (paperSmoothX n) ≤
      (paperSmoothLevel n : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2pos] at hratio
    linarith
  calc
    paperSmoothX n = Real.exp (Real.log (paperSmoothX n)) :=
      (Real.exp_log (paperSmoothX_pos n)).symm
    _ ≤ Real.exp ((paperSmoothLevel n : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hmul
    _ = (2 : ℝ) ^ paperSmoothLevel n := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
    _ = paperSmoothY n := rfl

/-! ## 2. The smooth set is the whole interval -/

/-- If the smoothness cutoff is at least the endpoint, the smooth set is the
full initial interval. -/
theorem smoothNumberSet_eq_self_of_le {X y : ℕ → ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hXy : X n ≤ y n) :
    smoothNumberSet X y n = smoothNumberSet X X n := by
  ext m
  rw [smoothNumberSet, smoothNumberSet, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hm, _⟩
    refine ⟨hm, ?_⟩
    intro p hp
    obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := by omega
    have hp_le_m : p ≤ m :=
      Nat.le_of_dvd hmpos (Nat.dvd_of_mem_primeFactors hp)
    have hm_le_X : (m : ℝ) ≤ X n :=
      (Nat.cast_le.mpr hmX).trans (Nat.floor_le (by linarith))
    exact (Nat.cast_le.mpr hp_le_m).trans hm_le_X
  · rintro ⟨hm, hs⟩
    exact ⟨hm, fun p hp => (hs p hp).trans hXy⟩

/-- For the paper pair the smooth set is `[1, ⌊X⌋]`. -/
theorem paperSmoothSet_eq_self (n : ℕ) :
    smoothNumberSet paperSmoothX paperSmoothY n =
      smoothNumberSet paperSmoothX paperSmoothX n :=
  smoothNumberSet_eq_self_of_le (paperSmoothX_ge_one n) (paperSmoothY_ge_X n)

/-- The smooth-number count of the paper pair is the full floor. -/
theorem paperSmoothCount_eq_floor (n : ℕ) :
    smoothNumberCount paperSmoothX paperSmoothY n =
      (⌊paperSmoothX n⌋₊ : ℝ) := by
  unfold smoothNumberCount
  rw [paperSmoothSet_eq_self n]
  exact smoothNumberCount_self (paperSmoothX_ge_one n)

/-! ## 3. The count lower bound -/

/-- The explicit floor estimate behind the paper count bound. -/
theorem exp_half_mul_le_paperSmoothFloor (n : ℕ) :
    Real.exp ((1 / 2 : ℝ) * paperD n * scale n) ≤
      (⌊paperSmoothX n⌋₊ : ℝ) := by
  set L : ℝ := paperD n * scale n with hL
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1 / 2 : ℝ) * paperD n * scale n = L / 2 := by
    calc
      (1 / 2 : ℝ) * paperD n * scale n
          = (1 / 2 : ℝ) * (paperD n * scale n) := by ring
      _ = (1 / 2 : ℝ) * L := by rw [← hL]
      _ = L / 2 := by ring
  by_cases hsmall : L ≤ Real.log 2
  · have hsmall' : paperD n * scale n ≤ Real.log 2 := by
      simpa [hL] using hsmall
    have hmax : paperSmoothLog n = Real.log 2 := by
      unfold paperSmoothLog
      rw [max_eq_left hsmall']
    have hX : paperSmoothX n = 2 := by
      unfold paperSmoothX
      rw [hmax, Real.exp_log (by norm_num)]
    have hle : L / 2 ≤ Real.log 2 := by nlinarith
    have hexp : Real.exp (L / 2) ≤ 2 := by
      calc
        Real.exp (L / 2) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr hle
        _ = 2 := Real.exp_log (by norm_num)
    rw [hhalf, hX]
    simpa using hexp
  · have hlarge : Real.log 2 ≤ L := le_of_not_ge hsmall
    have hlarge' : Real.log 2 ≤ paperD n * scale n := by
      simpa [hL] using hlarge
    have hmax : paperSmoothLog n = L := by
      unfold paperSmoothLog
      rw [max_eq_right hlarge']
    have hX : paperSmoothX n = Real.exp L := by
      unfold paperSmoothX
      rw [hmax]
    have hX2 : (2 : ℝ) ≤ paperSmoothX n := paperSmoothX_ge_two n
    have hN2 : (2 : ℝ) ≤ (⌊paperSmoothX n⌋₊ : ℝ) := by
      have hN : 2 ≤ ⌊paperSmoothX n⌋₊ :=
        Nat.le_floor (by exact_mod_cast hX2)
      exact_mod_cast hN
    have hNlow : Real.exp L - 1 ≤ (⌊paperSmoothX n⌋₊ : ℝ) := by
      rw [hX]
      have h := Nat.lt_floor_add_one (Real.exp L)
      linarith
    have htsq : Real.exp (L / 2) ^ 2 = Real.exp L := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have htN : Real.exp (L / 2) ≤ (⌊paperSmoothX n⌋₊ : ℝ) := by
      by_cases ht : Real.exp (L / 2) ≤ Real.exp L - 1
      · exact ht.trans hNlow
      · have ht' : Real.exp L - 1 < Real.exp (L / 2) := not_le.mp ht
        have htlt : Real.exp (L / 2) < 2 := by
          by_contra hge
          rw [not_lt] at hge
          nlinarith [ht', htsq, hge]
        linarith
    rw [hhalf]
    exact htN

/-- **The paper pair satisfies the smooth-number count lower bound** with the
honest constant `c = 1/2`. -/
theorem paperSmoothNumberCount_lower (n : ℕ) :
    Real.exp ((1 / 2 : ℝ) * paperD n * scale n) ≤
      smoothNumberCount paperSmoothX paperSmoothY n := by
  rw [paperSmoothCount_eq_floor n]
  exact exp_half_mul_le_paperSmoothFloor n

/-- **`SmoothNumberCountLower` for the paper pair.** -/
theorem paperSmoothNumberCountLower :
    SmoothNumberCountLower paperSmoothX paperSmoothY (1 / 2) :=
  ⟨by norm_num, paperSmoothNumberCount_lower⟩

/-! ## 4. The smooth reciprocal mass -/

/-- The reciprocal mass of the paper pair is the full-interval mass, because
the cutoff covers the whole endpoint. -/
theorem paperSmoothMass_eq_self (n : ℕ) :
    smoothNumberMass paperSmoothX paperSmoothY (fun _ => (1 / 2 : ℝ)) n =
      smoothNumberMass paperSmoothX paperSmoothX (fun _ => (1 / 2 : ℝ)) n := by
  unfold smoothNumberMass
  rw [paperSmoothSet_eq_self n]

/-- **`SmoothNumberMassLogLower` for the paper pair**, with `α = η = 1/2`.
The mass is bounded below by `√⌊X⌋`, and the saddle scale is
`log #smooth = log ⌊X⌋`. -/
theorem paperSmoothMassLogLower :
    SmoothNumberMassLogLower paperSmoothX paperSmoothY (fun _ => (1 / 2 : ℝ))
      (smoothSaddleScale paperSmoothX paperSmoothY) (1 / 2) := by
  refine ⟨by norm_num, fun n => ?_⟩
  set N : ℕ := ⌊paperSmoothX n⌋₊ with hN
  have hX1 : 1 ≤ paperSmoothX n := paperSmoothX_ge_one n
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.le_floor (by exact_mod_cast hX1)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hmass_ge : Real.sqrt (N : ℝ) ≤
      smoothNumberMass paperSmoothX paperSmoothY (fun _ => (1 / 2 : ℝ)) n := by
    rw [paperSmoothMass_eq_self n, hN]
    exact smoothNumberMass_self_ge_sqrt (X := paperSmoothX) (n := n) hX1
  have hcount : smoothNumberCount paperSmoothX paperSmoothY n = (N : ℝ) := by
    rw [paperSmoothCount_eq_floor n, hN]
  have hΛ : smoothSaddleScale paperSmoothX paperSmoothY n = Real.log (N : ℝ) := by
    unfold smoothSaddleScale
    rw [hcount]
  rw [hΛ]
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hmass_ge
  rw [Real.log_sqrt hNpos.le] at hlog
  nlinarith [hlog]

/-- The paper pair realizes the L20.2 saddle scale. -/
theorem paperSmoothSaddleScaleLower :
    SaddlePointScaleLower (smoothSaddleScale paperSmoothX paperSmoothY) (1 / 2) :=
  saddlePointScaleLower_of_smoothNumberCountLower paperSmoothNumberCountLower

/-- The paper pair realizes the L20.2 saddle mean. -/
theorem paperSmoothSaddleMeanLower :
    SaddlePointMeanLower
      (smoothNumberMass paperSmoothX paperSmoothY (fun _ => (1 / 2 : ℝ)))
      (smoothSaddleScale paperSmoothX paperSmoothY) (1 / 2) :=
  saddlePointMeanLower_of_smoothNumberMassLogLower paperSmoothX_ge_one
    paperSmoothMassLogLower

/-! ## 5. Identification with the unclipped paper endpoint -/

/-- On the genuine paper regime the clipped exponent is exactly
`paperD n * scale n = D log D`; this is the scale equality left by the
pre-asymptotic floor. -/
theorem eventually_paperSmoothLog_eq :
    ∀ᶠ n : ℕ in atTop, paperSmoothLog n = paperD n * scale n := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ scale n :=
    scale_grows.eventually_ge_atTop (Real.log 2)
  filter_upwards [hscale] with n hn
  have hD1 : 1 ≤ paperD n := by
    unfold paperD
    exact Real.one_le_exp (le_trans hlog2pos.le hn)
  have hprod : Real.log 2 ≤ paperD n * scale n := by
    calc
      Real.log 2 ≤ scale n := hn
      _ = 1 * scale n := (one_mul _).symm
      _ ≤ paperD n * scale n :=
          mul_le_mul_of_nonneg_right hD1 (le_trans hlog2pos.le hn)
  unfold paperSmoothLog
  exact max_eq_right hprod

/-- Eventually the clipped paper endpoint is the unclipped manuscript
endpoint. -/
theorem eventually_paperSmoothX_eq_raw :
    ∀ᶠ n : ℕ in atTop, paperSmoothX n = paperSmoothRawX n := by
  filter_upwards [eventually_paperSmoothLog_eq] with n hn
  have hnonneg : 0 ≤ paperD n * scale n := by
    have h := paperSmoothLog_ge_log_two n
    rw [hn] at h
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans h
  unfold paperSmoothX paperSmoothRawX
  rw [hn, max_eq_right hnonneg]

/-- Pointwise congruence of the smooth-number set in the upper endpoint. -/
theorem smoothNumberSet_congr_X {X X' y : ℕ → ℝ} {n : ℕ}
    (h : X n = X' n) :
    smoothNumberSet X y n = smoothNumberSet X' y n := by
  unfold smoothNumberSet
  rw [h]

/-- Pointwise congruence of the smooth-number count in the upper endpoint. -/
theorem smoothNumberCount_congr_X {X X' y : ℕ → ℝ} {n : ℕ}
    (h : X n = X' n) :
    smoothNumberCount X y n = smoothNumberCount X' y n := by
  unfold smoothNumberCount
  rw [smoothNumberSet_congr_X h]

/-- Pointwise congruence of the smooth reciprocal mass in the upper endpoint. -/
theorem smoothNumberMass_congr_X {X X' y α : ℕ → ℝ} {n : ℕ}
    (h : X n = X' n) :
    smoothNumberMass X y α n = smoothNumberMass X' y α n := by
  unfold smoothNumberMass
  rw [smoothNumberSet_congr_X h]

/-- Pointwise congruence of the saddle scale in the upper endpoint. -/
theorem smoothSaddleScale_congr_X {X X' y : ℕ → ℝ} {n : ℕ}
    (h : X n = X' n) :
    smoothSaddleScale X y n = smoothSaddleScale X' y n := by
  unfold smoothSaddleScale
  rw [smoothNumberCount_congr_X h]

/-- **The unclipped paper endpoint satisfies the count bound eventually.** -/
theorem eventually_rawCountLower :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((1 / 2 : ℝ) * paperD n * scale n) ≤
        smoothNumberCount paperSmoothRawX paperSmoothY n := by
  filter_upwards [eventually_paperSmoothX_eq_raw] with n hn
  have hcount : smoothNumberCount paperSmoothRawX paperSmoothY n =
      smoothNumberCount paperSmoothX paperSmoothY n :=
    smoothNumberCount_congr_X (X := paperSmoothRawX) (X' := paperSmoothX)
      (y := paperSmoothY) (n := n) hn.symm
  rw [hcount]
  exact paperSmoothNumberCount_lower n

/-- **The unclipped paper endpoint satisfies the mass bound eventually.** -/
theorem eventually_rawMassLogLower :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * smoothSaddleScale paperSmoothRawX paperSmoothY n ≤
        Real.log (smoothNumberMass paperSmoothRawX paperSmoothY
          (fun _ => (1 / 2 : ℝ)) n) := by
  filter_upwards [eventually_paperSmoothX_eq_raw] with n hn
  have hΛ : smoothSaddleScale paperSmoothRawX paperSmoothY n =
      smoothSaddleScale paperSmoothX paperSmoothY n :=
    smoothSaddleScale_congr_X (X := paperSmoothRawX) (X' := paperSmoothX)
      (y := paperSmoothY) (n := n) hn.symm
  have hμ : smoothNumberMass paperSmoothRawX paperSmoothY
      (fun _ => (1 / 2 : ℝ)) n =
      smoothNumberMass paperSmoothX paperSmoothY
        (fun _ => (1 / 2 : ℝ)) n :=
    smoothNumberMass_congr_X (X := paperSmoothRawX) (X' := paperSmoothX)
      (y := paperSmoothY) (α := fun _ => (1 / 2 : ℝ)) (n := n) hn.symm
  rw [hΛ, hμ]
  exact paperSmoothMassLogLower.2 n

/-! ## Axiom audit -/

#print axioms paperSmoothLog_ge_log_two
#print axioms paperSmoothX_ge_two
#print axioms paperSmoothLevel_ge_one
#print axioms paperSmoothY_ge_two
#print axioms paperSmoothY_ge_X
#print axioms smoothNumberSet_eq_self_of_le
#print axioms paperSmoothSet_eq_self
#print axioms paperSmoothCount_eq_floor
#print axioms exp_half_mul_le_paperSmoothFloor
#print axioms paperSmoothNumberCount_lower
#print axioms paperSmoothNumberCountLower
#print axioms paperSmoothMass_eq_self
#print axioms paperSmoothMassLogLower
#print axioms paperSmoothSaddleScaleLower
#print axioms paperSmoothSaddleMeanLower
#print axioms smoothNumberSet_congr_X
#print axioms smoothNumberCount_congr_X
#print axioms smoothNumberMass_congr_X
#print axioms smoothSaddleScale_congr_X
#print axioms eventually_paperSmoothLog_eq
#print axioms eventually_paperSmoothX_eq_raw
#print axioms eventually_rawCountLower
#print axioms eventually_rawMassLogLower

end

end Cogentic.RandomizedL20_2PaperSmooth
