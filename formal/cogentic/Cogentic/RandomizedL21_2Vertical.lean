import Cogentic.RandomizedL21_2Shift
import Cogentic.RandomizedProductPerron

set_option linter.style.haveILetI false

/-!
# L21.2: the vertical-strip zeta sum behind `VerticalShiftBound`

`Cogentic.RandomizedL21_2Shift` reduces the truncated Perron shift of L21.2 to
the single vertical estimate

```
VerticalShiftBound X c Kper Cper :
  ∀ᶠ n, ∀ v t, 2 ≤ v → v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
    ‖twistedPrimeSum v t - twistedMain v t‖ ≤ Kper n * v ^ (2 / 3) * U ^ C.
```

The horizontal segments at height `X^3` and the prime-power removal have already
been absorbed into the vertical term by `shiftError_le_three_vertical`.  What
remains is the contour at `Re s = perronRe = 2/3`.

This file names that contour explicitly.  With the Perron change of variables
`s = perronRe + i τ`, the vertical piece is

```
verticalZetaSum v t T =
  (1 / (2π)) ∫_{τ = -T}^{T} (-ζ'/ζ) (2/3 + i (τ + t)) · v^{2/3 + iτ} / (2/3 + iτ) dτ,
```

i.e. the interval integral of the logarithmic derivative of the Riemann zeta
function along the line `Re s = 2/3`, truncated at height `T = X^3`.  We prove

1. `norm_verticalZetaSum_le`: a uniform line bound
   `‖ζ'/ζ (2/3 + i u)‖ ≤ M` on `|u| ≤ 2 X^3` gives the explicit contour bound
   `‖verticalZetaSum v t X^3‖ ≤ (M v^{2/3} / π) (1 + log (X^3 / (2/3)))`.
   The proof is the same `L¹` estimate as the repository's
   `Cogentic.product_perron_vertical_l1` (the truncated Perron kernel bound), so
   no new analytic input is used beyond the line bound itself.
2. `verticalZetaStripBound_of_lineBound`: the resulting
   `VerticalZetaStripBound`, with the explicit Perron factor
   `Kper n = (K n / π) (1 + log (X^3 / (2/3)))`.
3. `verticalShiftBound_of_zetaStrip`: the strip bound plus the Perron remainder
   (the horizontal segments and the prime-power removal, bounded by
   `shiftHorizontal + shiftPrimePower`) imply `VerticalShiftBound` with constant
   `3 Kper`, using `shiftError_le_three_vertical`.
4. `verticalShiftBound_of_lineBound`: the headline reduction, from the uniform
   line bound on `ζ'/ζ` at `Re s = 2/3` directly to `VerticalShiftBound`.
5. `perronShift_of_lineBound`: the same reduction composed with
   `perronShift_of_vertical`, giving the full three-term Perron shift.

The remaining hypotheses are exactly the paper's two zeta-side inputs: the
uniform bound for `ζ'/ζ` on the vertical strip, and the Perron contour-shift
identity with its horizontal/prime-power remainder.  No `sorry`, `admit`,
`axiom` or `native_decide` is used, and no bound is replaced by zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Vertical

open Filter Real MeasureTheory
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift

/-! ## The vertical-strip zeta contour -/

/-- The integrand of the vertical Perron contour at `Re s = 2/3`:
`(-ζ'/ζ) (2/3 + i(τ+t)) · v^{2/3+iτ} / (2/3+iτ)`. -/
def stripIntegrand (v t : ℝ) (τ : ℝ) : ℂ :=
  (- logDeriv riemannZeta (perronLine perronRe (τ + t))) *
    ((v : ℂ) ^ perronLine perronRe τ / perronLine perronRe τ)

/-- The truncated vertical-strip zeta sum at `Re s = 2/3`, height `T`. -/
def verticalZetaSum (v t T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ τ in (-T)..T, stripIntegrand v t τ

/-- **The explicit vertical-strip zeta bound.**  This is the contour at
`Re s = 2/3`, truncated at height `X^3`, bounded by the paper's vertical error
`O (v^{2/3} U^C)`. -/
def VerticalZetaStripBound (X : ℕ → ℝ) (c : ℝ) (Kper : ℕ → ℝ) (Cper : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖verticalZetaSum v t (X n ^ 3)‖ ≤
        shiftVertical (Kper n) (bandLog X n) Cper v

/-- **The Perron contour-shift remainder.**  Subtracting the vertical strip
from `twistedPrimeSum - twistedMain` leaves exactly the two horizontal segments
at height `X^3` and the prime-power removal.  This is the paper's contour-shift
identity with the reference line `Re s = 1 + 1/log v`; the horizontal and
prime-power terms are already absorbed by `shiftError_le_three_vertical`. -/
def PerronShiftRemainder (X : ℕ → ℝ) (c : ℝ) (Kper : ℕ → ℝ) (Cper : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖(twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3)‖ ≤
        shiftHorizontal (Kper n) (bandLog X n) Cper (X n) v + shiftPrimePower (Kper n) v

/-- **The uniform line bound for `ζ'/ζ` at `Re s = 2/3`.**  This is the
smallest explicit vertical-strip zeta input: a bound `O (U^C)` for the
logarithmic derivative of the Riemann zeta function on the segment
`Re s = 2/3`, `|Im s| ≤ 2 X^3`. -/
def VerticalLineBound (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ 2 * X n ^ 3 →
    ‖logDeriv riemannZeta (perronLine perronRe u)‖ ≤ K n * (bandLog X n) ^ C

/-! ## The contour bound from the line bound -/

/-- **The vertical contour costs one logarithm of the height.**  A uniform bound
`M` for `ζ'/ζ` on the segment gives
`‖verticalZetaSum v t T‖ ≤ (M v^{2/3} / π) (1 + log (T / (2/3)))` for `T ≥ 2/3`.

This is the `L¹` estimate of `Cogentic.product_perron_vertical_l1`, applied to
the single log-derivative factor; the factor `v^{iτ}` has modulus one and
`v^{2/3}` is pulled out. -/
theorem norm_verticalZetaSum_le {v t T M : ℝ}
    (hv : 0 < v) (hT : perronRe ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ τ ∈ Set.Icc (-T) T,
      ‖logDeriv riemannZeta (perronLine perronRe (τ + t))‖ ≤ M) :
    ‖verticalZetaSum v t T‖ ≤
      (M * v ^ perronRe / Real.pi) * (1 + Real.log (T / perronRe)) := by
  have hσ : 0 < perronRe := by norm_num [perronRe]
  have hTnn : 0 ≤ T := le_trans hσ.le hT
  have hcontInv : Continuous fun τ : ℝ => (perronLine perronRe τ)⁻¹ := by
    apply Continuous.inv₀ (by unfold perronLine; fun_prop)
    intro τ h
    have hre := congrArg Complex.re h
    simp [perronLine, perronRe] at hre
  have hg : IntervalIntegrable
      (fun τ : ℝ => M * v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖) volume (-T) T :=
    (continuous_const.mul hcontInv.norm).intervalIntegrable _ _
  have hpt : ∀ᵐ τ ∂volume, τ ∈ Set.Ioc (-T) T →
      ‖stripIntegrand v t τ‖ ≤ M * v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖ := by
    refine Filter.Eventually.of_forall ?_
    intro τ hτ
    have hτ' : τ ∈ Set.Icc (-T) T := Set.Ioc_subset_Icc_self hτ
    have hz := hbound τ hτ'
    calc
      ‖stripIntegrand v t τ‖
          = ‖logDeriv riemannZeta (perronLine perronRe (τ + t))‖ *
              (v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖) := by
            unfold stripIntegrand
            rw [norm_mul, norm_neg, norm_div, norm_inv,
              Complex.norm_cpow_eq_rpow_re_of_pos hv, div_eq_mul_inv]
            simp [perronLine]
      _ ≤ M * (v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖) :=
            mul_le_mul_of_nonneg_right hz (by positivity)
      _ = M * v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖ := by ring
  have hint : ‖∫ τ in (-T)..T, stripIntegrand v t τ‖ ≤
      ∫ τ in (-T)..T, M * v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖ :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith) hpt hg
  have hbase := product_perron_vertical_l1 hσ hT
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold verticalZetaSum
  rw [norm_mul, hnorm]
  calc
    (1 / (2 * Real.pi)) * ‖∫ τ in (-T)..T, stripIntegrand v t τ‖
        ≤ (1 / (2 * Real.pi)) *
            ∫ τ in (-T)..T, M * v ^ perronRe * ‖(perronLine perronRe τ)⁻¹‖ := by
          gcongr
    _ = (1 / (2 * Real.pi)) * (M * v ^ perronRe) *
          ∫ τ in (-T)..T, ‖(perronLine perronRe τ)⁻¹‖ := by
          rw [intervalIntegral.integral_const_mul]
          ring
    _ ≤ (1 / (2 * Real.pi)) * (M * v ^ perronRe) *
          (2 * (1 + Real.log (T / perronRe))) := by
          gcongr
    _ = (M * v ^ perronRe / Real.pi) * (1 + Real.log (T / perronRe)) := by ring

/-- The explicit line bound on `ζ'/ζ` implies the vertical-strip zeta bound,
with the Perron factor `(1 + log (X^3 / (2/3))) / π` made explicit. -/
theorem verticalZetaStripBound_of_lineBound {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (hK : ∀ n, 0 ≤ K n)
    (hL : VerticalLineBound X K C) :
    VerticalZetaStripBound X c
      (fun n => (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) C := by
  filter_upwards [hL] with n hn
  intro v t hv _hvB ht
  have hσ1 : perronRe < 1 := by norm_num [perronRe]
  have hX3 : (1 : ℝ) ≤ X n ^ 3 := by
    simpa using one_le_pow₀ (hX n).le (n := 3)
  have hT : perronRe ≤ X n ^ 3 := by linarith
  have hbound : ∀ τ ∈ Set.Icc (-(X n ^ 3)) (X n ^ 3),
      ‖logDeriv riemannZeta (perronLine perronRe (τ + t))‖ ≤
        K n * (bandLog X n) ^ C := by
    intro τ hτ
    apply hn (τ + t)
    have ht' := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith [ht'.1, ht'.2, hτ.1, hτ.2, hX3]
  have h := norm_verticalZetaSum_le (v := v) (t := t) (T := X n ^ 3)
    (M := K n * (bandLog X n) ^ C) (by linarith) hT
    (mul_nonneg (hK n) (Real.rpow_nonneg (Real.log_pos (hX n)).le C))
    hbound
  refine h.trans (le_of_eq ?_)
  unfold shiftVertical
  rw [perronRe]
  ring

/-! ## From the strip bound to `VerticalShiftBound` -/

/-- **The vertical strip plus the Perron remainder give `VerticalShiftBound`.**
The remainder is bounded by `shiftHorizontal + shiftPrimePower`, and the existing
absorption `shiftError_le_three_vertical` turns the three displayed errors into
three times the vertical one. -/
theorem verticalShiftBound_of_zetaStrip {X : ℕ → ℝ} {c : ℝ} {Kper : ℕ → ℝ} {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hK : ∀ n, 0 ≤ Kper n)
    (hU : ∀ n, 3 ≤ bandLog X n) (hC : 2 ≤ Cper)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      smoothCutoff c X n ≤ Real.exp (bandLog X n / 3))
    (hZ : VerticalZetaStripBound X c Kper Cper)
    (hR : PerronShiftRemainder X c Kper Cper) :
    VerticalShiftBound X c (fun n => 3 * Kper n) Cper := by
  filter_upwards [hZ, hR, hsmall] with n hZn hRn hsn
  intro v t hv hvB ht
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have hv0 : 0 ≤ v := by linarith
  have hvExp : v ≤ Real.exp (bandLog X n / 3) := hvB.trans hsn
  have hv13 : v ^ (1 / 3 : ℝ) ≤ X n ^ 3 :=
    rpow_one_third_le_height (hX n) rfl (hU n) hv0 hvExp
  have hsplit : twistedPrimeSum v t - twistedMain v t =
      verticalZetaSum v t (X n ^ 3) +
        ((twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3)) := by
    ring
  have htri : ‖twistedPrimeSum v t - twistedMain v t‖ ≤
      shiftError (Kper n) (bandLog X n) Cper (X n) v := by
    rw [hsplit]
    calc
      ‖verticalZetaSum v t (X n ^ 3) +
          ((twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3))‖
          ≤ ‖verticalZetaSum v t (X n ^ 3)‖ +
              ‖(twistedPrimeSum v t - twistedMain v t) -
                verticalZetaSum v t (X n ^ 3)‖ := norm_add_le _ _
      _ ≤ shiftVertical (Kper n) (bandLog X n) Cper v +
            (shiftHorizontal (Kper n) (bandLog X n) Cper (X n) v +
              shiftPrimePower (Kper n) v) :=
            add_le_add (hZn v t hv hvB ht) (hRn v t hv hvB ht)
      _ = shiftError (Kper n) (bandLog X n) Cper (X n) v := by
            unfold shiftError
            ring
  have h3 := shiftError_le_three_vertical (K := Kper n) (U := bandLog X n)
    (C := Cper) (X := X n) (v := v) (hK n) (hU n) hC hv hXpos hv13 hvExp
  refine htri.trans ?_
  calc
    shiftError (Kper n) (bandLog X n) Cper (X n) v
        ≤ 3 * shiftVertical (Kper n) (bandLog X n) Cper v := h3
    _ = shiftVertical (3 * Kper n) (bandLog X n) Cper v := by
          unfold shiftVertical
          ring

/-! ## The Perron range and the `U/3` cutoff

The absorption `shiftError_le_three_vertical` needs `v ≤ exp (U/3)`, while the
Perron range only gives `v ≤ exp (c T_X)`.  Since `T_X = sqrt (U log U) ≪ U`,
this inclusion is automatic once `U` is large; we record the elementary bound
here so the headline reduction does not have to carry it as a hypothesis. -/

/-- `log U ≤ U/9` for `U ≥ 324`. -/
theorem log_le_div_nine {U : ℝ} (hU : 324 ≤ U) : Real.log U ≤ U / 9 := by
  have hU0 : 0 < U := by linarith
  have hlog := Real.log_le_rpow_div hU0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hsqrt : Real.sqrt U ≤ U / 18 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (U - 324)]
  calc
    Real.log U ≤ U ^ (1 / 2 : ℝ) / (1 / 2) := hlog
    _ = 2 * Real.sqrt U := by rw [Real.sqrt_eq_rpow]; ring
    _ ≤ 2 * (U / 18) := by linarith
    _ = U / 9 := by ring

/-- `T_X = sqrt (U log U) ≤ U/3` for `U ≥ 324`. -/
theorem paperRate_le_third {U : ℝ} (hU : 324 ≤ U) :
    Real.sqrt (U * Real.log U) ≤ U / 3 := by
  have hU0 : 0 < U := by linarith
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  rw [Real.sqrt_le_left (by linarith)]
  calc
    U * Real.log U ≤ U * (U / 9) :=
      mul_le_mul_of_nonneg_left (log_le_div_nine hU) hU0.le
    _ = (U / 3) ^ 2 := by ring

/-- In the large-`U` Perron range the smoothness cutoff lies below
`exp (U/3)`, where the prime-power term is absorbed. -/
theorem smoothCutoff_le_exp_third {X : ℕ → ℝ} {c : ℝ} {n : ℕ}
    (_hc0 : 0 < c) (hc1 : c ≤ 1) (hU : 324 ≤ bandLog X n) :
    smoothCutoff c X n ≤ Real.exp (bandLog X n / 3) := by
  unfold smoothCutoff logCutoff paperRate
  apply Real.exp_le_exp.mpr
  have h := paperRate_le_third hU
  have hsqrt : 0 ≤ Real.sqrt (bandLog X n * Real.log (bandLog X n)) :=
    Real.sqrt_nonneg _
  calc
    c * Real.sqrt (bandLog X n * Real.log (bandLog X n))
        ≤ 1 * Real.sqrt (bandLog X n * Real.log (bandLog X n)) :=
          mul_le_mul_of_nonneg_right hc1 hsqrt
    _ = Real.sqrt (bandLog X n * Real.log (bandLog X n)) := by ring
    _ ≤ bandLog X n / 3 := h

/-! ## The headline reductions -/

/-- **`VerticalShiftBound` from the vertical-strip zeta line bound.**  This is
the smallest explicit zeta-side input of L21.2: a uniform `O (U^C)` bound for
`ζ'/ζ` on `Re s = 2/3`, together with the already-absorbed Perron remainder. -/
theorem verticalShiftBound_of_lineBound {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hK : ∀ n, 0 ≤ K n)
    (hU : ∀ n, 3 ≤ bandLog X n) (hC : 2 ≤ Cper)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      smoothCutoff c X n ≤ Real.exp (bandLog X n / 3))
    (hL : VerticalLineBound X K Cper)
    (hR : PerronShiftRemainder X c
      (fun n => (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) Cper) :
    VerticalShiftBound X c
      (fun n => 3 * ((K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) Cper := by
  have hKper : ∀ n, 0 ≤ (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)) := by
    intro n
    have hlog : 0 ≤ Real.log (X n ^ 3 / perronRe) := by
      apply Real.log_nonneg
      rw [one_le_div (by norm_num [perronRe] : (0 : ℝ) < perronRe)]
      calc
        perronRe ≤ 1 := by norm_num [perronRe]
        _ ≤ X n ^ 3 := by simpa using one_le_pow₀ (hX n).le (n := 3)
    exact mul_nonneg (div_nonneg (hK n) Real.pi_pos.le) (by linarith)
  exact verticalShiftBound_of_zetaStrip hX hKper hU hC hsmall
    (verticalZetaStripBound_of_lineBound hX hK hL) hR

/-- **The headline reduction with the `exp (U/3)` range discharged.**  Once
`log X ≥ 324` the smoothness cutoff `exp (c T_X)` lies below `exp (U/3)`, so the
only Perron-range hypothesis left is `log X ≥ 3`. -/
theorem verticalShiftBound_of_lineBound_of_log_ge {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hc0 : 0 < c) (hc1 : c ≤ 1) (hK : ∀ n, 0 ≤ K n)
    (hU : ∀ n, 3 ≤ bandLog X n) (hC : 2 ≤ Cper)
    (hlog : ∀ᶠ n : ℕ in atTop, 324 ≤ bandLog X n)
    (hL : VerticalLineBound X K Cper)
    (hR : PerronShiftRemainder X c
      (fun n => (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) Cper) :
    VerticalShiftBound X c
      (fun n => 3 * ((K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) Cper :=
  verticalShiftBound_of_lineBound hX hK hU hC
    (hlog.mono fun _ hn => smoothCutoff_le_exp_third hc0 hc1 hn) hL hR

/-- **The full three-term Perron shift from the vertical-strip zeta bound.**
Composing with `perronShift_of_vertical` removes the need for any separate
`VerticalShiftBound`; the three-term error follows from the strip bound with the
same explicit constant. -/
theorem perronShift_of_lineBound {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hK : ∀ n, 0 ≤ K n)
    (hU : ∀ n, 3 ≤ bandLog X n) (hC : 2 ≤ Cper)
    (hsmall : ∀ᶠ n : ℕ in atTop,
      smoothCutoff c X n ≤ Real.exp (bandLog X n / 3))
    (hL : VerticalLineBound X K Cper)
    (hR : PerronShiftRemainder X c
      (fun n => (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) Cper) :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          (3 * ((K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
              + v * (bandLog X n) ^ Cper / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
  have hKper : ∀ n, 0 ≤ 3 * ((K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) := by
    intro n
    have hlog : 0 ≤ Real.log (X n ^ 3 / perronRe) := by
      apply Real.log_nonneg
      rw [one_le_div (by norm_num [perronRe] : (0 : ℝ) < perronRe)]
      calc
        perronRe ≤ 1 := by norm_num [perronRe]
        _ ≤ X n ^ 3 := by simpa using one_le_pow₀ (hX n).le (n := 3)
    exact mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg (hK n) Real.pi_pos.le) (by linarith))
  exact perronShift_of_vertical hX hKper hU
    (verticalShiftBound_of_lineBound hX hK hU hC hsmall hL hR)

/-- **The full three-term Perron shift with the `exp (U/3)` range discharged.**
Same as `perronShift_of_lineBound`, but the auxiliary cutoff inclusion follows
from `log X ≥ 324` instead of being assumed. -/
theorem perronShift_of_lineBound_of_log_ge {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hc0 : 0 < c) (hc1 : c ≤ 1) (hK : ∀ n, 0 ≤ K n)
    (hU : ∀ n, 3 ≤ bandLog X n) (hC : 2 ≤ Cper)
    (hlog : ∀ᶠ n : ℕ in atTop, 324 ≤ bandLog X n)
    (hL : VerticalLineBound X K Cper)
    (hR : PerronShiftRemainder X c
      (fun n => (K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe))) Cper) :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          (3 * ((K n / Real.pi) * (1 + Real.log (X n ^ 3 / perronRe)))) *
            (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
              + v * (bandLog X n) ^ Cper / X n ^ 3
              + Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
  perronShift_of_lineBound hX hK hU hC
    (hlog.mono fun _ hn => smoothCutoff_le_exp_third hc0 hc1 hn) hL hR

/-- **`VerticalShiftBound` when the Perron remainder is already absorbed.**
If the contour shift remainder is itself `O (v^{2/3} U^C)` (the form in which
`shiftError_le_three_vertical` leaves the horizontal and prime-power terms),
then the total constant is `2 Kper`. -/
theorem verticalShiftBound_of_zetaStrip_absorbed {X : ℕ → ℝ} {c : ℝ}
    {Kper : ℕ → ℝ} {Cper : ℝ}
    (hZ : VerticalZetaStripBound X c Kper Cper)
    (hR : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖(twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3)‖ ≤
          shiftVertical (Kper n) (bandLog X n) Cper v) :
    VerticalShiftBound X c (fun n => 2 * Kper n) Cper := by
  filter_upwards [hZ, hR] with n hZn hRn
  intro v t hv hvB ht
  have hsplit : twistedPrimeSum v t - twistedMain v t =
      verticalZetaSum v t (X n ^ 3) +
        ((twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3)) := by
    ring
  rw [hsplit]
  calc
    ‖verticalZetaSum v t (X n ^ 3) +
        ((twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X n ^ 3))‖
        ≤ ‖verticalZetaSum v t (X n ^ 3)‖ +
            ‖(twistedPrimeSum v t - twistedMain v t) -
              verticalZetaSum v t (X n ^ 3)‖ := norm_add_le _ _
    _ ≤ shiftVertical (Kper n) (bandLog X n) Cper v +
          shiftVertical (Kper n) (bandLog X n) Cper v :=
          add_le_add (hZn v t hv hvB ht) (hRn v t hv hvB ht)
    _ = shiftVertical (2 * Kper n) (bandLog X n) Cper v := by
          unfold shiftVertical
          ring

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Vertical.norm_verticalZetaSum_le
#print axioms Cogentic.RandomizedL21_2Vertical.verticalZetaStripBound_of_lineBound
#print axioms Cogentic.RandomizedL21_2Vertical.log_le_div_nine
#print axioms Cogentic.RandomizedL21_2Vertical.paperRate_le_third
#print axioms Cogentic.RandomizedL21_2Vertical.smoothCutoff_le_exp_third
#print axioms Cogentic.RandomizedL21_2Vertical.verticalShiftBound_of_zetaStrip
#print axioms Cogentic.RandomizedL21_2Vertical.verticalShiftBound_of_lineBound
#print axioms Cogentic.RandomizedL21_2Vertical.verticalShiftBound_of_lineBound_of_log_ge
#print axioms Cogentic.RandomizedL21_2Vertical.perronShift_of_lineBound
#print axioms Cogentic.RandomizedL21_2Vertical.perronShift_of_lineBound_of_log_ge
#print axioms Cogentic.RandomizedL21_2Vertical.verticalShiftBound_of_zetaStrip_absorbed

end Cogentic.RandomizedL21_2Vertical
