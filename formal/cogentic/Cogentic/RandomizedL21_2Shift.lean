import Cogentic.RandomizedL21_2Perron

set_option linter.style.haveILetI false

/-!
# L21.2: the truncated Perron shift at `Re s = 2/3`

`Cogentic.RandomizedL21_2Perron.L21_2PerronInputs` keeps the paper's Perron
shift as the abstract field

```
perronShift :
  ∀ᶠ n, ∀ v t, 2 ≤ v → v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
    ‖twistedPrimeSum v t - twistedMain v t‖ ≤
      Kper n * (v ^ (2 / 3) * U ^ C
        + v * U ^ C / X ^ 3
        + sqrt v * log (2 v) ^ 2).
```

The three summands are exactly the three displayed errors of the manuscript's
truncated Perron argument:

* the vertical contour at `Re s = 2/3`, `O (v^{2/3} U^C)`;
* the two horizontal segments at height `X^3`, `O (v U^C / X^3)`;
* the prime-power removal, `O (sqrt v log² (2 v))`.

The first term dominates the other two throughout the Perron range
`2 ≤ v ≤ e^{c T_X}` and `log X ≥ 3`: the horizontal term is smaller because
`v^{1/3} ≤ X^3`, and the prime-power term is smaller because
`v ≤ exp (U/3)` makes `log (2v) ≤ U` and `U ≥ 3`, `C ≥ 2` make
`sqrt v log² (2v) ≤ v^{2/3} U^C`.  This is the same absorption that
`L21_2Inputs.twisted_prime_sum` performs on the *full* Perron bound.

Consequently the whole `perronShift` field is equivalent, up to the explicit
constant `3`, to the single **vertical** estimate

```
VerticalShiftBound X c Kper Cper :
  ∀ᶠ n, ∀ v t, 2 ≤ v → v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
    ‖twistedPrimeSum v t - twistedMain v t‖ ≤ Kper n * v ^ (2 / 3) * U ^ C.
```

This is the smallest explicit zeta-side sub-`Prop` of the L21.2 Perron input:
it names only the dominant contour, and it drops the two subdominant errors.
We prove

1. `shiftError_le_three_vertical`: the three displayed errors are at most
   three times the vertical one (the paper's parameter range);
2. `perronShift_of_vertical`: `VerticalShiftBound` implies the full
   `perronShift` with the *same* constant;
3. `vertical_bound_of_perronShift`: a full `perronShift` implies
   `VerticalShiftBound` with constant `3 * Kper`, using the existing
   `L21_2Inputs.twisted_prime_sum` absorption;
4. `L21_2ShiftInputs.toPerronInputs`: a bundle in which the abstract
   `perronShift` field is replaced by `VerticalShiftBound`, together with the
   downstream `toReducedInputs`, `toInputs`, `toRatedLeaf`, `toSubexpLeaf`, the
   `B = 2` ledger slot, and the paper-assumption reassembly.

The existing product/Perron estimates (`product_perron_prefix_error`,
`product_perron_prefix_norm_le`, `primeBin_product_prefix_from_critical_line`)
are for finite Dirichlet polynomials on a dyadic support `[X, 2X]`; the L21.2
shift is for `-ζ'/ζ` at `v ≤ e^{c T_X} ≪ X`, so they control the truncation
kernel but not the zeta contour.  The zeta-side content is therefore kept in
the single `VerticalShiftBound` above.

No `sorry`, `admit`, `axiom` or `native_decide`; the loss is still the genuine
quotient `badCount / (X + 1)` and is never set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Shift

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The three displayed errors -/

/-- The vertical contour error at `Re s = 2/3`, `O (v^{2/3} U^C)`. -/
def shiftVertical (K U C v : ℝ) : ℝ :=
  K * (v ^ perronRe * U ^ C)

/-- The horizontal-segment error at height `X^3`, `O (v U^C / X^3)`. -/
def shiftHorizontal (K U C X v : ℝ) : ℝ :=
  K * (v * U ^ C / X ^ 3)

/-- The prime-power removal error, `O (sqrt v log² (2 v))`. -/
def shiftPrimePower (K v : ℝ) : ℝ :=
  K * (Real.sqrt v * (Real.log (2 * v)) ^ 2)

/-- The three-term majorant of `perronShift`, in the manuscript's order. -/
def shiftError (K U C X v : ℝ) : ℝ :=
  shiftVertical K U C v + shiftHorizontal K U C X v + shiftPrimePower K v

/-- `shiftError` is exactly the `perronShift` majorant
`K (v^{2/3} U^C + v U^C / X^3 + sqrt v log² (2v))`. -/
theorem shiftError_eq_majorant (K U C X v : ℝ) :
    shiftError K U C X v =
      K * (v ^ (2 / 3 : ℝ) * U ^ C
        + v * U ^ C / X ^ 3
        + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
  unfold shiftError shiftVertical shiftHorizontal shiftPrimePower
  rw [perronRe]
  ring

theorem shiftVertical_nonneg {K U C v : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (_hC : 0 ≤ C) (hv : 0 ≤ v) :
    0 ≤ shiftVertical K U C v := by
  unfold shiftVertical
  exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg hv _) (Real.rpow_nonneg hU _))

theorem shiftHorizontal_nonneg {K U C X v : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (_hC : 0 ≤ C) (hX : 0 ≤ X) (hv : 0 ≤ v) :
    0 ≤ shiftHorizontal K U C X v := by
  unfold shiftHorizontal
  exact mul_nonneg hK (div_nonneg (mul_nonneg hv (Real.rpow_nonneg hU _))
    (pow_nonneg hX 3))

theorem shiftPrimePower_nonneg {K v : ℝ} (hK : 0 ≤ K) :
    0 ≤ shiftPrimePower K v := by
  unfold shiftPrimePower
  exact mul_nonneg hK (mul_nonneg (Real.sqrt_nonneg v) (sq_nonneg _))

theorem shiftError_nonneg {K U C X v : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (hC : 0 ≤ C) (hX : 0 ≤ X) (hv : 0 ≤ v) :
    0 ≤ shiftError K U C X v := by
  unfold shiftError
  exact add_nonneg (add_nonneg (shiftVertical_nonneg hK hU hC hv)
    (shiftHorizontal_nonneg hK hU hC hX hv)) (shiftPrimePower_nonneg hK)

/-- **The horizontal error is dominated by the vertical one.**  Since
`v = v^{1/3} v^{2/3}` and `v^{1/3} ≤ X^3`, the quotient `v / X^3` is at most
`v^{2/3}`. -/
theorem shiftHorizontal_le_shiftVertical {K U C X v : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (_hC : 0 ≤ C) (hv : 0 < v) (hX : 0 < X)
    (hv13 : v ^ (1 / 3 : ℝ) ≤ X ^ 3) :
    shiftHorizontal K U C X v ≤ shiftVertical K U C v := by
  unfold shiftHorizontal shiftVertical
  have hUC : 0 ≤ U ^ C := Real.rpow_nonneg hU C
  have hX3 : 0 < X ^ 3 := pow_pos hX 3
  have hv23 : 0 ≤ v ^ (2 / 3 : ℝ) := Real.rpow_nonneg hv.le _
  have hdiv : v / X ^ 3 ≤ v ^ (2 / 3 : ℝ) := by
    rw [div_le_iff₀ hX3]
    have hveq : v = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hv (1 / 3) (2 / 3)]
      norm_num
    calc
      v = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) := hveq
      _ ≤ X ^ 3 * v ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hv13 hv23
      _ = v ^ (2 / 3 : ℝ) * X ^ 3 := by rw [mul_comm]
  have hmul : (v / X ^ 3) * U ^ C ≤ v ^ (2 / 3 : ℝ) * U ^ C :=
    mul_le_mul_of_nonneg_right hdiv hUC
  calc
    K * (v * U ^ C / X ^ 3) = K * ((v / X ^ 3) * U ^ C) := by ring
    _ ≤ K * (v ^ (2 / 3 : ℝ) * U ^ C) :=
      mul_le_mul_of_nonneg_left hmul hK
    _ = K * (v ^ perronRe * U ^ C) := by rw [perronRe]

/-- **The prime-power error is dominated by the vertical one.**  On the Perron
range `v ≤ exp (U/3)` with `U ≥ 3`, `C ≥ 2`, we have `sqrt v ≤ v^{2/3}` and
`log² (2v) ≤ U^C`. -/
theorem shiftPrimePower_le_shiftVertical {K U C v : ℝ}
    (hK : 0 ≤ K) (hU3 : 3 ≤ U) (hC2 : 2 ≤ C)
    (hv2 : 2 ≤ v) (hvExp : v ≤ Real.exp (U / 3)) :
    shiftPrimePower K v ≤ shiftVertical K U C v := by
  unfold shiftPrimePower shiftVertical
  have hv0 : 0 < v := by linarith
  have hv1 : 1 ≤ v := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hsqrt : Real.sqrt v ≤ v ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv1
      (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
  have hv2exp : 2 * v ≤ Real.exp U := by
    have h2 : 2 * v ≤ 2 * Real.exp (U / 3) :=
      mul_le_mul_of_nonneg_left hvExp (by norm_num)
    have hlog2 : Real.log 2 ≤ (2 / 3 : ℝ) * U := by
      have h2le : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      nlinarith
    calc
      2 * v ≤ 2 * Real.exp (U / 3) := h2
      _ = Real.exp (Real.log 2) * Real.exp (U / 3) := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp (Real.log 2 + U / 3) := by rw [← Real.exp_add]
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  have hlogv : Real.log (2 * v) ≤ U :=
    (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2 * v)).mpr hv2exp
  have hsq : (Real.log (2 * v)) ^ 2 ≤ U ^ (2 : ℝ) := by
    have hnn : 0 ≤ Real.log (2 * v) :=
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * v)
    rw [Real.rpow_two]
    nlinarith
  have hupow : U ^ (2 : ℝ) ≤ U ^ C :=
    Real.rpow_le_rpow_of_exponent_le hU1 hC2
  have hlog : (Real.log (2 * v)) ^ 2 ≤ U ^ C := hsq.trans hupow
  have hmul : Real.sqrt v * (Real.log (2 * v)) ^ 2 ≤ v ^ (2 / 3 : ℝ) * U ^ C :=
    mul_le_mul hsqrt hlog (sq_nonneg _) (Real.rpow_nonneg hv0.le _)
  calc
    K * (Real.sqrt v * (Real.log (2 * v)) ^ 2)
        ≤ K * (v ^ (2 / 3 : ℝ) * U ^ C) :=
      mul_le_mul_of_nonneg_left hmul hK
    _ = K * (v ^ perronRe * U ^ C) := by rw [perronRe]

/-- **The three displayed errors are at most three times the vertical one** on
the Perron range.  This is the arithmetic content of the paper's absorption of
the horizontal and prime-power errors into `v^{2/3} U^C`. -/
theorem shiftError_le_three_vertical {K U C X v : ℝ}
    (hK : 0 ≤ K) (hU3 : 3 ≤ U) (hC2 : 2 ≤ C)
    (hv2 : 2 ≤ v) (hX : 0 < X)
    (hv13 : v ^ (1 / 3 : ℝ) ≤ X ^ 3)
    (hvExp : v ≤ Real.exp (U / 3)) :
    shiftError K U C X v ≤ 3 * shiftVertical K U C v := by
  have hH := shiftHorizontal_le_shiftVertical (K := K) (U := U) (C := C) (X := X)
    (v := v) hK (by linarith : 0 ≤ U) (by linarith : 0 ≤ C)
    (by linarith : 0 < v) hX hv13
  have hP := shiftPrimePower_le_shiftVertical (K := K) (U := U) (C := C) (v := v)
    hK hU3 hC2 hv2 hvExp
  unfold shiftError
  calc
    shiftVertical K U C v + shiftHorizontal K U C X v + shiftPrimePower K v
        ≤ shiftVertical K U C v + shiftVertical K U C v + shiftVertical K U C v :=
      add_le_add (add_le_add le_rfl hH) hP
    _ = 3 * shiftVertical K U C v := by ring

/-- On the L21.2 Perron range `v ≤ exp (U/3)` with `X = exp U` and `U ≥ 3`, the
height condition `v^{1/3} ≤ X^3` is automatic. -/
theorem rpow_one_third_le_height {X v U : ℝ} (hX : 1 < X)
    (hU : U = Real.log X) (hU3 : 3 ≤ U) (hv0 : 0 ≤ v)
    (hvExp : v ≤ Real.exp (U / 3)) :
    v ^ (1 / 3 : ℝ) ≤ X ^ 3 := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hXexp : X = Real.exp U := by
    rw [hU, Real.exp_log hX0]
  have hX3 : X ^ 3 = Real.exp (3 * U) := by
    calc
      X ^ 3 = Real.exp U ^ 3 := by rw [hXexp]
      _ = Real.exp (3 * U) := by
        simpa using (Real.exp_nat_mul U 3).symm
  have h1 : v ^ (1 / 3 : ℝ) ≤ (Real.exp (U / 3)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hv0 hvExp (by norm_num)
  have h2 : (Real.exp (U / 3)) ^ (1 / 3 : ℝ) = Real.exp (U / 9) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have h3 : Real.exp (U / 9) ≤ Real.exp (3 * U) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    v ^ (1 / 3 : ℝ) ≤ (Real.exp (U / 3)) ^ (1 / 3 : ℝ) := h1
    _ = Real.exp (U / 9) := h2
    _ ≤ Real.exp (3 * U) := h3
    _ = X ^ 3 := hX3.symm

/-- The three-error absorption with the height condition discharged from the
L21.2 Perron range. -/
theorem shiftError_le_three_vertical_of_perronRange {K U C X v : ℝ}
    (hK : 0 ≤ K) (hU3 : 3 ≤ U) (hC2 : 2 ≤ C)
    (hv2 : 2 ≤ v) (hX : 1 < X) (hU : U = Real.log X)
    (hvExp : v ≤ Real.exp (U / 3)) :
    shiftError K U C X v ≤ 3 * shiftVertical K U C v :=
  shiftError_le_three_vertical hK hU3 hC2 hv2 (lt_trans zero_lt_one hX)
    (rpow_one_third_le_height hX hU hU3 (by linarith) hvExp) hvExp

/-! ## The single vertical Perron-shift input -/

/-- **The vertical Perron-shift estimate at `Re s = 2/3`.**

This is `perronShift` with the horizontal and prime-power errors removed: the
remaining term is exactly the contour at `perronRe = 2/3`, truncated at height
`X^3`.  It is the smallest explicit zeta-side input of the L21.2 reduction. -/
def VerticalShiftBound (X : ℕ → ℝ) (c : ℝ) (Kper : ℕ → ℝ) (Cper : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        shiftVertical (Kper n) (bandLog X n) Cper v

/-- The full `perronShift` field follows from the vertical estimate with the
same constant: the vertical term is one summand of the three-term majorant. -/
theorem perronShift_of_vertical {X : ℕ → ℝ} {c : ℝ} {Kper : ℕ → ℝ} {Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hK : ∀ n, 0 ≤ Kper n)
    (hU : ∀ n, 3 ≤ bandLog X n)
    (h : VerticalShiftBound X c Kper Cper) :
    ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
      v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
        ‖twistedPrimeSum v t - twistedMain v t‖ ≤
          Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
            + v * (bandLog X n) ^ Cper / X n ^ 3
            + Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
  filter_upwards [h] with n hn
  intro v t hv hvB ht
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have hUpos : 0 < bandLog X n := lt_of_lt_of_le (by norm_num) (hU n)
  have hUC : 0 ≤ (bandLog X n) ^ Cper := Real.rpow_nonneg hUpos.le Cper
  have hv0 : 0 ≤ v := by linarith
  have hA : 0 ≤ v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper :=
    mul_nonneg (Real.rpow_nonneg hv0 _) hUC
  have hB : 0 ≤ v * (bandLog X n) ^ Cper / X n ^ 3 :=
    div_nonneg (mul_nonneg hv0 hUC) (pow_nonneg hXpos.le 3)
  have hC : 0 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg v) (sq_nonneg _)
  have hle : v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper ≤
      v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
        + v * (bandLog X n) ^ Cper / X n ^ 3
        + Real.sqrt v * (Real.log (2 * v)) ^ 2 := by linarith
  have hbase : shiftVertical (Kper n) (bandLog X n) Cper v =
      Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper) := by
    simp [shiftVertical, perronRe]
  calc
    ‖twistedPrimeSum v t - twistedMain v t‖
        ≤ shiftVertical (Kper n) (bandLog X n) Cper v := hn v t hv hvB ht
    _ = Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper) := hbase
    _ ≤ Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
      mul_le_mul_of_nonneg_left hle (hK n)

/-- A full `perronShift` implies the vertical estimate with the explicit
constant `3 * Kper`.  The proof reuses the existing absorption theorem
`L21_2Inputs.twisted_prime_sum`, which is exactly the paper's estimate after
combining the three displayed errors. -/
theorem vertical_bound_of_perronShift (P : L21_2PerronInputs) :
    VerticalShiftBound P.X P.c (fun n => 3 * P.Kper n) P.Cper := by
  have h := L21_2Inputs.twisted_prime_sum P.toInputs
  filter_upwards [h] with n hn
  intro v t hv hvB ht
  have h' := hn v t hv hvB ht
  have heq : (3 * P.Kper n) * v ^ (2 / 3 : ℝ) * (bandLog P.X n) ^ P.Cper =
      shiftVertical (3 * P.Kper n) (bandLog P.X n) P.Cper v := by
    simp [shiftVertical, perronRe]
    ring
  exact h'.trans (le_of_eq heq)

/-! ## The bundle with the vertical input -/

/-- `L21_2PerronInputs` with the abstract three-term `perronShift` replaced by
the single vertical estimate `VerticalShiftBound`.  Every other field is
unchanged. -/
structure L21_2ShiftInputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c`. -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)`. -/
  fourierGap : ℕ → ℝ → ℂ
  smoothCount : ℕ → ℝ
  badCount : ℕ → ℝ
  lowTerm : ℕ → ℝ
  middleTerm : ℕ → ℝ
  tailTerm : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  X_gt_one : ∀ n, 1 < X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog X n
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  Cper_ge_two : 2 ≤ Cper
  Ceps_nonneg : 0 ≤ Ceps
  polyExp_ge_three : 3 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  badCount_nonneg : ∀ n, 0 ≤ badCount n
  lowTerm_nonneg : ∀ n, 0 ≤ lowTerm n
  middleTerm_nonneg : ∀ n, 0 ≤ middleTerm n
  tailTerm_nonneg : ∀ n, 0 ≤ tailTerm n
  /-- **The vertical Perron shift at `Re s = 2/3`.**  This replaces the
  three-error `perronShift` field of `L21_2PerronInputs`. -/
  verticalShift : VerticalShiftBound X c Kper Cper
  fourierSupBound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ X n ^ 3 →
    ‖fourierGap n t‖ ≤ supEps X (aOf X c) Ceps n
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  tentChebyshev : ∀ᶠ n : ℕ in atTop,
    badCount n / (X n + 1) ≤
      4 * (kOf X c n * spacingOf X c n) ^ 2 *
        (lowTerm n + middleTerm n + tailTerm n)
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) *
        Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
      smoothCount n
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    lowTerm n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate X n)
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    middleTerm n ≤ Real.exp (-((1 / c) - δ) * paperRate X n)
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    tailTerm n ≤ Real.exp (-δ * paperRate X n)
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2ShiftInputs

variable (S : L21_2ShiftInputs)

/-- **The vertical input builds `L21_2PerronInputs`.**  The only change is that
`perronShift` is supplied by `perronShift_of_vertical`; all other fields pass
through. -/
def toPerronInputs : L21_2PerronInputs where
  X := S.X
  c := S.c
  Kper := S.Kper
  Cper := S.Cper
  Ceps := S.Ceps
  fourierGap := S.fourierGap
  smoothCount := S.smoothCount
  badCount := S.badCount
  lowTerm := S.lowTerm
  middleTerm := S.middleTerm
  tailTerm := S.tailTerm
  polyExp := S.polyExp
  X_gt_one := S.X_gt_one
  c_pos := S.c_pos
  c_le_one := S.c_le_one
  U_ge_three := S.U_ge_three
  Kper_nonneg := S.Kper_nonneg
  Cper_ge_two := S.Cper_ge_two
  Ceps_nonneg := S.Ceps_nonneg
  polyExp_ge_three := S.polyExp_ge_three
  smoothCount_nonneg := S.smoothCount_nonneg
  badCount_nonneg := S.badCount_nonneg
  lowTerm_nonneg := S.lowTerm_nonneg
  middleTerm_nonneg := S.middleTerm_nonneg
  tailTerm_nonneg := S.tailTerm_nonneg
  perronShift := perronShift_of_vertical S.X_gt_one S.Kper_nonneg S.U_ge_three
    S.verticalShift
  fourierSupBound := S.fourierSupBound
  b_le_B := S.b_le_B
  tentChebyshev := S.tentChebyshev
  densityNormalization := S.densityNormalization
  fourierLow := S.fourierLow
  fourierMiddle := S.fourierMiddle
  fourierTail := S.fourierTail
  U_dominates := S.U_dominates
  U_le_exp := S.U_le_exp

/-- The reduced `L21_2Sub` bundle. -/
def toReducedInputs : L21_2ReducedInputs :=
  L21_2PerronInputs.toReducedInputs S.toPerronInputs

/-- The parent `L21_2Inputs`. -/
def toInputs : L21_2Inputs := L21_2PerronInputs.toInputs S.toPerronInputs

/-- The L21.2 `RatedLeaf`. -/
def toRatedLeaf : RatedLeaf := L21_2PerronInputs.toRatedLeaf S.toPerronInputs

/-- The `D^{-B}` form as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf := L21_2PerronInputs.toSubexpLeaf S.toPerronInputs

theorem loss_nonneg (n : ℕ) : 0 ≤ S.toReducedInputs.loss n :=
  S.toReducedInputs.loss_nonneg n

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      S.toReducedInputs.loss n ≤ Real.exp (-(((S.c) / 64) * paperRate S.X n)) :=
  S.toReducedInputs.loss_le_paper

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      S.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = S.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le S.toReducedInputs h

/-- The eleven remaining leaves plus the vertical L21.2 shift inputs give the
full paper assumptions. -/
def paperAssumptions_of_shift
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2PerronInputs.paperAssumptions_of_perron S.toPerronInputs A

end L21_2ShiftInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Shift.shiftVertical_nonneg
#print axioms Cogentic.RandomizedL21_2Shift.shiftError_eq_majorant
#print axioms Cogentic.RandomizedL21_2Shift.shiftHorizontal_le_shiftVertical
#print axioms Cogentic.RandomizedL21_2Shift.shiftPrimePower_le_shiftVertical
#print axioms Cogentic.RandomizedL21_2Shift.shiftError_le_three_vertical
#print axioms Cogentic.RandomizedL21_2Shift.rpow_one_third_le_height
#print axioms Cogentic.RandomizedL21_2Shift.shiftError_le_three_vertical_of_perronRange
#print axioms Cogentic.RandomizedL21_2Shift.perronShift_of_vertical
#print axioms Cogentic.RandomizedL21_2Shift.vertical_bound_of_perronShift
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.toPerronInputs
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Shift.L21_2ShiftInputs.paperAssumptions_of_shift

end Cogentic.RandomizedL21_2Shift
