import Cogentic.RandomizedL18_4CellCount

/-!
# L18.4: canonical cell data, the supply-fit condition, and the factor `2/3`

`RandomizedL18_4CellCount` reduces `L18_4Inputs.cell_prime_count` to three
ingredients: an integer denominator cell `(A, B] ⊂ (0, V]` of width at least
`V / (d K)`, the prime-bin square-root error fitting in half that width, and the
real-to-integer rounding.  This file supplies the data for the *canonical
shrunken denominator interval*

  `(2V/3, (2V/3)(1 + 1/d)]`,  `V = exp W`,  `K = V^{1/4} = exp (W/4)`.

## What is proved

* `canonicalCellData` is an actual `CellData W d` (not an existential), obtained
  from the rounding construction of `exists_cellData_canonical`.
* `canonicalCellData_inside_shrunk` proves that this cell is *contained in the
  shrunken interval*, not merely in `(0, V]`.  The numerical hypotheses are
  `3 ≤ K` and `6 d ≤ V`, exactly the statement that `V/(dK) ≤ 2V/(3d)` and that
  the two rounding units fit.
* `eventually_supply_fit` proves the supply-fit condition

  `2 d K0 (1 + log 3 + W)^2 ≤ K`

  from `d ≤ exp (c W)` with `c < 1/4` and `W → ∞` (the polynomial is absorbed by
  `exp ((1/4 - c) W)`).  `L18_4Inputs.eventually_supply_fit` instantiates this
  on the ledger scale, using `d = D^{O(1)}` and `W` dominating every fixed
  multiple of `scale n`, so the only constant left is the critical-line `K0`.
* `exists_shrunk_cellData_and_cell_prime_count` combines the two: the honest
  prime count of a cell *inside* the shrunken interval is at least
  `V / (2 d K (1 + W))`, the field's constant.

## The factor `2V/(3dK)` versus `V/(2dK(1+W))`

Splitting the shrunken interval into `K` equal cells gives width `2V/(3dK)` and,
through the prime-bin supply, only `V/(3dK(1+W))`, i.e. `2/3` of the field's
constant.  The equal subdivision is nevertheless wasteful: the shrunken interval
has total length `2V/(3d)`, and since `K ≥ 3` we have `V/(dK) ≤ 2V/(3d)`.  Thus a
*single* cell of the full required width `V/(dK)` already fits inside the
interval, and the field's constant `V/(2dK(1+W))` is attainable as stated.
`shrunkCellWidth_le_shrunk_length` records the numerical fact
`V/(dK) ≤ 2V/(3d)`, and `paperCellWidth_eq_two_thirds_shrunkCellWidth` records
the exact `2/3` gap for the equal subdivision.  No corrected field statement is
needed; the `2/3` is an artefact of insisting on exactly `K` pieces.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`; the count
is the actual prime count of the constructed cell.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The canonical shrunken interval -/

/-- The left endpoint `2V/3` of the shrunken denominator interval. -/
noncomputable def shrunkLeft (W : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * denomScale W n / 3

/-- The right endpoint `(2V/3)(1 + 1/d)` of the shrunken denominator interval. -/
noncomputable def shrunkRight (W d : ℕ → ℝ) (n : ℕ) : ℝ :=
  shrunkLeft W n * (1 + 1 / d n)

/-- The required cell width `V/(dK)`. -/
noncomputable def shrunkCellWidth (W d : ℕ → ℝ) (n : ℕ) : ℝ :=
  denomScale W n / (d n * cellMesh W n)

/-- The width `2V/(3dK)` obtained by cutting the shrunken interval into `K`
equal pieces. -/
noncomputable def paperCellWidth (W d : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * denomScale W n / (3 * d n * cellMesh W n)

theorem shrunkLeft_pos (W : ℕ → ℝ) (n : ℕ) : 0 < shrunkLeft W n := by
  unfold shrunkLeft
  have hV := denomScale_pos W n
  positivity

theorem shrunkRight_sub_left (W d : ℕ → ℝ) (n : ℕ) (hd : d n ≠ 0) :
    shrunkRight W d n - shrunkLeft W n = 2 * denomScale W n / (3 * d n) := by
  unfold shrunkRight shrunkLeft
  field_simp [hd]
  ring

/-- The shrunken interval is long enough for a cell of the full width
`V/(dK)` as soon as `K ≥ 3` (the proof uses only `2K ≥ 3`). -/
theorem shrunkCellWidth_le_shrunk_length
    {W d : ℕ → ℝ} {n : ℕ} (hd : 0 < d n) (hK : 3 ≤ cellMesh W n) :
    shrunkCellWidth W d n ≤ shrunkRight W d n - shrunkLeft W n := by
  have hV := denomScale_pos W n
  rw [shrunkRight_sub_left W d n hd.ne']
  unfold shrunkCellWidth
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `V * (3d) ≤ 2V * (dK)`, i.e. `3 ≤ 2K`
  have hVd : 0 < denomScale W n * d n := mul_pos hV hd
  have h3K : (3 : ℝ) ≤ 2 * cellMesh W n := by linarith
  calc
    denomScale W n * (3 * d n) = 3 * (denomScale W n * d n) := by ring
    _ ≤ (2 * cellMesh W n) * (denomScale W n * d n) :=
      mul_le_mul_of_nonneg_right h3K hVd.le
    _ = 2 * denomScale W n * (d n * cellMesh W n) := by ring

/-- The equal subdivision width is exactly `2/3` of the full cell width. -/
theorem paperCellWidth_eq_two_thirds_shrunkCellWidth
    {W d : ℕ → ℝ} {n : ℕ} (hd : d n ≠ 0) (hK : cellMesh W n ≠ 0) :
    paperCellWidth W d n = (2 / 3 : ℝ) * shrunkCellWidth W d n := by
  unfold paperCellWidth shrunkCellWidth
  field_simp [hd, hK]

/-- Splitting the shrunken interval into `K` equal cells gives exactly `2/3` of
the field's per-cell constant.  This is the precise numerical content of the
`2V/(3dK)` versus `V/(2dK(1+W))` discrepancy. -/
theorem paper_count_eq_two_thirds_field_count
    {V d K logV : ℝ} (hV : 0 < V) (hd : 0 < d) (hK : 0 < K) (hlog : 0 < logV) :
    V / (3 * d * K * logV) =
      (2 / 3 : ℝ) * (V / (2 * d * K * logV)) := by
  field_simp [hV.ne', hd.ne', hK.ne', hlog.ne']

/-- The equal-subdivision count is *strictly* smaller than the field's count:
the gap `2/3` is a genuine loss, not an artefact of a weak inequality. -/
theorem paper_count_lt_field_count
    {V d K logV : ℝ} (hV : 0 < V) (hd : 0 < d) (hK : 0 < K) (hlog : 0 < logV) :
    V / (3 * d * K * logV) < V / (2 * d * K * logV) := by
  refine div_lt_div_of_pos_left hV (by positivity) ?_
  have hq : 0 < d * K * logV := mul_pos (mul_pos hd hK) hlog
  nlinarith only [hq]

/-! ## The canonical integer cell -/

/-- The canonical `CellData` of the shrunken denominator interval: the integer
cell produced by rounding the real interval
`[2V/3, 2V/3 + V/(dK) + 2]`, which the rounding lemma places inside `(0, V]`
and gives width at least `V/(dK)`. -/
noncomputable def canonicalCellData {W d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n) : CellData W d :=
  Classical.choose (exists_cellData_canonical hd hV12 hK6)

theorem canonicalCellData_A {W d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n) (n : ℕ) :
    shrunkLeft W n ≤ (canonicalCellData hd hV12 hK6).A n := by
  unfold canonicalCellData shrunkLeft
  exact (Classical.choose_spec (exists_cellData_canonical hd hV12 hK6) n).1

theorem canonicalCellData_B {W d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n) (n : ℕ) :
    ((canonicalCellData hd hV12 hK6).B n : ℝ) ≤
      shrunkLeft W n + shrunkCellWidth W d n + 2 := by
  unfold canonicalCellData shrunkLeft shrunkCellWidth
  exact (Classical.choose_spec (exists_cellData_canonical hd hV12 hK6) n).2

/-- **Containment in the shrunken interval.**  Beyond the width and `(0, V]`
facts already built into `CellData`, the canonical cell lies in
`(2V/3, (2V/3)(1 + 1/d)]` when `K ≥ 3` and `6 d ≤ V`.  The proof is the two
elementary inequalities `V/(dK) ≤ V/(3d)` and `2 ≤ V/(3d)`. -/
theorem canonicalCellData_inside_shrunk {W d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n)
    (hK3 : ∀ n, 3 ≤ cellMesh W n) (hV6d : ∀ n, 6 * d n ≤ denomScale W n) :
    ∀ n, shrunkLeft W n ≤ (canonicalCellData hd hV12 hK6).A n ∧
      ((canonicalCellData hd hV12 hK6).B n : ℝ) ≤ shrunkRight W d n := by
  intro n
  refine ⟨canonicalCellData_A hd hV12 hK6 n, ?_⟩
  have hV := denomScale_pos W n
  have hdpos := hd n
  have hKpos := cellMesh_pos W n
  have hstep1 : shrunkCellWidth W d n ≤ denomScale W n / (3 * d n) := by
    unfold shrunkCellWidth
    refine div_le_div_of_nonneg_left hV.le (by positivity) ?_
    nlinarith only [hK3 n, hdpos]
  have hstep2 : (2 : ℝ) ≤ denomScale W n / (3 * d n) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hV6d n]
  have hright : shrunkRight W d n =
      shrunkLeft W n + 2 * (denomScale W n / (3 * d n)) := by
    unfold shrunkRight shrunkLeft
    field_simp [hdpos.ne']
  have hB := canonicalCellData_B hd hV12 hK6 n
  rw [hright]
  linarith only [hB, hstep1, hstep2]

/-- **The canonical cell as an existential.**  The cell is inside the shrunken
denominator interval, so the field constant does not require widening the
interval. -/
theorem exists_cellData_shrunk {W d : ℕ → ℝ}
    (hd : ∀ n, 0 < d n) (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n)
    (hK3 : ∀ n, 3 ≤ cellMesh W n) (hV6d : ∀ n, 6 * d n ≤ denomScale W n) :
    ∃ D : CellData W d, ∀ n,
      shrunkLeft W n ≤ (D.A n : ℝ) ∧ (D.B n : ℝ) ≤ shrunkRight W d n :=
  ⟨canonicalCellData hd hV12 hK6,
    canonicalCellData_inside_shrunk hd hV12 hK6 hK3 hV6d⟩

/-! ## The supply-fit condition `2 d K0 (1 + log 3 + W)^2 ≤ K` -/

/-- `exp (c x)` eventually dominates any constant times `(1 + log 3 + x)^2`.
This is the analytic core of the supply-fit condition: the polynomial is the
square-root prime-bin error, the exponential is `K = V^{1/4}` in the variable
`x = W`. -/
theorem exp_eventually_dominates_supply_polynomial
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log 3 + x) ^ 2 ≤ Real.exp (c * x) := by
  -- `x ^ 2 = o (exp (c x))`
  have hpow : (fun x : ℝ => x ^ 2) =o[atTop] fun x : ℝ => Real.exp (c * x) := by
    have hcomp := (Real.isLittleO_pow_exp_atTop (n := 2)).comp_tendsto
      (tendsto_id.const_mul_atTop hc)
    have hcomp' : (fun x : ℝ => (c * x) ^ 2) =o[atTop]
        fun x : ℝ => Real.exp (c * x) := by
      simpa only [Function.comp_def, id_eq] using hcomp
    have hscaled := hcomp'.const_mul_left ((c⁻¹) ^ 2)
    have hfun : (fun x : ℝ => (c⁻¹) ^ 2 * (c * x) ^ 2) = fun x : ℝ => x ^ 2 := by
      ext x
      field_simp [hc.ne']
    simpa only [hfun] using hscaled
  -- `1 = o (exp (c x))`
  have hone : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => Real.exp (c * x) := by
    rw [Real.isLittleO_one_exp_comp]
    exact tendsto_id.const_mul_atTop hc
  have hsum : (fun x : ℝ => 1 + x ^ 2) =o[atTop]
      fun x : ℝ => Real.exp (c * x) := by
    simpa using hone.add hpow
  have hconst : (fun x : ℝ => (C * (1 + Real.log 3) ^ 2 * 2) * (1 + x ^ 2)) =o[atTop]
      fun x : ℝ => Real.exp (c * x) :=
    hsum.const_mul_left (C * (1 + Real.log 3) ^ 2 * 2)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ 1 + Real.log 3 := by linarith
  filter_upwards [hconst.eventuallyLE, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hpoly : (1 + Real.log 3 + x) ^ 2 ≤
      (1 + Real.log 3) ^ 2 * 2 * (1 + x ^ 2) := by
    have h1 : 1 + Real.log 3 + x ≤ (1 + Real.log 3) * (1 + x) := by
      nlinarith only [hA, hlog3, hx0]
    have h2 : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      nlinarith only [sq_nonneg (1 - x)]
    calc
      (1 + Real.log 3 + x) ^ 2 ≤ ((1 + Real.log 3) * (1 + x)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h1 2
      _ = (1 + Real.log 3) ^ 2 * (1 + x) ^ 2 := by ring
      _ ≤ (1 + Real.log 3) ^ 2 * (2 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (1 + Real.log 3) ^ 2 * 2 * (1 + x ^ 2) := by ring
  have hCnn : 0 ≤ C * (1 + Real.log 3) ^ 2 * 2 :=
    mul_nonneg (mul_nonneg hC (sq_nonneg _)) (by norm_num)
  have hnn : 0 ≤ (C * (1 + Real.log 3) ^ 2 * 2) * (1 + x ^ 2) :=
    mul_nonneg hCnn (by positivity)
  have hx' : (C * (1 + Real.log 3) ^ 2 * 2) * (1 + x ^ 2) ≤ Real.exp (c * x) := by
    have := hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn,
      abs_of_pos (Real.exp_pos (c * x))] using this
  calc
    C * (1 + Real.log 3 + x) ^ 2 ≤
        C * ((1 + Real.log 3) ^ 2 * 2 * (1 + x ^ 2)) :=
      mul_le_mul_of_nonneg_left hpoly hC
    _ = (C * (1 + Real.log 3) ^ 2 * 2) * (1 + x ^ 2) := by ring
    _ ≤ Real.exp (c * x) := hx'

/-- **Supply-fit from an exponential bound on `d`.**  If `d n ≤ exp (c W n)`
with `c < 1/4` and `W n → ∞`, then eventually

  `2 d n K0 (1 + log 3 + W n)^2 ≤ exp (W n / 4) = K n`.

The exponent gap `1/4 - c` is what absorbs the square-root error. -/
theorem eventually_supply_fit_of_exp_dominated
    {W d : ℕ → ℝ} {K0 c : ℝ} (hK0 : 0 ≤ K0) (hc : c < 1 / 4)
    (hd : ∀ᶠ n : ℕ in atTop, d n ≤ Real.exp (c * W n))
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n := by
  have hδ : 0 < 1 / 4 - c := by linarith
  have hpoly := exp_eventually_dominates_supply_polynomial
    (C := 2 * K0) (c := 1 / 4 - c) (by positivity) hδ
  obtain ⟨T, hT⟩ := eventually_atTop.1 hpoly
  filter_upwards [hd, hW.eventually (eventually_ge_atTop T)] with n hdn hWn
  have hbase : 2 * K0 * (1 + Real.log 3 + W n) ^ 2 ≤
      Real.exp ((1 / 4 - c) * W n) := hT (W n) hWn
  have hsq : 0 ≤ (1 + Real.log 3 + W n) ^ 2 := sq_nonneg _
  calc
    2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2
        = d n * (2 * K0 * (1 + Real.log 3 + W n) ^ 2) := by ring
    _ ≤ Real.exp (c * W n) * (2 * K0 * (1 + Real.log 3 + W n) ^ 2) :=
      mul_le_mul_of_nonneg_right hdn (by positivity)
    _ ≤ Real.exp (c * W n) * Real.exp ((1 / 4 - c) * W n) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = cellMesh W n := by
      unfold cellMesh
      rw [← Real.exp_add]
      congr 1
      ring

/-- The ledger instantiation: `d = D^{O(1)}` and `W` dominating every fixed
multiple of `scale n` make the exponential hypothesis automatic.  Hence the
supply-fit condition holds eventually for the critical-line constant `K0`. -/
theorem L18_4Inputs.eventually_supply_fit (I : L18_4Inputs) {K0 : ℝ} (hK0 : 0 ≤ K0) :
    ∀ᶠ n : ℕ in atTop,
      2 * I.d n * K0 * (1 + Real.log 3 + I.W n) ^ 2 ≤ I.K n := by
  have hWtop : Tendsto I.W atTop atTop := by
    rw [tendsto_atTop]
    intro T
    by_cases hT : T ≤ 0
    · filter_upwards [eventually_ge_atTop (0 : ℕ)] with n _
      linarith only [hT, I.W_nonneg n]
    · have hTpos : 0 < T := lt_of_not_ge hT
      filter_upwards [I.W_dominates T hTpos,
        scale_grows.eventually (eventually_ge_atTop (1 : ℝ))] with n hdom hscale
      nlinarith only [hdom, hscale, hTpos.le]
  have hd8 : ∀ᶠ n : ℕ in atTop, I.d n ≤ Real.exp ((1 / 8 : ℝ) * I.W n) := by
    have hcpos : 0 < 8 * I.cd + 1 := by linarith [I.cd_nonneg]
    filter_upwards [eventually_ge_atTop (3 : ℕ),
      I.W_dominates (8 * I.cd + 1) hcpos,
      scale_grows.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hdom hscale0
    have hdu : I.d n ≤ Real.exp (I.cd * scale n) := I.d_upper n hn
    have h8 : I.cd * scale n ≤ (1 / 8 : ℝ) * I.W n := by
      nlinarith only [hdom, hscale0]
    exact hdu.trans (Real.exp_le_exp.mpr h8)
  have hfit := eventually_supply_fit_of_exp_dominated (W := I.W) (d := I.d)
    (K0 := K0) (c := (1 / 8 : ℝ)) hK0 (by norm_num) hd8 hWtop
  simpa only [L18_4Inputs.K] using hfit

/-! ## The field's constant from a cell inside the shrunken interval -/

/-- Single-`n` form of `cell_prime_count_of_cellData`: the cell count follows
whenever the supply-fit condition holds at that one index. -/
theorem cell_prime_count_of_cellData_at
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hsupply : ∀ {A B : ℕ}, 2 ≤ A → A ≤ B → ∀ {lg : ℝ}, 0 < lg →
      Real.log (B : ℝ) ≤ lg →
      K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
          ((B : ℝ) - (A : ℝ)) / 2 →
        ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤ ((primeBin A B).card : ℝ))
    {W d : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (D : CellData W d) {n : ℕ}
    (hsmall : 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) :
    denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n := by
  have hB2 : 2 ≤ D.B n := le_trans (D.A_two n) (D.A_le_B n)
  have hBpos : (0 : ℝ) < (D.B n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlg : 0 < 1 + W n := by linarith [hW n]
  have hlog : Real.log (D.B n : ℝ) ≤ 1 + W n := by
    have h1 : Real.log (D.B n : ℝ) ≤ W n :=
      (Real.log_le_iff_le_exp hBpos).2 (by simpa [denomScale] using D.B_le_V n)
    linarith
  have herr :
      K0 * (1 + Real.log (3 * (D.B n : ℝ))) ^ 2 * Real.sqrt (D.B n : ℝ) ≤
        ((D.B n : ℝ) - (D.A n : ℝ)) / 2 := by
    have h1 := primeBin_supply_of_cell_width hK0 (hW n) (hd n) hB2
      (by simpa only [denomScale] using D.B_le_V n)
      (by simpa only [cellMesh] using hsmall)
    have h2 :
        (denomScale W n / (d n * cellMesh W n)) / 2 ≤
          ((D.B n : ℝ) - (D.A n : ℝ)) / 2 :=
      div_le_div_of_nonneg_right (D.width n) (by norm_num)
    have h1' :
        K0 * (1 + Real.log (3 * (D.B n : ℝ))) ^ 2 * Real.sqrt (D.B n : ℝ) ≤
          (denomScale W n / (d n * cellMesh W n)) / 2 := by
      simpa only [denomScale, cellMesh] using h1
    linarith only [h1', h2]
  have hcard :=
    hsupply (A := D.A n) (B := D.B n) (D.A_two n) (D.A_le_B n)
      (lg := 1 + W n) hlg hlog herr
  have hEq :
      denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) =
        (denomScale W n / (d n * cellMesh W n)) / (2 * (1 + W n)) := by
    have hd' : (d n) ≠ 0 := (hd n).ne'
    have hK' : (cellMesh W n) ≠ 0 := (cellMesh_pos W n).ne'
    have hW' : (1 + W n) ≠ 0 := by linarith [hW n]
    field_simp
  calc
    denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) =
        (denomScale W n / (d n * cellMesh W n)) / (2 * (1 + W n)) := hEq
    _ ≤ ((D.B n : ℝ) - (D.A n : ℝ)) / (2 * (1 + W n)) :=
      div_le_div_of_nonneg_right (D.width n) (by positivity)
    _ ≤ ((primeBin (D.A n) (D.B n)).card : ℝ) := hcard
    _ = D.Ncell n := rfl

/-- **The field statement with cells inside the shrunken interval.**  There is a
critical-line constant `K0 ≥ 0` such that, once the supply-fit condition holds,
the canonical cell of the shrunken interval has at least
`V / (2 d K (1 + W))` primes.  This is `cell_prime_count` with the paper's
denominator interval, not a widened one. -/
theorem exists_shrunk_cellData_and_cell_prime_count
    (line : DirichletLZerosOnLine) {W d : ℕ → ℝ}
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n)
    (hK3 : ∀ n, 3 ≤ cellMesh W n) (hV6d : ∀ n, 6 * d n ≤ denomScale W n) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ((∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) →
        ∃ D : CellData W d,
          (∀ n, shrunkLeft W n ≤ (D.A n : ℝ) ∧
            (D.B n : ℝ) ≤ shrunkRight W d n) ∧
            ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤
              D.Ncell n) := by
  obtain ⟨K0, hK0, hsupply⟩ := cell_card_lower_from_critical_line line
  refine ⟨K0, hK0, fun hsmall => ?_⟩
  obtain ⟨D, hD⟩ := exists_cellData_shrunk hd hV12 hK6 hK3 hV6d
  exact ⟨D, hD, cell_prime_count_of_cellData hK0 hsupply hW hd D hsmall⟩

/-- **Eventual field statement.**  The supply-fit condition is discharged by
`eventually_supply_fit_of_exp_dominated`, so with `d ≤ exp (W/8)` eventually and
`W → ∞` the lower bound holds eventually with the field's constant
`V/(2dK(1+W))`, on cells inside the shrunken interval. -/
theorem eventually_shrunk_field_count
    (line : DirichletLZerosOnLine) {W d : ℕ → ℝ}
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n)
    (hK3 : ∀ n, 3 ≤ cellMesh W n) (hV6d : ∀ n, 6 * d n ≤ denomScale W n)
    (hd8 : ∀ᶠ n : ℕ in atTop, d n ≤ Real.exp ((1 / 8 : ℝ) * W n))
    (hWtop : Tendsto W atTop atTop) :
    ∃ D : CellData W d,
      (∀ n, shrunkLeft W n ≤ (D.A n : ℝ) ∧ (D.B n : ℝ) ≤ shrunkRight W d n) ∧
        ∀ᶠ n : ℕ in atTop,
          denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n := by
  obtain ⟨K0, hK0, hsupply⟩ := cell_card_lower_from_critical_line line
  obtain ⟨D, hD⟩ := exists_cellData_shrunk hd hV12 hK6 hK3 hV6d
  have hfit : ∀ᶠ n : ℕ in atTop,
      2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n :=
    eventually_supply_fit_of_exp_dominated (W := W) (d := d) (K0 := K0)
      (c := (1 / 8 : ℝ)) hK0 (by norm_num) hd8 hWtop
  exact ⟨D, hD, hfit.mono fun n hn =>
    cell_prime_count_of_cellData_at hK0 hsupply hW hd D hn⟩

/-! ## Axiom audit -/

#print axioms shrunkCellWidth_le_shrunk_length
#print axioms paperCellWidth_eq_two_thirds_shrunkCellWidth
#print axioms paper_count_eq_two_thirds_field_count
#print axioms paper_count_lt_field_count
#print axioms canonicalCellData
#print axioms canonicalCellData_inside_shrunk
#print axioms exists_cellData_shrunk
#print axioms exp_eventually_dominates_supply_polynomial
#print axioms eventually_supply_fit_of_exp_dominated
#print axioms L18_4Inputs.eventually_supply_fit
#print axioms cell_prime_count_of_cellData_at
#print axioms exists_shrunk_cellData_and_cell_prime_count
#print axioms eventually_shrunk_field_count

end Cogentic.RandomizedL18_4
