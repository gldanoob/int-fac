import Cogentic.RandomizedL18_4
import Cogentic.RandomizedPrimeBinSupply

/-!
# L18.4: the cell prime count from the prime-bin supply

`RandomizedL18_4.L18_4Inputs.cell_prime_count` is the hypothesis

`V / (2 d K (1 + log V)) ≤ Ncell`,

where `V = exp W`, `K = exp (W / 4) = V^{1/4}`, `d` is the field degree and
`Ncell` is the minimum number of primes in one of the `K` comparable denominator
cells.  The existing `cell_card_lower_from_critical_line` turns the RH prime-bin
supply into

`(B - A) / (2 log B) ≤ #(primeBin A B)`

for *integer* endpoints `A ≤ B`, provided the square-root error is at most half
the bin width.

This file closes the gap between those two statements.

* `exists_integer_cell` is the real-to-integer rounding lemma: a real interval
  `[a, b]` of length at least `L + 2` contains natural endpoints `A ≤ B` with
  `a ≤ A`, `B ≤ b` and `B - A ≥ L`.  The `+ 2` is exactly the two endpoint
  roundings lost by `⌈a⌉` and `⌊b⌋`.
* `primeBin_supply_of_cell_width` checks that the supply error
  `K0 (1 + log (3B))² √B` fits in half the cell width as soon as
  `2 d K0 (1 + log 3 + W)² ≤ K`.  This is the arithmetic form of the paper's
  condition `d K log² V = o(√V)`.
* `cell_prime_count_of_cellData` combines the two: an integer cell of width
  `V / (d K)`, an upper endpoint `B ≤ V`, and the smallness condition imply
  the literal `cell_prime_count` inequality.
* `exists_cellData_of_real_cell` and `exists_cellData_canonical` build such
  integer cells from real cell endpoints, so the only remaining hypotheses are
  the pointwise real inequalities on `V`, `d`, `K`.

Nothing here is a `sorry`, an `axiom`, or `native_decide`; the count is the
actual prime count `#(primeBin A B)`, never `0` and never a chosen lower bound.
-/

namespace Cogentic.RandomizedL18_4

open Real
open Cogentic.Randomized

/-! ## Positivity of the two scales -/

theorem denomScale_pos (W : ℕ → ℝ) (n : ℕ) : 0 < denomScale W n := by
  unfold denomScale
  exact exp_pos _

theorem cellMesh_pos (W : ℕ → ℝ) (n : ℕ) : 0 < cellMesh W n := by
  unfold cellMesh
  exact exp_pos _

/-! ## The supply inequality fits in half a cell -/

/-- The prime-bin square-root error is smaller than half a cell of width
`V / (d K)`, provided the explicit pointwise condition
`2 d K0 (1 + log 3 + W)² ≤ K`.

The hypotheses are exactly the ones available for a cell of L18.4: the upper
endpoint is at most `V = exp W`, so `log B ≤ W`, and the cell width after the
main term is `V / (d K)`.  The factor `1 + log 3` is `log (3 B) - log B`. -/
theorem primeBin_supply_of_cell_width
    {K0 W d : ℝ} (hK0 : 0 ≤ K0) (hW : 0 ≤ W) (hd : 0 < d)
    {B : ℕ} (hB2 : 2 ≤ B) (hBV : (B : ℝ) ≤ Real.exp W)
    (hsmall : 2 * d * K0 * (1 + Real.log 3 + W) ^ 2 ≤ Real.exp (W / 4)) :
    K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      (Real.exp W / (d * Real.exp (W / 4))) / 2 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlog3B : Real.log (3 * (B : ℝ)) = Real.log 3 + Real.log (B : ℝ) := by
    rw [Real.log_mul (by norm_num) hBpos.ne']
  have hlogB : Real.log (B : ℝ) ≤ W :=
    (Real.log_le_iff_le_exp hBpos).2 hBV
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hbase : 1 + Real.log (3 * (B : ℝ)) ≤ 1 + Real.log 3 + W := by
    rw [hlog3B]
    linarith
  have hbase_nn : 0 ≤ 1 + Real.log (3 * (B : ℝ)) := by
    have hlogBnn : 0 ≤ Real.log (3 * (B : ℝ)) := by
      refine Real.log_nonneg ?_
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hB2)
      nlinarith only [hB1]
    linarith
  have hsq : (1 + Real.log (3 * (B : ℝ))) ^ 2 ≤ (1 + Real.log 3 + W) ^ 2 :=
    pow_le_pow_left₀ hbase_nn hbase 2
  have hsqrt : Real.sqrt (B : ℝ) ≤ Real.exp (W / 4) ^ 2 := by
    calc
      Real.sqrt (B : ℝ) ≤ Real.sqrt (Real.exp W) := Real.sqrt_le_sqrt hBV
      _ = Real.exp (W / 2) := by rw [← Real.exp_half]
      _ = Real.exp (W / 4) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hstep :
      K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        K0 * (1 + Real.log 3 + W) ^ 2 * Real.exp (W / 4) ^ 2 := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hsq hK0) hsqrt (Real.sqrt_nonneg _) ?_
    positivity
  have hKM :
      (Real.exp W / (d * Real.exp (W / 4))) / 2 = Real.exp (W / 4) ^ 3 / (2 * d) := by
    have hV4 : Real.exp W = Real.exp (W / 4) ^ 4 := by
      conv_lhs => rw [show W = ((4 : ℕ) : ℝ) * (W / 4) by push_cast; ring]
      rw [Real.exp_nat_mul]
    have hX : Real.exp (W / 4) ≠ 0 := (Real.exp_pos _).ne'
    have hd' : d ≠ 0 := hd.ne'
    rw [hV4]
    field_simp [hX, hd']
  rw [hKM]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d)]
  calc
    K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) * (2 * d)
        ≤ (K0 * (1 + Real.log 3 + W) ^ 2 * Real.exp (W / 4) ^ 2) * (2 * d) :=
      mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = (2 * d * K0 * (1 + Real.log 3 + W) ^ 2) * Real.exp (W / 4) ^ 2 := by ring
    _ ≤ Real.exp (W / 4) * Real.exp (W / 4) ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
    _ = Real.exp (W / 4) ^ 3 := by ring

/-- Scaled form of `primeBin_supply_of_cell_width`: if the error fits in a
`c`-fraction of the cell, `2 d K0 (1 + log 3 + W)² ≤ c K`, then it fits in
`c · V/(2 d K)`.  The unscaled lemma is the case `c = 1`. -/
theorem primeBin_supply_of_scaled_cell_width
    {K0 c W d : ℝ} (hK0 : 0 ≤ K0) (_hc : 0 ≤ c) (hW : 0 ≤ W) (hd : 0 < d)
    {B : ℕ} (hB2 : 2 ≤ B) (hBV : (B : ℝ) ≤ Real.exp W)
    (hsmall : 2 * d * K0 * (1 + Real.log 3 + W) ^ 2 ≤ c * Real.exp (W / 4)) :
    K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
      c * (Real.exp W / (d * Real.exp (W / 4))) / 2 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlog3B : Real.log (3 * (B : ℝ)) = Real.log 3 + Real.log (B : ℝ) := by
    rw [Real.log_mul (by norm_num) hBpos.ne']
  have hlogB : Real.log (B : ℝ) ≤ W :=
    (Real.log_le_iff_le_exp hBpos).2 hBV
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hbase : 1 + Real.log (3 * (B : ℝ)) ≤ 1 + Real.log 3 + W := by
    rw [hlog3B]
    linarith
  have hbase_nn : 0 ≤ 1 + Real.log (3 * (B : ℝ)) := by
    have hlogBnn : 0 ≤ Real.log (3 * (B : ℝ)) := by
      refine Real.log_nonneg ?_
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hB2)
      nlinarith only [hB1]
    linarith
  have hsq : (1 + Real.log (3 * (B : ℝ))) ^ 2 ≤ (1 + Real.log 3 + W) ^ 2 :=
    pow_le_pow_left₀ hbase_nn hbase 2
  have hsqrt : Real.sqrt (B : ℝ) ≤ Real.exp (W / 4) ^ 2 := by
    calc
      Real.sqrt (B : ℝ) ≤ Real.sqrt (Real.exp W) := Real.sqrt_le_sqrt hBV
      _ = Real.exp (W / 2) := by rw [← Real.exp_half]
      _ = Real.exp (W / 4) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hstep :
      K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        K0 * (1 + Real.log 3 + W) ^ 2 * Real.exp (W / 4) ^ 2 := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hsq hK0) hsqrt (Real.sqrt_nonneg _) ?_
    positivity
  have hKM :
      (Real.exp W / (d * Real.exp (W / 4))) / 2 = Real.exp (W / 4) ^ 3 / (2 * d) := by
    have hV4 : Real.exp W = Real.exp (W / 4) ^ 4 := by
      conv_lhs => rw [show W = ((4 : ℕ) : ℝ) * (W / 4) by push_cast; ring]
      rw [Real.exp_nat_mul]
    have hX : Real.exp (W / 4) ≠ 0 := (Real.exp_pos _).ne'
    have hd' : d ≠ 0 := hd.ne'
    rw [hV4]
    field_simp [hX, hd']
  rw [mul_div_assoc, hKM, ← mul_div_assoc]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d)]
  calc
    K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) * (2 * d)
        ≤ (K0 * (1 + Real.log 3 + W) ^ 2 * Real.exp (W / 4) ^ 2) * (2 * d) :=
      mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = (2 * d * K0 * (1 + Real.log 3 + W) ^ 2) * Real.exp (W / 4) ^ 2 := by ring
    _ ≤ (c * Real.exp (W / 4)) * Real.exp (W / 4) ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
    _ = c * Real.exp (W / 4) ^ 3 := by ring

/-! ## Real-to-integer cell rounding -/

/-- **The real-interval rounding lemma.**  A real interval `[a, b]` of length at
least `L + 2` contains natural endpoints `A = ⌈a⌉` and `B = ⌊b⌋` whose integer
cell `(A, B]` has width at least `L`.

The `2` is sharp for the two inward roundings: `⌈a⌉ < a + 1` and
`b - 1 < ⌊b⌋`, so `⌊b⌋ - ⌈a⌉ > (b - a) - 2 ≥ L`.  The hypotheses `2 ≤ a` and
`0 ≤ L` make the floor nonnegative and the interval nonempty. -/
theorem exists_integer_cell
    {a b L : ℝ} (ha : 2 ≤ a) (hL : 0 ≤ L) (hgap : L + 2 ≤ b - a) :
    ∃ A B : ℕ, 2 ≤ A ∧ A ≤ B ∧ a ≤ (A : ℝ) ∧ (B : ℝ) ≤ b ∧
      L ≤ (B : ℝ) - (A : ℝ) := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hfloor : b - 1 < (⌊b⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one b
    linarith
  have hceil : (⌈a⌉₊ : ℝ) ≤ a + 1 := by
    have h1 : (⌈a⌉₊ : ℝ) ≤ (⌊a⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one a
    have h2 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (by linarith)
    linarith
  refine ⟨⌈a⌉₊, ⌊b⌋₊, ?_, ?_, Nat.le_ceil a, Nat.floor_le hb0, ?_⟩
  · exact_mod_cast le_trans ha (Nat.le_ceil a)
  · have hle : (⌈a⌉₊ : ℝ) ≤ (⌊b⌋₊ : ℝ) := by nlinarith only [hfloor, hceil, hgap, hL]
    exact_mod_cast hle
  · nlinarith only [hfloor, hceil, hgap]

/-! ## Integer cell data -/

/-- An integer denominator cell `(A, B]` for L18.4, with the three arithmetic
facts the prime-bin supply consumes: the cell starts at `2`, its upper endpoint
is at most `V`, and its width is at least `V / (d K)`. -/
structure CellData (W d : ℕ → ℝ) where
  /-- Lower endpoint: the cell is `(A n, B n]`. -/
  A : ℕ → ℕ
  /-- Upper endpoint. -/
  B : ℕ → ℕ
  /-- The bin starts at `2`, as required by the Chebyshev estimate. -/
  A_two : ∀ n, 2 ≤ A n
  /-- The cell is nonempty. -/
  A_le_B : ∀ n, A n ≤ B n
  /-- The upper endpoint is still inside `(0, V]`, so `log B ≤ log V = W`. -/
  B_le_V : ∀ n, (B n : ℝ) ≤ denomScale W n
  /-- The integer cell retains the width `V / (d K)`. -/
  width : ∀ n, denomScale W n / (d n * cellMesh W n) ≤ (B n : ℝ) - (A n : ℝ)

namespace CellData

variable {W d : ℕ → ℝ}

/-- The actual prime count of the cell, as a real number. -/
noncomputable def Ncell (D : CellData W d) (n : ℕ) : ℝ :=
  ((primeBin (D.A n) (D.B n)).card : ℝ)

theorem Ncell_nonneg (D : CellData W d) (n : ℕ) : 0 ≤ D.Ncell n :=
  Nat.cast_nonneg _

theorem Ncell_eq (D : CellData W d) (n : ℕ) :
    D.Ncell n = ((primeBin (D.A n) (D.B n)).card : ℝ) := rfl

end CellData

/-! ## The `cell_prime_count` field -/

/-- **`L18_4Inputs.cell_prime_count` from the prime-bin supply.**  If the cell
data have width at least `V / (d K)` and upper endpoint at most `V`, and if the
square-root error satisfies `2 d K0 (1 + log 3 + W)² ≤ K`, then the actual prime
count in the cell is at least `V / (2 d K (1 + log V))`. -/
theorem cell_prime_count_of_cellData
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hsupply : ∀ {A B : ℕ}, 2 ≤ A → A ≤ B → ∀ {lg : ℝ}, 0 < lg →
      Real.log (B : ℝ) ≤ lg →
      K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
          ((B : ℝ) - (A : ℝ)) / 2 →
        ((B : ℝ) - (A : ℝ)) / (2 * lg) ≤ ((primeBin A B).card : ℝ))
    {W d : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (D : CellData W d)
    (hsmall : ∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) :
    ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n := by
  intro n
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
      (by simpa only [cellMesh] using hsmall n)
    have h2 :
        (denomScale W n / (d n * cellMesh W n)) / 2 ≤
          ((D.B n : ℝ) - (D.A n : ℝ)) / 2 := by
      exact div_le_div_of_nonneg_right (D.width n) (by norm_num)
    have h1' :
        K0 * (1 + Real.log (3 * (D.B n : ℝ))) ^ 2 * Real.sqrt (D.B n : ℝ) ≤
          (denomScale W n / (d n * cellMesh W n)) / 2 := by
      simpa only [denomScale, cellMesh] using h1
    linarith only [h1', h2]
  have hcard :=
    hsupply (D.A_two n) (D.A_le_B n) (lg := 1 + W n) hlg hlog herr
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

/-- The same reduction with the error constant `K0` existentially quantified by
the critical-line prime-bin supply.  The only remaining hypothesis is the
explicit smallness condition `2 d K0 (1 + log 3 + W)² ≤ K`. -/
theorem cell_prime_count_from_critical_line (line : DirichletLZerosOnLine)
    {W d : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (D : CellData W d) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ((∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) →
        ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n) := by
  obtain ⟨K0, hK0, hsupply⟩ := cell_card_lower_from_critical_line line
  exact ⟨K0, hK0, fun hsmall =>
    cell_prime_count_of_cellData hK0 hsupply hW hd D hsmall⟩

/-! ## Building the cells from real endpoints -/

/-- **Cell construction from real endpoints.**  If `[a n, b n]` is a real cell of
length at least `V / (d K) + 2` whose right endpoint is at most `V`, then there
is an integer cell `(A n, B n]` inside it with width at least `V / (d K)`. -/
theorem exists_cellData_of_real_cell
    {W d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    {a b : ℕ → ℝ} (ha : ∀ n, 2 ≤ a n)
    (hgap : ∀ n, denomScale W n / (d n * cellMesh W n) + 2 ≤ b n - a n)
    (hbV : ∀ n, b n ≤ denomScale W n) :
    ∃ D : CellData W d, ∀ n, a n ≤ (D.A n : ℝ) ∧ (D.B n : ℝ) ≤ b n := by
  classical
  have hL : ∀ n, 0 ≤ denomScale W n / (d n * cellMesh W n) := fun n =>
    div_nonneg (denomScale_pos W n).le (mul_pos (hd n) (cellMesh_pos W n)).le
  choose A B hspec using fun n => exists_integer_cell (ha n) (hL n) (hgap n)
  let D : CellData W d :=
    { A := A
      B := B
      A_two := fun n => (hspec n).1
      A_le_B := fun n => (hspec n).2.1
      B_le_V := fun n => ((hspec n).2.2.2.1).trans (hbV n)
      width := fun n => (hspec n).2.2.2.2 }
  refine ⟨D, fun n => ?_⟩
  change a n ≤ (A n : ℝ) ∧ (B n : ℝ) ≤ b n
  exact ⟨(hspec n).2.2.1, (hspec n).2.2.2.1⟩

/-- The literal `cell_prime_count` field, with `Ncell` equal to the actual prime
count of an integer cell built from a real cell.  The remaining hypotheses are
purely real: the cell starts above `2`, its length is at least `V / (d K) + 2`,
its upper endpoint is at most `V`, and the supply error obeys
`2 d K0 (1 + log 3 + W)² ≤ K`. -/
theorem exists_cellData_and_cell_prime_count_of_real_cell
    (line : DirichletLZerosOnLine) {W d : ℕ → ℝ}
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    {a b : ℕ → ℝ} (ha : ∀ n, 2 ≤ a n)
    (hgap : ∀ n, denomScale W n / (d n * cellMesh W n) + 2 ≤ b n - a n)
    (hbV : ∀ n, b n ≤ denomScale W n) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ((∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) →
        ∃ D : CellData W d,
          (∀ n, a n ≤ (D.A n : ℝ) ∧ (D.B n : ℝ) ≤ b n) ∧
            ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n) := by
  obtain ⟨K0, hK0, hsupply⟩ := cell_card_lower_from_critical_line line
  refine ⟨K0, hK0, fun hsmall => ?_⟩
  obtain ⟨D, hD⟩ := exists_cellData_of_real_cell hd ha hgap hbV
  exact ⟨D, hD, cell_prime_count_of_cellData hK0 hsupply hW hd D hsmall⟩

/-! ## The canonical cell of the shrunken denominator interval -/

/-- **Canonical cell.**  Take the left half `2V/3` of the shrunken denominator
interval and extend it by the cell width `V / (d K)` plus the two rounding units.
If `12 ≤ V` and `6 ≤ d K`, this cell lies inside `(0, V]`, so the rounding lemma
supplies an integer cell of width `V / (d K)` with upper endpoint at most `V`.

The two numerical hypotheses are the only real-interval facts left; both are
eventual consequences of `log V` dominating `log d` (and of `K = V^{1/4}`). -/
theorem exists_cellData_canonical
    {W d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n) :
    ∃ D : CellData W d, ∀ n,
      2 * denomScale W n / 3 ≤ (D.A n : ℝ) ∧
        (D.B n : ℝ) ≤
          2 * denomScale W n / 3 + denomScale W n / (d n * cellMesh W n) + 2 := by
  let a : ℕ → ℝ := fun n => 2 * denomScale W n / 3
  let b : ℕ → ℝ :=
    fun n => a n + denomScale W n / (d n * cellMesh W n) + 2
  have ha : ∀ n, 2 ≤ a n := by
    intro n
    have hV := hV12 n
    dsimp [a]
    linarith
  have hgap : ∀ n, denomScale W n / (d n * cellMesh W n) + 2 ≤ b n - a n := by
    intro n
    dsimp [b]
    linarith
  have hbV : ∀ n, b n ≤ denomScale W n := by
    intro n
    have hV := hV12 n
    have h6 := hK6 n
    have hdiv : denomScale W n / (d n * cellMesh W n) ≤ denomScale W n / 6 :=
      div_le_div_of_nonneg_left (denomScale_pos W n).le (by norm_num) h6
    have hquarter : denomScale W n / 6 ≤ denomScale W n / 3 - 2 := by linarith
    dsimp [b, a]
    linarith
  obtain ⟨D, hD⟩ := exists_cellData_of_real_cell hd ha hgap hbV
  exact ⟨D, fun n => by simpa [a, b] using hD n⟩

/-- **The `cell_prime_count` field for the canonical cell.**  Everything except
the three explicit pointwise real conditions is discharged: the critical-line
supply, the square-root error fit, and the real-to-integer rounding. -/
theorem cell_prime_count_canonical
    (line : DirichletLZerosOnLine) {W d : ℕ → ℝ}
    (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    (hV12 : ∀ n, 12 ≤ denomScale W n)
    (hK6 : ∀ n, 6 ≤ d n * cellMesh W n) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ((∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤ cellMesh W n) →
        ∃ D : CellData W d,
          (∀ n, 2 * denomScale W n / 3 ≤ (D.A n : ℝ)) ∧
            ∀ n, denomScale W n / (2 * d n * cellMesh W n * (1 + W n)) ≤ D.Ncell n) := by
  obtain ⟨D, hD⟩ := exists_cellData_canonical hd hV12 hK6
  obtain ⟨K0, hK0, hcount⟩ := cell_prime_count_from_critical_line line hW hd D
  refine ⟨K0, hK0, fun hsmall => ⟨D, fun n => (hD n).1, hcount hsmall⟩⟩

/-! ## The paper cell width `2V/(3dK)` and the constant in the field

The field `cell_prime_count` asks for `V / (2 d K (1 + W))`.  Splitting the
shrunken interval `(2V/3, (2V/3)(1 + 1/d)]` into `K` equal cells gives width
`2V / (3 d K)`, which yields `V / (3 d K (1 + W))`, a factor `3/2` smaller.
The two constants are separated here so that the gap is explicit: a cell of
width `c · V/(dK)` gives a count `c · V/(2 d K (1 + W))`. -/

/-- **Width-parametrised cell count.**  A cell of width at least
`c · V/(d K)` has at least `c · V / (2 d K (1 + W))` primes.  The field is the
case `c = 1`; the paper's equal subdivision of the shrunken interval is the case
`c = 2/3`. -/
theorem cell_prime_count_of_scaled_cellData
    {K0 c : ℝ} (hK0 : 0 ≤ K0) (hc : 0 ≤ c)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) -
          K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((primeBin A B).card : ℝ) * Real.log (B : ℝ))
    {W d : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    {A B : ℕ → ℕ} (hA : ∀ n, 2 ≤ A n) (hAB : ∀ n, A n ≤ B n)
    (hBV : ∀ n, (B n : ℝ) ≤ denomScale W n)
    (hwidth : ∀ n, c * (denomScale W n / (d n * cellMesh W n)) ≤
      (B n : ℝ) - (A n : ℝ))
    (hsmall : ∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤
      c * cellMesh W n) :
    ∀ n, c * (denomScale W n / (2 * d n * cellMesh W n * (1 + W n))) ≤
      ((primeBin (A n) (B n)).card : ℝ) := by
  intro n
  have hB2 : 2 ≤ B n := le_trans (hA n) (hAB n)
  have hBpos : (0 : ℝ) < (B n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hB2)
  have hlg : 0 < 1 + W n := by linarith [hW n]
  have hlog : Real.log (B n : ℝ) ≤ 1 + W n := by
    have h1 : Real.log (B n : ℝ) ≤ W n :=
      (Real.log_le_iff_le_exp hBpos).2 (by simpa [denomScale] using hBV n)
    linarith
  have herr :
      K0 * (1 + Real.log (3 * (B n : ℝ))) ^ 2 * Real.sqrt (B n : ℝ) ≤
        ((B n : ℝ) - (A n : ℝ)) / 2 := by
    have h1 := primeBin_supply_of_scaled_cell_width hK0 (hc) (hW n) (hd n) hB2
      (by simpa only [denomScale] using hBV n)
      (by simpa only [cellMesh] using hsmall n)
    have h1' :
        K0 * (1 + Real.log (3 * (B n : ℝ))) ^ 2 * Real.sqrt (B n : ℝ) ≤
          c * (denomScale W n / (d n * cellMesh W n)) / 2 := by
      simpa only [denomScale, cellMesh] using h1
    have h2 : c * (denomScale W n / (d n * cellMesh W n)) / 2 ≤
        ((B n : ℝ) - (A n : ℝ)) / 2 :=
      div_le_div_of_nonneg_right (hwidth n) (by norm_num)
    linarith only [h1', h2]
  have hcard :=
    cell_card_lower_of_primeBinSupply hK0 hsupply (hA n) (hAB n) (lg := 1 + W n)
      hlg hlog herr
  have hEq :
      c * (denomScale W n / (2 * d n * cellMesh W n * (1 + W n))) =
        c * (denomScale W n / (d n * cellMesh W n)) / (2 * (1 + W n)) := by
    have hd' : (d n) ≠ 0 := (hd n).ne'
    have hK' : (cellMesh W n) ≠ 0 := (cellMesh_pos W n).ne'
    have hW' : (1 + W n) ≠ 0 := by linarith [hW n]
    field_simp
  calc
    c * (denomScale W n / (2 * d n * cellMesh W n * (1 + W n))) =
        c * (denomScale W n / (d n * cellMesh W n)) / (2 * (1 + W n)) := hEq
    _ ≤ ((B n : ℝ) - (A n : ℝ)) / (2 * (1 + W n)) :=
      div_le_div_of_nonneg_right (hwidth n) (by positivity)
    _ ≤ ((primeBin (A n) (B n)).card : ℝ) := hcard

/-- The paper's equal-cell width `2V/(3dK)` gives the honest count
`V/(3 d K (1 + W))`, i.e. `cell_prime_count` with the constant `1/3` instead of
`1/2`.  This is the exact numerical gap between the field as stated and the
supply bound applied to the shrunken interval. -/
theorem cell_prime_count_of_paper_cell_width
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) -
          K0 * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt (B : ℝ) ≤
        ((primeBin A B).card : ℝ) * Real.log (B : ℝ))
    {W d : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (hd : ∀ n, 0 < d n)
    {A B : ℕ → ℕ} (hA : ∀ n, 2 ≤ A n) (hAB : ∀ n, A n ≤ B n)
    (hBV : ∀ n, (B n : ℝ) ≤ denomScale W n)
    (hwidth : ∀ n, (2 / 3 : ℝ) * (denomScale W n / (d n * cellMesh W n)) ≤
      (B n : ℝ) - (A n : ℝ))
    (hsmall : ∀ n, 2 * d n * K0 * (1 + Real.log 3 + W n) ^ 2 ≤
      (2 / 3 : ℝ) * cellMesh W n) :
    ∀ n, denomScale W n / (3 * d n * cellMesh W n * (1 + W n)) ≤
      ((primeBin (A n) (B n)).card : ℝ) := by
  have h := cell_prime_count_of_scaled_cellData (c := (2 / 3 : ℝ)) hK0
    (by norm_num) hsupply hW hd hA hAB hBV hwidth hsmall
  intro n
  have h' := h n
  have hd' : (d n) ≠ 0 := (hd n).ne'
  have hK' : (cellMesh W n) ≠ 0 := (cellMesh_pos W n).ne'
  have hW' : (1 + W n) ≠ 0 := by linarith [hW n]
  convert h' using 2
  field_simp

/-! ## Axiom audit -/

#print axioms primeBin_supply_of_cell_width
#print axioms primeBin_supply_of_scaled_cell_width
#print axioms exists_integer_cell
#print axioms cell_prime_count_of_cellData
#print axioms cell_prime_count_from_critical_line
#print axioms exists_cellData_of_real_cell
#print axioms exists_cellData_and_cell_prime_count_of_real_cell
#print axioms exists_cellData_canonical
#print axioms cell_prime_count_canonical
#print axioms cell_prime_count_of_scaled_cellData
#print axioms cell_prime_count_of_paper_cell_width

end Cogentic.RandomizedL18_4
