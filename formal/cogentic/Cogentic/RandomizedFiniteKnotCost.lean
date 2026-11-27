import Cogentic.RandomizedPrivateFloor
import Mathlib.Tactic.FieldSimp

namespace Cogentic.Randomized

open scoped BigOperators

noncomputable def bellmanKnot (m : ℝ) : ℝ := 2 / (3 * (1 - m))

noncomputable def bellmanValue (m : ℝ) : ℝ := 4 / (27 * (1 - m) ^ 2)

theorem bellmanKnot_mem {m : ℝ} (hm : m < 1 / 3) :
    0 < bellmanKnot m ∧ bellmanKnot m < 1 := by
  have hd : 0 < 3 * (1 - m) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_iff₀ hd).2 ?_⟩
  linarith

private theorem bellman_gap {m : ℝ} (hm : m < 1 / 3) (t : ℝ) :
    bellmanValue m - (m * t ^ 3 + t ^ 2 * (1 - t)) =
      (t - bellmanKnot m) ^ 2 * ((1 - m) * t + 1 / 3) := by
  have hd : 1 - m ≠ 0 := by linarith
  unfold bellmanValue bellmanKnot
  field_simp
  ring

/-- Exact maximum of the scalar Bellman objective on `0 ≤ t ≤ 1`. -/
theorem bellman_maximum {m : ℝ} (hm : m < 1 / 3) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → m * t ^ 3 + t ^ 2 * (1 - t) ≤ bellmanValue m) ∧
    m * bellmanKnot m ^ 3 + bellmanKnot m ^ 2 * (1 - bellmanKnot m) = bellmanValue m := by
  constructor
  · intro t ht _
    have hfactor : 0 ≤ (1 - m) * t + 1 / 3 := by
      have h : 0 ≤ 1 - m := by linarith
      positivity
    have hgap := mul_nonneg (sq_nonneg (t - bellmanKnot m)) hfactor
    rw [← bellman_gap hm] at hgap
    exact sub_nonneg.mp hgap
  · have h := bellman_gap hm (bellmanKnot m)
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_eq_zero] at h
    exact h.symm

private theorem bellmanValue_range {m : ℝ} (hm : m < 1 / 3) :
    0 ≤ bellmanValue m ∧ bellmanValue m < 1 / 3 := by
  have ht := bellmanKnot_mem hm
  have he : bellmanValue m = bellmanKnot m ^ 2 / 3 := by
    have hd : 1 - m ≠ 0 := by linarith
    unfold bellmanValue bellmanKnot
    field_simp
    ring
  rw [he]
  have hpos : 0 < 1 + bellmanKnot m := by linarith only [ht.1]
  exact ⟨by positivity, by nlinarith only [mul_pos (sub_pos.mpr ht.2) hpos]⟩

/-- `finiteKnotMaximum k` is the unit-endpoint maximum for `k + 1` intervals. -/
noncomputable def finiteKnotMaximum : ℕ → ℝ
  | 0 => 0
  | k + 1 => bellmanValue (finiteKnotMaximum k)

theorem finiteKnotMaximum_range (k : ℕ) :
    0 ≤ finiteKnotMaximum k ∧ finiteKnotMaximum k < 1 / 3 := by
  induction k with
  | zero => norm_num [finiteKnotMaximum]
  | succ k ih => exact bellmanValue_range ih.2

noncomputable def leftSquareSum (n : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z i ^ 2 * (z (i + 1) - z i)

private theorem homogeneous_step {m x y : ℝ} (hy : y ≠ 0) :
    m * x ^ 3 + x ^ 2 * (y - x) =
      (m * (x / y) ^ 3 + (x / y) ^ 2 * (1 - x / y)) * y ^ 3 := by
  field_simp

private theorem homogeneous_bound {m x y : ℝ} (hm : m < 1 / 3) (hx : 0 ≤ x)
    (hxy : x ≤ y) : m * x ^ 3 + x ^ 2 * (y - x) ≤ bellmanValue m * y ^ 3 := by
  by_cases hy : y = 0
  · have hx0 : x = 0 := le_antisymm (hy ▸ hxy) hx
    simp [hx0, hy]
  have hypos : 0 < y := lt_of_le_of_ne (hx.trans hxy) (Ne.symm hy)
  rw [homogeneous_step hy]
  exact mul_le_mul_of_nonneg_right ((bellman_maximum hm).1 (x / y)
    (div_nonneg hx hypos.le) (div_le_one₀ hypos |>.2 hxy)) (by positivity)

private theorem knot_nonneg {n : ℕ} {z : ℕ → ℝ} (hz : z 0 = 0)
    (hstep : ∀ i < n, z i ≤ z (i + 1)) (i : ℕ) (hi : i ≤ n) : 0 ≤ z i := by
  induction i with
  | zero => rw [hz]
  | succ j hj => exact (hj (by omega)).trans (hstep j (by omega))

/-- The Bellman value bounds every weakly ordered partition. -/
theorem leftSquareSum_le_finiteKnotMaximum (k : ℕ) (z : ℕ → ℝ) (hz : z 0 = 0)
    (hstep : ∀ i < k + 1, z i ≤ z (i + 1)) :
    leftSquareSum (k + 1) z ≤ finiteKnotMaximum k * z (k + 1) ^ 3 := by
  induction k with
  | zero => simp [leftSquareSum, finiteKnotMaximum, hz]
  | succ k ih =>
    have hprefix (i : ℕ) (hi : i < k + 1) : z i ≤ z (i + 1) := hstep i (by omega)
    rw [leftSquareSum, Finset.sum_range_succ]
    calc
      _ ≤ finiteKnotMaximum k * z (k + 1) ^ 3 + z (k + 1) ^ 2 * (z (k + 2) - z (k + 1)) :=
        add_le_add (ih hprefix) le_rfl
      _ ≤ _ := homogeneous_bound (finiteKnotMaximum_range k).2
        (knot_nonneg hz hprefix _ le_rfl) (hstep _ (by omega))

/-- A strict partition attains the Bellman value at every positive endpoint. -/
theorem exists_finiteKnotMaximum_partition (k : ℕ) {y : ℝ} (hy : 0 < y) :
    ∃ z : ℕ → ℝ, z 0 = 0 ∧ z (k + 1) = y ∧
      (∀ i < k + 1, z i < z (i + 1)) ∧
      leftSquareSum (k + 1) z = finiteKnotMaximum k * y ^ 3 := by
  induction k generalizing y with
  | zero =>
    refine ⟨fun i => if i = 0 then 0 else y, by simp, by simp, ?_, ?_⟩
    · intro i hi
      have h : i = 0 := by omega
      simpa [h] using hy
    · simp [leftSquareSum, finiteKnotMaximum]
  | succ k ih =>
    let m := finiteKnotMaximum k
    let t := bellmanKnot m
    have hm : m < 1 / 3 := (finiteKnotMaximum_range k).2
    have ht : 0 < t ∧ t < 1 := bellmanKnot_mem hm
    obtain ⟨w, hw0, hwend, hwstep, hwsum⟩ := ih (mul_pos ht.1 hy)
    let z (i : ℕ) := if i = k + 2 then y else w i
    have hkeep (i : ℕ) (hi : i ≤ k + 1) : z i = w i := by
      simp [z, show i ≠ k + 2 by omega]
    have hlast : z (k + 2) = y := by simp [z]
    have hbefore : z (k + 1) = t * y := (hkeep _ le_rfl).trans hwend
    refine ⟨z, (hkeep _ (by omega)).trans hw0, hlast, ?_, ?_⟩
    · intro i hi
      by_cases hp : i < k + 1
      · simpa only [hkeep i (by omega), hkeep (i + 1) (by omega)] using hwstep i hp
      · have he : i = k + 1 := by omega
        rw [he, hbefore, hlast]
        simpa using mul_lt_mul_of_pos_right ht.2 hy
    · have hsum : leftSquareSum (k + 1) z = leftSquareSum (k + 1) w := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [hkeep i (by omega), hkeep (i + 1) (by omega)]
      rw [leftSquareSum, Finset.sum_range_succ]
      change leftSquareSum (k + 1) z + z (k + 1) ^ 2 * (z (k + 2) - z (k + 1)) =
        bellmanValue m * y ^ 3
      rw [hsum, hwsum, hbefore, hlast, homogeneous_step hy.ne', mul_div_cancel_right₀ _ hy.ne']
      rw [(bellman_maximum hm).2]

/-- The maximum over all unit partitions is attained with strictly increasing knots. -/
theorem finiteKnotMaximum_exact (k : ℕ) :
    (∀ z : ℕ → ℝ, z 0 = 0 → z (k + 1) = 1 →
      (∀ i < k + 1, z i ≤ z (i + 1)) → leftSquareSum (k + 1) z ≤ finiteKnotMaximum k) ∧
    ∃ z : ℕ → ℝ, z 0 = 0 ∧ z (k + 1) = 1 ∧
      (∀ i < k + 1, z i < z (i + 1)) ∧ leftSquareSum (k + 1) z = finiteKnotMaximum k := by
  constructor
  · intro z hz0 hz1 hstep
    simpa [hz1] using leftSquareSum_le_finiteKnotMaximum k z hz0 hstep
  · simpa using exists_finiteKnotMaximum_partition k (y := 1) zero_lt_one

/-- The finite tail-cap bound uses the exact number of screening intervals. -/
theorem finite_knot_private_floor (k : ℕ) (z w : ℕ → ℝ) {h P : ℝ}
    (hh : 0 ≤ h) (hz0 : z 0 = 0) (hz1 : z (k + 1) = 1)
    (hstep : ∀ i < k + 1, z i ≤ z (i + 1))
    (htail : ∀ i < k + 1, (∑ j ∈ Finset.Ico i (k + 1), w j) ≤ P - h * z (i + 1)) :
    (∑ i ∈ Finset.range (k + 1), z (i + 1) ^ 2 * w i) +
      h * (1 - finiteKnotMaximum k) ≤ P := by
  let n := k + 1
  let tail (i : ℕ) := ∑ j ∈ Finset.Ico i n, w j
  have hparts : (∑ i ∈ Finset.range n, z (i + 1) ^ 2 * w i) =
      ∑ i ∈ Finset.range n, (z (i + 1) ^ 2 - z i ^ 2) * tail i := by
    have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
        z (i + 1) ^ 2 * w i = (z (i + 1) ^ 2 - z i ^ 2) * tail i -
          (z (i + 1) ^ 2 * tail (i + 1) - z i ^ 2 * tail i) := by
      have hti : tail i = w i + tail (i + 1) :=
        Finset.sum_eq_sum_Ico_succ_bot (Finset.mem_range.mp hi) w
      rw [hti]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun i => z i ^ 2 * tail i)]
    simp [tail, hz0]
  have hbound : (∑ i ∈ Finset.range n, (z (i + 1) ^ 2 - z i ^ 2) * tail i) ≤
      ∑ i ∈ Finset.range n, (P * (z (i + 1) ^ 2 - z i ^ 2) -
        h * ((z (i + 1) ^ 3 - z i ^ 3) - z i ^ 2 * (z (i + 1) - z i))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hs := pow_le_pow_left₀ (knot_nonneg hz0 hstep i hin.le) (hstep i hin) 2
    have hcap := mul_le_mul_of_nonneg_left (htail i hin) (sub_nonneg.mpr hs)
    convert hcap using 1
    ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub (fun i => z i ^ 2), Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun i => z i ^ 3),
    show z n = 1 from hz1, hz0, ← leftSquareSum] at hbound
  have hm := mul_le_mul_of_nonneg_left ((finiteKnotMaximum_exact k).1 z hz0 hz1 hstep) hh
  rw [hparts]
  nlinarith only [hbound, hm]

end Cogentic.Randomized
