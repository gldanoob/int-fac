import Cogentic.RandomizedFiniteKnotCost
import Mathlib.Algebra.Order.Floor.Div

namespace Cogentic.Randomized

private def thirdScale : ℕ := 10 ^ 13
private def scale : ℕ := 3 * thirdScale
private def denominator (u : ℕ) : ℕ := 27 * (scale - u) ^ 2
private def numerator : ℕ := 4 * scale ^ 3

private def roundedUpper : ℕ → ℕ
  | 0 => 0
  | n + 1 => numerator ⌈/⌉ denominator (roundedUpper n)

private theorem denominator_pos {u : ℕ} (hu : u ≤ thirdScale) :
    0 < denominator u := by
  have hs : thirdScale < scale := by decide
  unfold denominator
  exact Nat.mul_pos (by decide) (pow_pos (Nat.sub_pos_of_lt (hu.trans_lt hs)) _)

private theorem roundedUpper_cap (n : ℕ) : roundedUpper n ≤ thirdScale := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    change numerator ⌈/⌉ denominator (roundedUpper n) ≤ thirdScale
    apply (ceilDiv_le_iff_le_mul (denominator_pos ih)).2
    have hd : denominator thirdScale ≤ denominator (roundedUpper n) := by
      unfold denominator
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le_sub_left ih _) _)
    have hfixed : numerator = denominator thirdScale * thirdScale := by decide
    rw [hfixed]
    exact Nat.mul_le_mul_right _ hd

private theorem roundedUpper_sound (n : ℕ) :
    finiteKnotMaximum n ≤ (roundedUpper n : ℝ) / (scale : ℝ) := by
  induction n with
  | zero => simp [finiteKnotMaximum, roundedUpper]
  | succ n ih =>
    have hs : 0 < scale := by decide
    have ht : thirdScale < scale := by decide
    have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
    have hu := (roundedUpper_cap n).trans_lt ht
    have huR : (roundedUpper n : ℝ) < (scale : ℝ) := by exact_mod_cast hu
    have hd := denominator_pos (roundedUpper_cap n)
    have hdR : (0 : ℝ) < denominator (roundedUpper n) := by exact_mod_cast hd
    have hsub : (0 : ℝ) < (scale : ℝ) - (roundedUpper n : ℝ) := sub_pos.mpr huR
    have hratio : 0 < 1 - (roundedUpper n : ℝ) / (scale : ℝ) := by
      have hlt : (roundedUpper n : ℝ) / (scale : ℝ) < 1 := by
        apply (div_lt_iff₀ hsR).2
        simpa using huR
      exact sub_pos.mpr hlt
    have hnat : numerator ≤ denominator (roundedUpper n) * roundedUpper (n + 1) := by
      apply (ceilDiv_le_iff_le_mul hd).1
      exact le_rfl
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [Nat.cast_mul] at hcast
    have hdenom : (denominator (roundedUpper n) : ℝ) =
        27 * ((scale : ℝ) - (roundedUpper n : ℝ)) ^ 2 := by
      unfold denominator
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_sub hu.le]
    calc
      finiteKnotMaximum (n + 1) = bellmanValue (finiteKnotMaximum n) := rfl
      _ ≤ bellmanValue ((roundedUpper n : ℝ) / (scale : ℝ)) := by
        unfold bellmanValue
        refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio.le (sub_le_sub_left ih 1) 2) (by norm_num)
      _ = ((numerator : ℝ) / (denominator (roundedUpper n) : ℝ)) / (scale : ℝ) := by
        rw [hdenom]
        unfold bellmanValue numerator
        push_cast
        field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hsR.le
        apply (div_le_iff₀ hdR).2
        rw [mul_comm]
        exact hcast

set_option maxRecDepth 65536 in
/-- The exact scalar maximum for 352 finite intervals is at most the displayed
bound. All 351 upward-rounded Bellman steps are checked by kernel reduction. -/
theorem finiteKnotMaximum_352_bound :
    finiteKnotMaximum 351 ≤ (1 : ℝ) / 3 - 4 / 3178 := by
  apply (roundedUpper_sound 351).trans
  have hs : (0 : ℝ) < scale := by norm_num [scale, thirdScale]
  have hcert : roundedUpper 351 * 9534 ≤ 3166 * scale := by decide
  have hcast : (roundedUpper 351 : ℝ) * 9534 ≤ 3166 * (scale : ℝ) := by
    exact_mod_cast hcert
  apply (div_le_iff₀ hs).2
  linarith only [hcast]

/-- The same certificate bounds all partitions with at most 352 intervals. -/
theorem finiteKnotMaximum_atMost352_bound {k : ℕ} (hk : k ≤ 351) :
    finiteKnotMaximum k ≤ (1 : ℝ) / 3 - 4 / 3178 := by
  have hmono : Monotone finiteKnotMaximum := monotone_nat_of_le_succ fun j => by
    have h := (bellman_maximum (finiteKnotMaximum_range j).2).1 1 (by norm_num) le_rfl
    simpa [finiteKnotMaximum] using h
  exact (hmono hk).trans finiteKnotMaximum_352_bound

end Cogentic.Randomized
