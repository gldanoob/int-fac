import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

theorem quadratic_linearization (b r : ℤ) : (b+r)^2 = b^2+2*b*r+r^2 := by ring

/-- A short positive square yields a hit in the stated circular interval
after subtracting the quadratic error of the offset. -/
theorem linearized_square_in_cyclic_interval {N B X b r z : ℤ}
    (hz : z ≡ b+r [ZMOD N]) (hr₀ : 0 ≤ r) (hrB : r < B)
    (hlo : 1 ≤ z^2 % N) (hhi : z^2 % N ≤ X) :
    ∃ y : ℤ, -B^2 ≤ y ∧ y ≤ X ∧ b^2+2*b*r ≡ y [ZMOD N] := by
  have hr_sq : r^2 ≤ B^2 := pow_le_pow_left₀ hr₀ hrB.le _
  have hq := (Int.mod_modEq (z^2) N).symm
  have h := Int.ModEq.sub_right (r^2) ((hz.pow 2).symm.trans hq)
  refine ⟨z^2 % N-r^2, by omega, by nlinarith only [hhi, sq_nonneg r], ?_⟩
  simpa only [quadratic_linearization, add_sub_cancel_right] using h

/-- If the interval has width less than the modulus, it contains at most
one integer lift of any residue. -/
theorem linearized_cyclic_lift_unique {N B X y y' : ℤ} (hlen : B^2+X < N)
    (hlo : -B^2 ≤ y) (hhi : y ≤ X) (hlo' : -B^2 ≤ y') (hhi' : y' ≤ X)
    (heq : y ≡ y' [ZMOD N]) : y = y' := by
  have h := Int.ModEq.add_right (B^2) heq
  change (y+B^2)%N = (y'+B^2)%N at h
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

/-- The exact lattice shear changes the slope from twice the center to the
actual root and doubles the horizontal coordinate. -/
theorem quadratic_shear_modEq_iff {N b r z t h : ℤ} (hz : z ≡ b+r [ZMOD N]) :
    (h+2*r*t ≡ z*(2*t) [ZMOD N]) ↔ (h ≡ 2*b*t [ZMOD N]) := by
  have hz' : z*(2*t) ≡ 2*b*t+2*r*t [ZMOD N] := by
    convert hz.mul_right (2*t) using 1; ring
  exact ⟨fun h => Int.ModEq.add_right_cancel' (2*r*t) (h.trans hz'),
    fun h => (h.add_right (2*r*t)).trans hz'.symm⟩

theorem quadratic_shear_injective (r : ℤ) :
    Function.Injective (fun p : ℤ × ℤ => (2*p.1, p.2+2*r*p.1)) := by
  rintro ⟨t,h⟩ ⟨t',h'⟩ heq
  have ht : t = t' := by
    have hfst : 2*t = 2*t' := congrArg Prod.fst heq
    omega
  subst t'
  have hh : h+2*r*t = h'+2*r*t := congrArg Prod.snd heq
  rw [add_right_cancel hh]

/-- With `B² ≤ X`, the shear expands the squared Euclidean length in
the normalized coordinates by at most sixteen. -/
theorem quadratic_shear_scaled_sq_le {B X r : ℝ}
    (hB : 0 < B) (hBX : B^2 ≤ X) (hr₀ : 0 ≤ r) (hrB : r ≤ B) (t h : ℝ) :
    (2*t/B)^2+((h+2*r*t)/X)^2 ≤ 16*((t/B)^2+(h/X)^2) := by
  have hX : 0 < X := (pow_pos hB 2).trans_le hBX
  have hrBX : r*B ≤ X :=
    (mul_le_mul_of_nonneg_right hrB hB.le).trans (by simpa [pow_two] using hBX)
  let c := 2*r*B/X
  have hc₀ : 0 ≤ c := by dsimp [c]; positivity
  have hc₂ : c ≤ 2 := (div_le_iff₀ hX).mpr (by linarith only [hrBX])
  have hc_sq : c^2 ≤ 4 := by
    calc c^2 ≤ (2 : ℝ)^2 := pow_le_pow_left₀ hc₀ hc₂ 2
         _ = 4 := by norm_num
  have ht : 2*t/B = 2*(t/B) := by ring
  have hh : (h+2*r*t)/X = h/X+c*(t/B) := by dsimp [c]; field_simp
  rw [ht, hh]
  have hscale := mul_le_mul_of_nonneg_right hc_sq (sq_nonneg (t/B))
  nlinarith only [sq_nonneg (h/X-c*(t/B)), hscale, sq_nonneg (t/B), sq_nonneg (h/X)]

/-- In the length normalization used for shortest vectors, the shear
has Euclidean expansion at most four. -/
theorem quadratic_shear_scaled_norm_le {B X r : ℝ}
    (hB : 0 < B) (hBX : B^2 ≤ X) (hr₀ : 0 ≤ r) (hrB : r ≤ B) (t h : ℝ) :
    Real.sqrt ((2*t/B)^2+((h+2*r*t)/X)^2) ≤
      4*Real.sqrt ((t/B)^2+(h/X)^2) := by
  have hc : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), hc] using
    Real.sqrt_le_sqrt (quadratic_shear_scaled_sq_le hB hBX hr₀ hrB t h)

end Cogentic.Randomized
