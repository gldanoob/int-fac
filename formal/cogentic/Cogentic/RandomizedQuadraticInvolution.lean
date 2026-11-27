import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

/-- Evaluate the binary quadratic with mixed coefficient (b). -/
def binaryQuadratic {R : Type*} [CommRing R] (a b c r q : R) : R :=
  a * r ^ 2 + b * r * q + c * q ^ 2

/-- The linear map associated with the three minors of a quadratic pencil. -/
def quadraticPencilMap {R : Type*} [CommRing R] (u v w r q : R) : R × R :=
  (-v * r - w * q, u * r + v * q)

theorem quadraticPencilMap_sq {R : Type*} [CommRing R] (u v w r q : R) :
    let j := quadraticPencilMap u v w r q
    quadraticPencilMap u v w j.1 j.2 = ((v ^ 2 - u * w) * r, (v ^ 2 - u * w) * q) := by
  dsimp [quadraticPencilMap]
  congr 1 <;> ring

theorem binaryQuadratic_pencilMap {R : Type*} [CommRing R] (a b c A B C r q : R) :
    let u := a * B - b * A
    let v := a * C - c * A
    let w := b * C - c * B
    let j := quadraticPencilMap u v w r q
    binaryQuadratic a b c j.1 j.2 = (v ^ 2 - u * w) * binaryQuadratic a b c r q ∧
    binaryQuadratic A B C j.1 j.2 = (v ^ 2 - u * w) * binaryQuadratic A B C r q := by
  dsimp [quadraticPencilMap, binaryQuadratic]
  constructor <;> ring

/-- Three division-free pencil identities give both coordinates at a common zero. -/
theorem quadraticPencilMap_eq_zero_of_common_zero {R : Type*} [CommRing R] [IsDomain R]
    (a b c A B C r q : R)
    (hh : binaryQuadratic a b c r q = 0) (hg : binaryQuadratic A B C r q = 0) :
    quadraticPencilMap (a * B - b * A) (a * C - c * A) (b * C - c * B) r q = (0, 0) := by
  let j := quadraticPencilMap (a * B - b * A) (a * C - c * A) (b * C - c * B) r q
  have hr : r * j.1 = 0 := by
    calc
      r * j.1 = c * binaryQuadratic A B C r q - C * binaryQuadratic a b c r q := by
        dsimp [j, quadraticPencilMap, binaryQuadratic]
        ring
      _ = 0 := by rw [hh, hg]; simp
  have hq : q * j.2 = 0 := by
    calc
      q * j.2 = a * binaryQuadratic A B C r q - A * binaryQuadratic a b c r q := by
        dsimp [j, quadraticPencilMap, binaryQuadratic]
        ring
      _ = 0 := by rw [hh, hg]; simp
  have hcross : r * j.2 + q * j.1 = 0 := by
    calc
      r * j.2 + q * j.1 = B * binaryQuadratic a b c r q - b * binaryQuadratic A B C r q := by
        dsimp [j, quadraticPencilMap, binaryQuadratic]
        ring
      _ = 0 := by rw [hh, hg]; simp
  change j = (0, 0)
  by_cases hr0 : r = 0
  · by_cases hq0 : q = 0
    · simp [j, quadraticPencilMap, hr0, hq0]
    · have hfirst : j.1 = 0 := by
        apply (mul_eq_zero.mp _).resolve_left hq0
        simpa [hr0] using hcross
      exact Prod.ext hfirst ((mul_eq_zero.mp hq).resolve_left hq0)
  · have hfirst := (mul_eq_zero.mp hr).resolve_left hr0
    have hsecond : j.2 = 0 := by
      apply (mul_eq_zero.mp _).resolve_left hr0
      simpa [hfirst] using hcross
    exact Prod.ext hfirst hsecond

theorem prime_dvd_quadraticPencilMap_of_dvd {p : ℕ} (hp : p.Prime)
    (a b c A B C r q : ℤ)
    (hh : (p : ℤ) ∣ binaryQuadratic a b c r q) (hg : (p : ℤ) ∣ binaryQuadratic A B C r q) :
    let j := quadraticPencilMap (a * B - b * A) (a * C - c * A) (b * C - c * B) r q
    (p : ℤ) ∣ j.1 ∧ (p : ℤ) ∣ j.2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hh' : binaryQuadratic (a : ZMod p) b c r q = 0 := by
    simpa only [binaryQuadratic, Int.cast_add, Int.cast_mul, Int.cast_pow] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hh
  have hg' : binaryQuadratic (A : ZMod p) B C r q = 0 := by
    simpa only [binaryQuadratic, Int.cast_add, Int.cast_mul, Int.cast_pow] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hg
  have hz := quadraticPencilMap_eq_zero_of_common_zero
      (a : ZMod p) b c A B C r q hh' hg'
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [quadraticPencilMap, Int.cast_neg, Int.cast_mul, Int.cast_sub] using congrArg Prod.fst hz
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [quadraticPencilMap, Int.cast_add, Int.cast_mul, Int.cast_sub] using congrArg Prod.snd hz

end Cogentic.Randomized
