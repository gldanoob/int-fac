import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedLinearPairCount

open Finset

/-- First coordinates of solutions to one linear equation share the residue
given by cancelling the coefficient modulo the second coefficient. -/
theorem modEq_fst_of_linear_eq {a b t x y x' y' : ℤ} (hb : 0 < b)
    (hxy : a * x - b * y = t) (hxy' : a * x' - b * y' = t) :
    x ≡ x' [ZMOD b / (b.gcd a : ℤ)] := by
  apply Int.ModEq.cancel_left_div_gcd hb
  apply Int.modEq_iff_dvd.mpr
  exact ⟨y' - y, by linarith only [hxy, hxy']⟩

/-- The integer gcd, returned as a natural number, commutes with squaring
both arguments. -/
theorem gcd_sq_sq (h k : ℤ) : (h ^ 2).gcd (k ^ 2) = (h.gcd k) ^ 2 := by
  by_cases hg : 0 < h.gcd k
  · obtain ⟨h₀, k₀, hcop, hh, hk⟩ := Int.exists_gcd_one hg
    have hcop' : (h₀ ^ 2).gcd (k₀ ^ 2) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ((Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow_left.pow_right)
    rw [show h ^ 2 = h₀ ^ 2 * (h.gcd k : ℤ) ^ 2 by rw [← mul_pow, ← hh],
      show k ^ 2 = k₀ ^ 2 * (h.gcd k : ℤ) ^ 2 by rw [← mul_pow, ← hk],
      Int.gcd_mul_right, hcop', one_mul, Int.natAbs_pow, Int.natAbs_natCast]
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp (by omega : h.gcd k = 0)
    rfl

theorem modEq_fst_of_square_linear_eq {h k t x y x' y' : ℤ} (hk : k ≠ 0)
    (hxy : h ^ 2 * x - k ^ 2 * y = t) (hxy' : h ^ 2 * x' - k ^ 2 * y' = t) :
    x ≡ x' [ZMOD k ^ 2 / ((k.gcd h : ℤ) ^ 2)] := by
  simpa only [gcd_sq_sq, Int.natCast_pow] using
    modEq_fst_of_linear_eq (sq_pos_of_ne_zero hk) hxy hxy'

/-- A finite set of solution pairs injects into an interval of quotients
of the first coordinate by the spacing modulus. No bound on the second
coordinate is needed. -/
theorem card_linear_solutions_le {a b t X : ℤ} (hb : 0 < b) (hX : 0 < X)
    (S : Finset (ℤ × ℤ))
    (hbox : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < X ∧ a * p.1 - b * p.2 = t) :
    (S.card : ℤ) ≤ 1 + (X - 1) / (b / (b.gcd a : ℤ)) := by
  let d : ℤ := b / (b.gcd a : ℤ)
  have hg : 0 < (b.gcd a : ℤ) := Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_left _ hb.ne')
  have hd : 0 < d := by
    have hone : 1 ≤ d := (Int.le_ediv_iff_mul_le hg).mpr
      (by simpa only [one_mul] using Int.le_of_dvd hb (Int.gcd_dvd_left b a))
    omega
  let Q := Icc (0 : ℤ) ((X - 1) / d)
  let f (p : ℤ × ℤ) := p.1 / d
  have hmap : Set.MapsTo f (S : Set (ℤ × ℤ)) (Q : Set ℤ) := by
    intro p hp
    obtain ⟨hp₀, hpX, _⟩ := hbox p hp
    exact mem_Icc.mpr ⟨Int.ediv_nonneg hp₀ hd.le, Int.ediv_le_ediv hd (by omega)⟩
  have hinj : Set.InjOn f (S : Set (ℤ × ℤ)) := by
    intro p hp q hq he
    have hx := (Int.ext_ediv_modEq_iff d p.1 q.1).mpr
      ⟨he, modEq_fst_of_linear_eq hb (hbox p hp).2.2 (hbox q hq).2.2⟩
    have hq' := (hbox q hq).2.2
    rw [← hx] at hq'
    have hy : b * (p.2 - q.2) = 0 := by linarith only [(hbox p hp).2.2, hq']
    exact Prod.ext hx (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hb.ne'))
  have hcard : (S.card : ℤ) ≤ Q.card := by
    exact_mod_cast card_le_card_of_injOn f hmap hinj
  have hQ := Int.card_Icc_of_le 0 ((X - 1) / d)
    (by have := Int.ediv_nonneg (show 0 ≤ X - 1 by omega) hd.le; omega)
  dsimp only [Q] at hcard
  rw [hQ] at hcard
  change _ ≤ 1 + (X - 1) / d
  omega

theorem card_linear_solutions_le_of_coprime {a b t X : ℤ} (hb : 0 < b) (hX : 0 < X)
    (hcop : a.gcd b = 1) (S : Finset (ℤ × ℤ))
    (hbox : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < X ∧ a * p.1 - b * p.2 = t) :
    (S.card : ℤ) ≤ 1 + (X - 1) / b := by
  simpa only [Int.gcd_comm b a, hcop, Int.natCast_one, Int.ediv_one] using
    card_linear_solutions_le hb hX S hbox

theorem card_square_linear_solutions_le {h k t X : ℤ} (hk : k ≠ 0) (hX : 0 < X)
    (S : Finset (ℤ × ℤ))
    (hbox : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < X ∧ h ^ 2 * p.1 - k ^ 2 * p.2 = t) :
    (S.card : ℤ) ≤ 1 + (X - 1) / (k ^ 2 / ((k.gcd h : ℤ) ^ 2)) := by
  simpa only [gcd_sq_sq, Int.natCast_pow] using
    card_linear_solutions_le (sq_pos_of_ne_zero hk) hX S hbox

#print axioms modEq_fst_of_linear_eq
#print axioms gcd_sq_sq
#print axioms modEq_fst_of_square_linear_eq
#print axioms card_linear_solutions_le
#print axioms card_linear_solutions_le_of_coprime
#print axioms card_square_linear_solutions_le

end Cogentic.RandomizedLinearPairCount
