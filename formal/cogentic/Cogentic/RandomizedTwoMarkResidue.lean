import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

/-- Integer evaluation of a homogeneous form, with the coefficient of
`X^(d-i)Y^i` stored at index `i`. -/
def homogeneousFormEval (d : ℕ) (c : ℕ → ℤ) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), c i*a^(d-i)*b^i

/-- Reducing at the denominator leaves precisely the top coefficient term. -/
theorem homogeneousFormEval_modEq_top (d : ℕ) (c : ℕ → ℤ) (a b : ℤ) :
    homogeneousFormEval d c a b ≡ c 0*a^d [ZMOD b] := by
  rw [homogeneousFormEval, Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, mul_one, Int.add_modEq_right_iff]
  apply Finset.dvd_sum
  intro i _
  refine ⟨c (i+1)*a^(d-(i+1))*b^i, ?_⟩
  rw [pow_succ]
  ring

/-- Equal values at a primitive mark fix the top coefficient modulo the
denominator of that mark. -/
theorem homogeneous_top_sub_dvd_of_mark_eq {d : ℕ} {c c' : ℕ → ℤ} {a b : ℤ}
    (hcop : Int.gcd a b = 1) (heq : homogeneousFormEval d c a b = homogeneousFormEval d c' a b) :
    b ∣ c' 0-c 0 := by
  have hm : c 0*a^d ≡ c' 0*a^d [ZMOD b] :=
    (homogeneousFormEval_modEq_top d c a b).symm.trans
      (heq ▸ homogeneousFormEval_modEq_top d c' a b)
  have hd : b ∣ (c' 0-c 0)*a^d := by
    rw [sub_mul]
    exact Int.modEq_iff_dvd.mp hm
  have hpow : IsCoprime b (a^d) := (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm.pow_right
  exact hpow.dvd_of_dvd_mul_right hd

/-- Equal values at two primitive marks with coprime denominators fix
the top coefficient modulo the product of the denominators. -/
theorem homogeneous_top_sub_dvd_of_two_marks_eq {d : ℕ} {c c' : ℕ → ℤ}
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : Int.gcd a₁ b₁ = 1) (h₂ : Int.gcd a₂ b₂ = 1)
    (hb : Int.gcd b₁ b₂ = 1)
    (he₁ : homogeneousFormEval d c a₁ b₁ = homogeneousFormEval d c' a₁ b₁)
    (he₂ : homogeneousFormEval d c a₂ b₂ = homogeneousFormEval d c' a₂ b₂) :
    b₁*b₂ ∣ c' 0-c 0 :=
  (Int.isCoprime_iff_gcd_eq_one.mpr hb).mul_dvd
    (homogeneous_top_sub_dvd_of_mark_eq h₁ he₁)
    (homogeneous_top_sub_dvd_of_mark_eq h₂ he₂)

/-- Coefficients of the product of the two vanishing linear forms,
padded by a power of the first variable. -/
def twoMarkVanishingCoeffs (a₁ b₁ a₂ b₂ : ℤ) (i : ℕ) : ℤ :=
  if i = 0 then b₁*b₂ else if i = 1 then -(a₁*b₂+a₂*b₁) else if i = 2 then a₁*a₂ else 0

@[simp] theorem twoMarkVanishingCoeffs_top (a₁ b₁ a₂ b₂ : ℤ) :
    twoMarkVanishingCoeffs a₁ b₁ a₂ b₂ 0 = b₁*b₂ := rfl

theorem twoMarkVanishingCoeffs_eval (k : ℕ) (a₁ b₁ a₂ b₂ a b : ℤ) :
    homogeneousFormEval (k+2) (twoMarkVanishingCoeffs a₁ b₁ a₂ b₂) a b =
      a^k*(b₁*a-a₁*b)*(b₂*a-a₂*b) := by
  rw [homogeneousFormEval, Finset.sum_range_succ' _ (k+2),
    Finset.sum_range_succ' _ (k+1), Finset.sum_range_succ' _ k]
  have hz :
      (∑ i ∈ Finset.range k, twoMarkVanishingCoeffs a₁ b₁ a₂ b₂ (i+1+1+1) *
        a^(k+2-(i+1+1+1))*b^(i+1+1+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have h₂ : i+1+1+1 ≠ 2 := by omega
    simp [twoMarkVanishingCoeffs, h₂]
  rw [hz]
  simp [twoMarkVanishingCoeffs, pow_succ]
  ring

private theorem homogeneousFormEval_shift (d : ℕ) (c e : ℕ → ℤ) (k a b : ℤ) :
    homogeneousFormEval d (fun i => c i+k*e i) a b =
      homogeneousFormEval d c a b+k*homogeneousFormEval d e a b := by
  simp only [homogeneousFormEval, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- In degree at least two, the permitted top coefficients for the same
pair of marked values are exactly the congruence class modulo the product. -/
theorem homogeneous_two_mark_top_class_iff {d : ℕ} (hd : 2 ≤ d) (c : ℕ → ℤ)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : Int.gcd a₁ b₁ = 1) (h₂ : Int.gcd a₂ b₂ = 1)
    (hb : Int.gcd b₁ b₂ = 1) (top : ℤ) :
    (∃ c' : ℕ → ℤ, c' 0 = top ∧
      homogeneousFormEval d c a₁ b₁ = homogeneousFormEval d c' a₁ b₁ ∧
      homogeneousFormEval d c a₂ b₂ = homogeneousFormEval d c' a₂ b₂) ↔
      c 0 ≡ top [ZMOD b₁*b₂] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨c', rfl, he₁, he₂⟩
    exact homogeneous_top_sub_dvd_of_two_marks_eq h₁ h₂ hb he₁ he₂
  · rintro ⟨k, hk⟩
    let e := twoMarkVanishingCoeffs a₁ b₁ a₂ b₂
    have hde : d = (d-2)+2 := (Nat.sub_add_cancel hd).symm
    have hv₁ : homogeneousFormEval d e a₁ b₁ = 0 := by
      rw [hde, twoMarkVanishingCoeffs_eval]
      ring
    have hv₂ : homogeneousFormEval d e a₂ b₂ = 0 := by
      rw [hde, twoMarkVanishingCoeffs_eval]
      ring
    refine ⟨fun i => c i+k*e i, ?_, ?_, ?_⟩
    · change c 0+k*(b₁*b₂) = top
      calc
        c 0+k*(b₁*b₂) = (b₁*b₂)*k+c 0 := by ring
        _ = top := by rw [← hk, sub_add_cancel]
    · rw [homogeneousFormEval_shift, hv₁, mul_zero, add_zero]
    · rw [homogeneousFormEval_shift, hv₂, mul_zero, add_zero]

end Cogentic.Randomized
