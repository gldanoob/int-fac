import Cogentic.RandomizedReducedFormRoot

namespace Cogentic.RandomizedFormReduction

open RandomizedReducedFormRoot (formValue)

structure Result (a b c : ℤ) where
  A : ℤ
  B : ℤ
  C : ℤ
  x : ℤ
  y : ℤ
  u : ℤ
  v : ℤ
  reduced : 0 < A ∧ -A < 2 * B ∧ 2 * B ≤ A ∧ A ≤ C ∧ (A = C → 0 ≤ B)
  det : x * v - u * y = 1
  transform : ∀ s t : ℤ, formValue A B C s t =
    formValue a b c (x * s + u * t) (y * s + v * t)
  discriminant : B ^ 2 - A * C = b ^ 2 - a * c

/-- The first column gives the new leading coefficient. -/
theorem Result.first_column {a b c : ℤ} (r : Result a b c) :
    r.A = formValue a b c r.x r.y := by
  simpa [formValue] using r.transform 1 0

def center (a b : ℤ) : ℤ :=
  (b + (a - 1) / 2) % a - (a - 1) / 2

private theorem center_bounds {a b : ℤ} (ha : 0 < a) :
    -a < 2 * center a b ∧ 2 * center a b ≤ a := by
  unfold center
  have h₀ := Int.emod_nonneg (b + (a - 1) / 2) (Int.ne_of_gt ha)
  have h₁ := Int.emod_lt_of_pos (b + (a - 1) / 2) ha
  omega

private theorem center_eq_shear {a b : ℤ} :
    center a b = b + a * (-((b + (a - 1) / 2) / a)) := by
  unfold center
  rw [Int.mul_neg]
  have := Int.mul_ediv_add_emod (b + (a - 1) / 2) a
  omega

private def finish (a b c : ℤ)
    (hr : 0 < a ∧ -a < 2 * b ∧ 2 * b ≤ a ∧ a ≤ c ∧ (a = c → 0 ≤ b)) :
    Result a b c where
  A := a
  B := b
  C := c
  x := 1
  y := 0
  u := 0
  v := 1
  reduced := hr
  det := by decide
  transform := by simp
  discriminant := rfl

private def transport {a b c a' b' c' : ℤ} (r : Result a' b' c')
    (x y u v : ℤ) (hdet : x * v - u * y = 1)
    (htrans : ∀ s t : ℤ, formValue a' b' c' s t =
      formValue a b c (x * s + u * t) (y * s + v * t))
    (hdisc : b' ^ 2 - a' * c' = b ^ 2 - a * c) : Result a b c where
  A := r.A
  B := r.B
  C := r.C
  x := x * r.x + u * r.y
  y := y * r.x + v * r.y
  u := x * r.u + u * r.v
  v := y * r.u + v * r.v
  reduced := r.reduced
  det := by
    calc
      _ = (x * v - u * y) * (r.x * r.v - r.u * r.y) := by ring
      _ = 1 := by rw [hdet, r.det, one_mul]
  transform := by
    intro s t
    rw [r.transform, htrans]
    congr 1 <;> ring
  discriminant := r.discriminant.trans hdisc

private def undoShear {a b c : ℤ} (k : ℤ)
    (r : Result a (b + a * k) (c + 2 * b * k + a * k ^ 2)) : Result a b c :=
  transport r 1 0 k 1 (by simp)
    (fun s t => by simpa using (RandomizedReducedFormRoot.shear a b c k s t).2)
    (RandomizedReducedFormRoot.shear a b c k 0 0).1

private def undoRotate {a b c : ℤ} (r : Result c (-b) a) : Result a b c :=
  transport r 0 1 (-1) 0 (by simp)
    (fun s t => by simpa using (RandomizedReducedFormRoot.rotate a b c s t).2)
    (RandomizedReducedFormRoot.rotate a b c 0 0).1

/-- Gauss reduction in the half-middle coefficient convention. -/
def reduce (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) : Result a b c := by
  let k := -((b + (a - 1) / 2) / a)
  let B := b + a * k
  let C := c + 2 * b * k + a * k ^ 2
  have hB : -a < 2 * B ∧ 2 * B ≤ a := by
    rw [show B = center a b from center_eq_shear.symm]
    exact center_bounds ha
  have hCdisc : 0 < a * C - B ^ 2 := by
    have hs := (RandomizedReducedFormRoot.shear a b c k 0 0).1
    change B ^ 2 - a * C = b ^ 2 - a * c at hs
    omega
  have hC : 0 < C := by
    by_contra h
    have hz : a * C ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) (le_of_not_gt h)
    have hn : 0 ≤ B ^ 2 := sq_nonneg B
    omega
  apply undoShear k
  change Result a B C
  by_cases hdown : C < a
  · apply undoRotate
    exact reduce C (-B) a hC (by
      have hr := (RandomizedReducedFormRoot.rotate a B C 0 0).1
      omega)
  · by_cases htie : a = C ∧ B < 0
    · apply undoRotate
      exact finish C (-B) a (by
        rcases htie with ⟨heq, hneg⟩
        rcases hB with ⟨hlo, hhi⟩
        refine ⟨hC, by omega, by omega, by omega, ?_⟩
        intro _
        omega)
    · exact finish a B C ⟨ha, hB.1, hB.2, by omega, by omega⟩
termination_by a.toNat
decreasing_by exact (Int.toNat_lt_toNat ha).2 hdown

end Cogentic.RandomizedFormReduction
