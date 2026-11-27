import Cogentic.RandomizedReducedFormRoot
import Cogentic.RandomizedReductionSteps

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

private def shearIndex (a b : ℤ) : ℤ :=
  -((b + (a - 1) / 2) / a)

private def centeredTrailing (a b c : ℤ) : ℤ :=
  c + 2 * b * shearIndex a b + a * shearIndex a b ^ 2

private theorem centered_positive {a b c : ℤ} (ha : 0 < a)
    (hdisc : 0 < a * c - b ^ 2) :
    0 < centeredTrailing a b c ∧
      0 < a * centeredTrailing a b c - (b + a * shearIndex a b) ^ 2 := by
  have hs := (RandomizedReducedFormRoot.shear a b c (shearIndex a b) 0 0).1
  change (b + a * shearIndex a b) ^ 2 - a * centeredTrailing a b c =
    b ^ 2 - a * c at hs
  refine ⟨?_, by omega⟩
  by_contra! h
  have hprod := mul_nonpos_of_nonneg_of_nonpos ha.le h
  have hsq := sq_nonneg (b + a * shearIndex a b)
  omega

private def StrictSwapTrace (a b c : ℤ) (n : ℕ) : Prop :=
  ∃ lead : ℕ → ℕ, ∃ middle : ℕ → ℤ,
    lead 0 = a.toNat ∧
    (0 < n → lead 1 = (centeredTrailing a b c).toNat) ∧
    (∀ i < n, 0 < lead i) ∧
    (∀ i < n, |2 * middle i| ≤ (lead i : ℤ)) ∧
    (∀ i < n, lead (i + 1) < lead i) ∧
    (∀ i, i + 1 < n → ∃ k : ℤ,
      (lead (i + 2) : ℤ) = (lead i : ℤ) - 2 * k * middle i +
        k ^ 2 * (lead (i + 1) : ℤ))

private theorem emptyTrace (a b c : ℤ) : StrictSwapTrace a b c 0 := by
  refine ⟨fun _ => a.toNat, fun _ => 0, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem consTrace {a b c B C : ℤ} {n : ℕ}
    (ha : 0 < a) (hC : 0 < C) (hdown : C < a) (hcenter : |2 * B| ≤ a)
    (htrailing : C = centeredTrailing a b c) (hdisc : 0 < C * a - (-B) ^ 2)
    (tail : StrictSwapTrace C (-B) a n) : StrictSwapTrace a b c (n + 1) := by
  obtain ⟨lead, middle, hlead, hsucc, hpos, hmid, hswap, hnext⟩ := tail
  refine ⟨fun i => Nat.casesOn i a.toNat lead, fun i => Nat.casesOn i B middle,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    change lead 0 = (centeredTrailing a b c).toNat
    rw [hlead, htrailing]
  · intro i hi
    cases i with
    | zero =>
      change 0 < a.toNat
      omega
    | succ i => exact hpos i (by omega)
  · intro i hi
    cases i with
    | zero =>
      change |2 * B| ≤ (a.toNat : ℤ)
      simpa only [Int.toNat_of_nonneg ha.le] using hcenter
    | succ i => exact hmid i (by omega)
  · intro i hi
    cases i with
    | zero =>
      change lead 0 < a.toNat
      simpa only [hlead] using (Int.toNat_lt_toNat ha).2 hdown
    | succ i => exact hswap i (by omega)
  · intro i hi
    cases i with
    | zero =>
      let k := shearIndex C (-B)
      refine ⟨k, ?_⟩
      change (lead 1 : ℤ) = (a.toNat : ℤ) - 2 * k * B + k ^ 2 * (lead 0 : ℤ)
      rw [hsucc (by omega), hlead, Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hC.le,
        Int.toNat_of_nonneg (centered_positive hC hdisc).1.le]
      dsimp only [centeredTrailing, k]
      ring
    | succ i => exact hnext i (by omega)

private structure CountedResult (a b c : ℤ) where
  result : Result a b c
  strictSwaps : ℕ
  trace : StrictSwapTrace a b c strictSwaps

private def reduceCounted (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    CountedResult a b c := by
  let k := shearIndex a b
  let B := b + a * k
  let C := c + 2 * b * k + a * k ^ 2
  have hB : -a < 2 * B ∧ 2 * B ≤ a := by
    rw [show B = center a b from center_eq_shear.symm]
    exact center_bounds ha
  have hpositive : 0 < C ∧ 0 < a * C - B ^ 2 := centered_positive ha hdisc
  obtain ⟨hC, hCdisc⟩ := hpositive
  by_cases hdown : C < a
  · have hrotate : 0 < C * a - (-B) ^ 2 := by
      have hr := (RandomizedReducedFormRoot.rotate a B C 0 0).1
      omega
    let tail := reduceCounted C (-B) a hC hrotate
    have hcenter : |2 * B| ≤ a := abs_le.mpr ⟨hB.1.le, hB.2⟩
    exact ⟨undoShear k (undoRotate tail.result), tail.strictSwaps + 1,
      consTrace ha hC hdown hcenter rfl hrotate tail.trace⟩
  · by_cases htie : a = C ∧ B < 0
    · refine ⟨undoShear k (undoRotate (finish C (-B) a ?_)), 0, emptyTrace a b c⟩
      rcases htie with ⟨heq, hneg⟩
      rcases hB with ⟨hlo, hhi⟩
      refine ⟨hC, by omega, by omega, by omega, ?_⟩
      intro _
      omega
    · exact ⟨undoShear k (finish a B C ⟨ha, hB.1, hB.2, by omega, by omega⟩),
        0, emptyTrace a b c⟩
termination_by a.toNat
decreasing_by exact (Int.toNat_lt_toNat ha).2 hdown

/-- Gauss reduction in the half-middle coefficient convention. -/
def reduce (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) : Result a b c :=
  (reduceCounted a b c ha hdisc).result

/-- The number of strict swaps in the recursion computing the reduced form. -/
def strictSwapCount (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) : ℕ :=
  (reduceCounted a b c ha hdisc).strictSwaps

theorem strictSwapCount_le_log2 (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    strictSwapCount a b c ha hdisc ≤ a.toNat.log2 + 1 := by
  obtain ⟨lead, middle, hlead, _, hpos, hcenter, hswap, hnext⟩ :=
    (reduceCounted a b c ha hdisc).trace
  rw [← hlead]
  exact RandomizedReductionSteps.gauss_strict_swap_count_le_log2
    lead middle hpos hcenter hswap hnext

#print axioms strictSwapCount_le_log2

end Cogentic.RandomizedFormReduction
