import Std

namespace ThreeSquareShell

private theorem sq_le_sq {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : a^2 ≤ b^2 := by
  simpa [Int.pow_succ] using Int.mul_le_mul hab hab ha (by omega : 0 ≤ b)

private theorem coefficient_eq {B q k : Int} (hB : 0 < B)
    (lo : B * (k - 1) < B * q) (hi : B * q < B * (k + 1)) : q = k := by
  have := (Int.mul_lt_mul_left hB).mp lo
  have := (Int.mul_lt_mul_left hB).mp hi
  omega

/-- Membership in the half-open shell for integer points in the stated clipping box. -/
theorem clipped_shell_iff {n x y t : Int} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hx : 2 ≤ x) (hxn : x ≤ n / 2) (hy : 0 ≤ y) (hyn : y ≤ n^2)
    (ht : 0 ≤ t) (htn : t ≤ n) :
    let A := n^2 + 1
    let H := A^2
    let L := n * A / 2
    let C := A * H^2 + L^2
    let X := n * H + x
    let Y := H - y
    let Z := L - t
    C + A ≤ X^2 + Y^2 + Z^2 ∧ X^2 + Y^2 + Z^2 < C + 2 * A ↔
      y = n * x ∧ x^2 - n * t = 1 := by
  intro A H L C X Y Z
  have hA : 0 < A := by dsimp [A]; grind [Int.sq_nonneg]
  have hAH : A ≤ H := by
    simpa [H, Int.pow_succ] using
      Int.mul_le_mul_of_nonneg_left (show 1 ≤ A by omega) (by omega : 0 ≤ A)
  have hL : 2 * L = n * A := by
    have even : (n * A) % 2 = 0 := by
      rw [Int.mul_emod, show A = n * n + 1 by simp [A, Int.pow_succ],
        Int.add_emod, Int.mul_emod n n, hodd]
      decide
    dsimp [L]; omega
  let R := x^2 + y^2 + t^2 - A * n * t
  have hsum : X^2 + Y^2 + Z^2 - C = 2 * H * (n * x - y) + R := by
    have := congrArg (· * t) hL
    dsimp only [X, Y, Z, C, R, A]
    grind
  have hx2 := sq_le_sq (by omega : 0 ≤ x) (by omega : x ≤ n)
  have hy2 := sq_le_sq hy hyn
  have ht2 := sq_le_sq ht htn
  have hAn := Int.mul_nonneg (by omega : 0 ≤ A) (by omega : 0 ≤ n)
  have tlo := Int.sq_nonneg t
  have rlo : A - H ≤ R := by
    have := Int.mul_le_mul_of_nonneg_left htn hAn
    have := Int.sq_nonneg x
    have := Int.sq_nonneg y
    dsimp only [R, H, A] at *
    grind
  have rhi : R < H := by
    have := Int.mul_nonneg hAn ht
    dsimp only [R, H, A] at *
    grind
  have aligned (yx : y = n * x) : X^2 + Y^2 + Z^2 - C = A * (x^2 - n * t) + t^2 := by
    rw [hsum]
    dsimp only [R, A]
    rw [yx]
    grind
  have thi : t^2 < A := by dsimp [A]; omega
  constructor
  · intro ⟨lo, hi⟩
    have gap : n * x - y = 0 := coefficient_eq (B := 2 * H) (by omega) (by omega) (by omega)
    have yx : y = n * x := by omega
    have := aligned yx
    exact ⟨yx, coefficient_eq hA (by omega) (by omega)⟩
  · rintro ⟨yx, hxt⟩
    have h := aligned yx
    rw [hxt, Int.mul_one] at h
    omega

end ThreeSquareShell
