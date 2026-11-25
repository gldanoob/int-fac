import Cogentic.Marking
import Mathlib.Topology.Order.IntermediateValue

namespace Cogentic.Bisection
open Set

structure Bracket where
  left : ℚ
  right : ℚ
deriving Repr, DecidableEq

def Bracket.mid (b : Bracket) : ℚ := (b.left+b.right)/2

def halve (f : ℚ → ℚ) (b : Bracket) : Bracket :=
  if f b.left * f b.mid ≤ 0 then ⟨b.left,b.mid⟩ else ⟨b.mid,b.right⟩

def refine (f : ℚ → ℚ) : ℕ → Bracket → Bracket
  | 0,b => b
  | k+1,b => refine f k (halve f b)

private theorem halve_spec (f : ℚ → ℚ) {b : Bracket}
    (ordered : b.left ≤ b.right) (sign : f b.left*f b.right ≤ 0) :
    let c := halve f b
    b.left ≤ c.left ∧ c.left ≤ c.right ∧ c.right ≤ b.right ∧
      f c.left*f c.right ≤ 0 ∧ c.right-c.left = (b.right-b.left)/2 := by
  have lo : b.left ≤ b.mid := by dsimp [Bracket.mid]; linarith
  have hi : b.mid ≤ b.right := by dsimp [Bracket.mid]; linarith
  dsimp only [halve]
  split
  next h => exact ⟨le_rfl,lo,hi,h,by dsimp [Bracket.mid]; ring⟩
  next h =>
    have cross : f b.mid*f b.right ≤ 0 := by
      rcases (mul_pos_iff.mp (lt_of_not_ge h)) with both | both
      · exact mul_nonpos_of_nonneg_of_nonpos both.2.le (nonpos_of_mul_nonpos_right sign both.1)
      · exact mul_nonpos_of_nonpos_of_nonneg both.2.le (nonneg_of_mul_nonpos_right sign both.1)
    exact ⟨lo,hi,le_rfl,cross,by dsimp [Bracket.mid]; ring⟩

theorem refine_spec (f : ℚ → ℚ) (bits : ℕ) {b : Bracket}
    (ordered : b.left ≤ b.right) (sign : f b.left*f b.right ≤ 0) :
    let c := refine f bits b
    b.left ≤ c.left ∧ c.left ≤ c.right ∧ c.right ≤ b.right ∧
      f c.left*f c.right ≤ 0 ∧ c.right-c.left = (b.right-b.left)/(2:ℚ)^bits := by
  induction bits generalizing b with
  | zero => exact ⟨le_rfl,ordered,le_rfl,sign,by simp [refine]⟩
  | succ k ih =>
    obtain ⟨outerL,inside,outerR,nextSign,width⟩ := halve_spec f ordered sign
    obtain ⟨l,o,r,s,small⟩ := ih inside nextSign
    exact ⟨outerL.trans l,o,r.trans outerR,s,by simpa only [refine,small,width,pow_succ,div_div] using
      (show (b.right-b.left)/(2*2^k)=(b.right-b.left)/(2^k*2) by ring)⟩

/-- The rational midpoint approximates an actual root of the continuous
    extension in the original sign-changing bracket. This also handles exact
    midpoint and endpoint roots without extra search. -/
theorem midpoint_near_root (f : ℚ → ℚ) (F : ℝ → ℝ) (continuous : Continuous F)
    (eval : ∀ x : ℚ, F x = (f x:ℝ)) {b : Bracket} (bits : ℕ)
    (ordered : b.left ≤ b.right) (sign : f b.left*f b.right ≤ 0) :
    ∃ root ∈ Icc (b.left:ℝ) (b.right:ℝ), F root = 0 ∧
      |((refine f bits b).mid:ℝ)-root| ≤ ((b.right:ℝ)-b.left)/(2:ℝ)^(bits+1) := by
  let c := refine f bits b
  obtain ⟨l,o,r,s,w⟩ := refine_spec f bits ordered sign
  change b.left ≤ c.left at l
  change c.left ≤ c.right at o
  change c.right ≤ b.right at r
  change f c.left*f c.right ≤ 0 at s
  change c.right-c.left = _ at w
  have order : (c.left:ℝ) ≤ c.right := by exact_mod_cast o
  have hasRoot : ∃ y ∈ Icc (c.left:ℝ) (c.right:ℝ), F y = 0 := by
    rcases mul_nonpos_iff.mp s with h | h
    · exact intermediate_value_Icc' order continuous.continuousOn (by
        exact ⟨(eval c.right).trans_le (by exact_mod_cast h.2),
          (by exact_mod_cast h.1 : 0 ≤ (f c.left:ℝ)).trans_eq (eval c.left).symm⟩)
    · exact intermediate_value_Icc order continuous.continuousOn (by
        exact ⟨(eval c.left).trans_le (by exact_mod_cast h.1),
          (by exact_mod_cast h.2 : 0 ≤ (f c.right:ℝ)).trans_eq (eval c.right).symm⟩)
  obtain ⟨y,⟨yl,yr⟩,eq⟩ := hasRoot
  refine ⟨y,⟨(by exact_mod_cast l : (b.left:ℝ) ≤ c.left).trans yl,
    yr.trans (by exact_mod_cast r)⟩,eq,?_⟩
  have wid : (c.right:ℝ)-c.left = ((b.right:ℝ)-b.left)/(2:ℝ)^bits := by exact_mod_cast w
  change |(c.mid:ℝ)-y| ≤ _
  rw [Bracket.mid,pow_succ,← div_div,← wid]
  push_cast
  rw [abs_le]; constructor <;> linarith

end Cogentic.Bisection
