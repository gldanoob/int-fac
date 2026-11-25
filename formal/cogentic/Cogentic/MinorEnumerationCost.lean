import Cogentic.Concrete
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! The number of recursive calls used by `List.sublistsLenAux`, which is
how the candidate minor search constructs its list of column sets. -/
namespace Cogentic.MinorEnumeration
open Finset

/-- The library enumerator with one visit recorded at each invocation. -/
def counted {α β : Type*} : ℕ → List α → (List α → β) → List β → List β × ℕ
  | 0, _, f, r => (f [] :: r,1)
  | _+1, [], _, r => (r,1)
  | k+1, a::l, f, r =>
    let inner := counted k l (f ∘ List.cons a) r
    let outer := counted (k+1) l f inner.1
    (outer.1,1+inner.2+outer.2)

private def leaves (f k : ℕ) := ∑ i ∈ range (k+1), f.choose i

private theorem leaves_step (f k : ℕ) : leaves (f+1) (k+1) = leaves f k+leaves f (k+1) := by
  have e (x : ℕ) : leaves x (k+1) = (∑ i ∈ range (k+1), x.choose (i+1))+1 := by
    simp only [leaves,sum_range_succ',Nat.choose_zero_right]
  rw [e,e]
  simp only [Nat.choose_succ_succ,Finset.sum_add_distrib,leaves,Nat.succ_eq_add_one]
  omega

/-- The instrumented result agrees with the actual library list, and its call
count includes terminal branches which emit nothing. -/
theorem counted_spec {α β : Type*} (k : ℕ) (l : List α) (f : List α → β) (r : List β) :
    (counted k l f r).1 = List.sublistsLenAux k l f r ∧
    (counted k l f r).2+1 = 2*∑ i ∈ range (k+1), l.length.choose i := by
  change _ ∧ _ = 2*leaves _ _
  induction l generalizing k f r with
  | nil => cases k with
    | zero => simp [counted,List.sublistsLenAux,leaves]
    | succ k => simp [counted,List.sublistsLenAux,leaves,sum_range_succ']
  | cons a l ih => cases k with
    | zero => simp [counted,List.sublistsLenAux,leaves]
    | succ k =>
      have inner := ih k (f ∘ List.cons a) r
      have outer := ih (k+1) f (counted k l (f ∘ List.cons a) r).1
      refine ⟨?_,?_⟩
      · change (counted (k+1) l f (counted k l (f ∘ List.cons a) r).1).1 = List.sublistsLenAux (k+1) l f (List.sublistsLenAux k l (f ∘ List.cons a) r)
        rw [outer.1,inner.1]
      · simp only [counted,List.length_cons,leaves_step]
        omega

/-- In particular there is no hidden enumeration of all 2^f subsets when
only k columns are requested. The bound includes all failed recursion branches. -/
theorem selection_visit_bound (k f : ℕ) :
    (counted k (List.finRange f) id []).1 = (List.finRange f).sublistsLen k ∧
    (counted k (List.finRange f) id []).2 ≤ 2*(k+1)*(f+1)^k := by
  obtain ⟨agree,eq⟩ := counted_spec k (List.finRange f) id []
  refine ⟨agree,?_⟩
  simp only [List.length_finRange] at eq
  have le : ∑ i ∈ range (k+1), f.choose i ≤ (k+1)*(f+1)^k := by
    calc
      _ ≤ ∑ _i ∈ range (k+1), (f+1)^k := by
        apply sum_le_sum
        intro i hi
        exact (Nat.choose_le_pow ..).trans ((Nat.pow_le_pow_left (Nat.le_succ f) i).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_of_lt_succ (mem_range.mp hi))))
      _ = _ := by simp
  rw [Nat.mul_assoc]
  omega

/-- All invocations of the recursive minor enumerator on an actual retained
relation system fit the fixed two-thirds scale. -/
theorem fixed_selection_visits {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (ok : Marking.stageOne (TryPair.fixedInput n g pair) = some rel) {free : ℕ}
    (guard : free < rel.marks.length) :
    let b := n.log2+1
    (counted (2*Fixed.d b-2) (List.finRange free) id []).2 ≤ 2^(20005*Fixed.v b) := by
  let b := n.log2+1
  change (counted (2*Fixed.d b-2) (List.finRange free) id []).2 ≤ 2^(20005*Fixed.v b)
  have dpos : 0 < Fixed.d b := Fixed.degree_pos (Nat.succ_pos n.log2)
  have hpos : 0 < Fixed.h b := Nat.mul_pos dpos (Nat.succ_pos _)
  have dv : Fixed.d b ≤ Fixed.v b := Nat.le_mul_of_pos_right _ hpos
  have vpos : 0 < Fixed.v b := Nat.mul_pos dpos hpos
  have fb : free ≤ Fixed.A b := guard.le.trans (Concrete.retained_size ok)
  have ap : 0 < Fixed.A b := by unfold Fixed.A; positivity
  have fle : free+1 ≤ 2^(10000*Fixed.h b+1) := by
    rw [pow_succ]; change free+1 ≤ Fixed.A b*2; omega
  let k := 2*Fixed.d b-2
  have kle : k≤2*Fixed.d b := Nat.sub_le ..
  have kexp : k+1 ≤ 2^(2*Fixed.d b) := Nat.succ_le_of_lt (kle.trans_lt Nat.lt_two_pow_self)
  calc
    _ ≤ 2*(k+1)*(free+1)^k := (selection_visit_bound ..).2
    _ ≤ 2*2^(2*Fixed.d b)*(2^(10000*Fixed.h b+1))^(2*Fixed.d b) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ kexp) ((Nat.pow_le_pow_left fle _).trans (Nat.pow_le_pow_right (by positivity) kle))
    _ = 2^(1+2*Fixed.d b+(10000*Fixed.h b+1)*(2*Fixed.d b)) := by rw [←pow_mul,pow_add,pow_add,pow_one]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      have ident : (10000*Fixed.h b+1)*(2*Fixed.d b) = 20000*Fixed.v b+2*Fixed.d b := by unfold Fixed.v; ring
      rw [ident]; omega

end Cogentic.MinorEnumeration

#print axioms Cogentic.MinorEnumeration.selection_visit_bound

#print axioms Cogentic.MinorEnumeration.fixed_selection_visits
