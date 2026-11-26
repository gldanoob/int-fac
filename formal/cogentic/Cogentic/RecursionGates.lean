import Cogentic.SaturationCost
import Cogentic.IndexCapCost
import TwoThirdsFactor
import Cogentic.FixedSchedule

namespace Cogentic.BinaryRecursion
open TwoThirdsFactor BinaryDivision

/-- Charge for a restoring quotient at a split, or for copying the binary
prime to the output list at a leaf, including the branch and list link. -/
def nodeBudget (n : ℕ) := n.size*(20*n.size+1) + 3*n.size + 2

def quotient (n d : List Bool) : List Bool × ℕ :=
  let q := divide d n
  let c := BinarySaturation.canonical q.quotient
  (c.1,q.gates+c.2)

theorem split_quotient {n d : ℕ} (proper : 1 < d ∧ d < n) :
    (quotient n.bits d.bits).1 = (n / d).bits ∧ (quotient n.bits d.bits).2 + 2 ≤ nodeBudget n := by
  obtain ⟨q,_,cost⟩ := divide_naturals n d (by omega)
  obtain ⟨v,w⟩ := BinarySaturation.canonical_spec (divide d.bits n.bits).quotient
  have len := BinaryIndexCap.quotient_length d.bits n.bits
  have dw := Nat.size_le_size proper.2.le
  have upper : n.size*(10*(d.size+n.size)+1) ≤ n.size*(20*n.size+1) :=
    Nat.mul_le_mul_left _ (by omega)
  refine ⟨v.trans (congrArg Nat.bits q),?_⟩
  simp only [quotient,w,len,Nat.size_eq_bits_len,nodeBudget]
  exact Nat.add_le_add_right (Nat.add_le_add_right (cost.trans upper) _) _

private theorem two_le {n} (t : Run n) : 2 ≤ n := by
  induction t with
  | prime p h => exact h.1
  | @split a b l r hl hr => exact hl.trans (Nat.le_mul_of_pos_right _ (by omega))

/-- Accumulator traversal writes a leaf once. Its counter includes the local
quotient that formed the second child in the original factor recursion. -/
private def emitWords : {n : ℕ} → Run n → List Bool → List (List Bool) → List (List Bool) × ℕ
  | _, .prime _ _, input, acc => (input :: acc,input.length+2)
  | _, @Run.split a _ l r, input, acc =>
    let out := quotient input a.bits
    let right := emitWords r out.1 acc
    let left := emitWords l a.bits right.1
    (left.1, out.2 + 2 + left.2 + right.2)

def emit {n : ℕ} (t : Run n) := emitWords t n.bits

theorem emit_spec {n : ℕ} (t : Run n) (acc : List (List Bool)) :
    (emit t acc).1 = t.factors.map Nat.bits ++ acc ∧ (emit t acc).2 ≤ t.work nodeBudget := by
  induction t generalizing acc with
  | prime p h =>
    refine ⟨rfl,?_⟩
    change p.bits.length+2 ≤ nodeBudget p
    rw [Nat.size_eq_bits_len]
    unfold nodeBudget
    omega
  | @split a b l r hl hr =>
    obtain ⟨rv,rc⟩ := hr acc
    obtain ⟨lv,lc⟩ := hl (emit r acc).1
    have ap := two_le l
    have bp := two_le r
    have strict : a < a*b := by nlinarith only [Nat.mul_le_mul_left a bp,ap]
    obtain ⟨v,cost⟩ := split_quotient (n:=a*b) (d:=a) ⟨by omega,strict⟩
    rw [Nat.mul_div_cancel_left b (by omega : a>0)] at v
    unfold emit
    dsimp only [emitWords]
    rw [v]
    change (emit l (emit r acc).1).1 = _ ∧ _ + 2 + (emit l (emit r acc).1).2 + (emit r acc).2 ≤ _
    refine ⟨?_,Nat.add_le_add (Nat.add_le_add cost lc) rc⟩
    rw [lv,rv]
    simp only [Run.factors,List.map_append,List.append_assoc]

theorem budget_scale (n : ℕ) :
    nodeBudget n ≤ 2^(10*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  have zle : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans
    ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans (Fixed.scale_bounds (Nat.succ_pos _)).1)
  have sp : 0<S := (Nat.succ_pos _).trans_le zle
  have bw : n.size≤2^S := by
    have baseWidth : n.size ≤ b := Nat.size_le.mpr Nat.lt_log2_self
    exact baseWidth.trans (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zle))
  have pw := Nat.two_pow_pos S
  calc
    nodeBudget n ≤ (2^S)*(20*(2^S)+1)+3*(2^S)+2 := by unfold nodeBudget; gcongr
    _ ≤ 32*(2^S)^2 := by nlinarith [Nat.mul_le_mul_left (2^S) pw]
    _ = 2^(5+S*2) := by rw [pow_add,pow_mul]; rfl
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 5+S*2 ≤ 10*S; omega)

end Cogentic.BinaryRecursion

#print axioms Cogentic.BinaryRecursion.split_quotient
#print axioms Cogentic.BinaryRecursion.emit_spec
#print axioms Cogentic.BinaryRecursion.budget_scale
