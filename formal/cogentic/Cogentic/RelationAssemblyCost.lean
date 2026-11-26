import Cogentic.CandidateRuntime
import Cogentic.SolverStageParameters

namespace Cogentic.BinaryRelations
open CandidateRuntime BinaryDivision Elimination Finset

private def entry (r : Marking.Row) (a : ℕ) : ℤ × ℕ :=
  let t := residueEq a.bits r.q.bits r.r.bits
  (if t.1 then 1 else 0,t.2+2)

private def constant (r : Marking.Row) (g : ℕ) : ℤ × ℕ :=
  let t := equalWords r.q.bits g.bits
  (if !r.second && t.1 then -1 else 0,t.2+3)

/-- Materialize the intercept and the congruence rows consumed by elimination. -/
def assemble (s : Marking.Relations) : List (Row s.marks.length) × ℕ :=
  let cell := fun (i : Fin s.rows.length) (j : Fin s.marks.length) =>
    entry (s.rows.get i) (s.marks.get j)
  let rhs := fun (i : Fin s.rows.length) => constant (s.rows.get i) s.target
  let data := List.ofFn fun i : Fin (s.rows.length+1) => Fin.cases
    (Row.mk (Vector.ofFn (fun _ => 1)) 0)
    (fun k => Row.mk (Vector.ofFn fun j => (cell k j).1) (rhs k).1) i
  (data,s.marks.length+2+∑ i,((rhs i).2+1+∑ j,(cell i j).2))

theorem assembled_rows {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) :
    (assemble rel).1=relationRows rel ∧
      (assemble rel).2≤2^(200000*TwoThirdsCost.scale (n.log2+1)) := by
  let s := TryPair.fixedInput n g pair
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  let W := 2^(30000*S)
  obtain ⟨pos,m,rows,_,_⟩ := SolverStage.fixed_parameters stage
  change 0<S at pos
  change rel.marks.length≤W at m
  change rel.rows.length+1≤W at rows
  obtain ⟨_,target,te,clean,_⟩ := Marking.rows_and_guards stage
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans
    (Fixed.scale_bounds (Nat.succ_pos _)).1
  have A : s.A≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by change 10000*Fixed.h b ≤ 30000*S; omega)
  have B : s.B≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by change 1000*Fixed.h b ≤ 30000*S; omega)
  have bitlen {a : ℕ} (h : a≤W) : a.bits.length≤W := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans h
  have gw := bitlen ((Marking.mem_base.mp target).2.2.1.trans B)
  have gw' : rel.target.bits.length≤W := te ▸ gw
  have tested (i : Fin rel.rows.length) (j : Fin rel.marks.length) :=
    let r := rel.rows.get i
    let a := rel.marks.get j
    show (entry r a).1 = (if a%r.q=r.r then 1 else 0) ∧
      (entry r a).2≤W*(20*W+1)+28*W+6 from by
      have cleanRow : r∈s.clean := clean ▸ rel.rows.get_mem i
      have h := Marking.mem_rows.mp (Marking.mem_clean.mp cleanRow).1
      have prime := (Marking.mem_base.mp h.1).2.1
      have q := (Marking.mem_base.mp h.1).2.2.1.trans B
      have ha := ((Marking.retained_iff stage a).mp (rel.marks.get_mem j)).1
      simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter] at ha
      have qp : 0<value r.q.bits := by simpa only [value_bits] using prime.pos
      obtain ⟨eq,work⟩ := residue_spec a.bits r.q.bits r.r.bits qp W (bitlen (ha.2.2.1.trans A))
        (bitlen q) (bitlen (h.2.1.le.trans q))
      simp only [value_bits] at eq
      refine ⟨by simp only [entry,eq],by dsimp only [entry]; omega⟩
  have rhsSpec (i : Fin rel.rows.length) :
      (constant (rel.rows.get i) rel.target).1 = -rel.rhs i.succ ∧
      (constant (rel.rows.get i) rel.target).2≤14*W+6 := by
    let r := rel.rows.get i
    have cleanRow : r∈s.clean := clean ▸ rel.rows.get_mem i
    have q := (Marking.mem_base.mp (Marking.mem_rows.mp (Marking.mem_clean.mp cleanRow).1).1).2.2.1.trans B
    obtain ⟨eq,cost⟩ := equalWords_spec r.q.bits rel.target.bits
    simp only [value_bits] at eq
    have same : (equalWords r.q.bits rel.target.bits).1 = (r.q == rel.target) := by
      exact Bool.eq_iff_iff.mpr (eq.trans beq_iff_eq.symm)
    change (constant r rel.target).1 = -rel.rhs i.succ ∧ (constant r rel.target).2 ≤ _
    simp only [Marking.Relations.rhs,Fin.cases_succ,constant,same,cost]
    constructor
    · change (if !r.second && (r.q == rel.target) then -1 else 0) =
        -(if !r.second && (r.q == rel.target) then 1 else 0)
      split <;> decide
    · have bound := max_le (bitlen q) gw'
      omega
  constructor
  · apply congrArg List.ofFn
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [Marking.Relations.matrix,Marking.Relations.rhs]
    · simp only [Fin.cases_succ]
      rw [(rhsSpec k).1]
      congr 1
      apply congrArg Vector.ofFn
      funext j
      exact (tested k j).1
  · let C := W*(20*W+1)+28*W+6
    have perRow (i : Fin rel.rows.length) :
        (constant (rel.rows.get i) rel.target).2+1+
          (∑ j : Fin rel.marks.length, (entry (rel.rows.get i) (rel.marks.get j)).2)≤14*W+7+W*C := by
      have all := sum_le_sum (s:=univ) (fun j _ => (tested i j).2)
      simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at all
      have inner := all.trans (Nat.mul_le_mul_right C m)
      have head := (rhsSpec i).2
      omega
    have all := sum_le_sum (s:=univ) (fun i _ => perRow i)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at all
    have body := all.trans (Nat.mul_le_mul_right _ (Nat.le_of_succ_le rows))
    have pw : 0<W := Nat.two_pow_pos _
    calc
      (assemble rel).2 ≤ W+2+W*(14*W+7+W*C) := Nat.add_le_add (Nat.add_le_add_right m 2) body
      _ ≤ 128*W^4 := by dsimp only [C]; nlinarith [Nat.le_self_pow (n:=2) (by decide) W,
        Nat.pow_le_pow_right pw (by decide : 2≤4), Nat.pow_le_pow_right pw (by decide : 3≤4)]
      _ = 2^(7+30000*S*4) := by rw [pow_add, pow_mul 2 (30000*S) 4]; rfl
      _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 7+30000*S*4≤200000*S; omega)

end Cogentic.BinaryRelations

#print axioms Cogentic.BinaryRelations.assembled_rows
