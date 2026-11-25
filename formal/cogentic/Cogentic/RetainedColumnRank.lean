import Cogentic.NormCoordinates
import Cogentic.MarkIntervals
import Cogentic.ConstructionReduction
import Mathlib.Combinatorics.Pigeonhole

namespace Cogentic.Construction
open Finset Polynomial

/-- A binary matrix of rational rank r has a binary encoding of its
distinct columns using exactly r row coordinates. -/
theorem binary_row_signatures {I K : Type*} [Fintype I] [Fintype K] (A : Matrix I K ℚ)
    (binary : ∀ i j, A i j=0 ∨ A i j=1) :
    ∃ code : K→(Fin A.rank→Bool), ∀ j k, code j=code k → ∀ i, A i j=A i k := by
  classical
  let S := Set.range A.row
  obtain ⟨e,mem,span,_⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ S
  let h : A.rank=Module.finrank ℚ (Submodule.span ℚ S) := A.rank_eq_finrank_span_row
  let code := fun (j : K) (i : Fin A.rank) => decide (e (Fin.cast h i) j=1)
  refine ⟨code,?_⟩
  intro j k same i
  let D : Submodule ℚ (K→ℚ) :=
    { carrier := {v | v j=v k}
      zero_mem' := rfl
      add_mem' := fun hp hq => congrArg₂ (·+·) hp hq
      smul_mem' := fun c _ hp => congrArg (c*·) hp }
  have gen : Set.range e ⊆ D := by
    rintro _ ⟨idx,rfl⟩
    obtain ⟨row,hr⟩ := mem idx
    have bits := congrFun same (Fin.cast h.symm idx)
    change e idx j=e idx k
    simp only [code,Fin.cast_cast,Fin.cast_refl,decide_eq_decide] at bits
    have left : e idx j=0 ∨ e idx j=1 := hr ▸ binary row j
    have right : e idx k=0 ∨ e idx k=1 := hr ▸ binary row k
    grind
  have all : Submodule.span ℚ S ≤ D := by rw [←span]; exact Submodule.span_le.mpr gen
  exact all (Submodule.subset_span (Set.mem_range_self i))

private theorem incidence_binary (rel : Marking.Relations) :
    ∀ i j, (rel.matrix.map (Int.castRingHom ℚ)) i j=0 ∨ (rel.matrix.map (Int.castRingHom ℚ)) i j=1 := by
  let A := rel.matrix.map (Int.castRingHom ℚ)
  have binary (i j) : A i j=0 ∨ A i j=1 := by
    induction i using Fin.cases with
    | zero => exact Or.inr rfl
    | succ i => change (↑(if rel.marks.get j%(rel.rows.get i).q=(rel.rows.get i).r then (1:ℤ) else 0):ℚ)=0 ∨ _
                split <;> simp_all [A,Marking.Relations.matrix,Matrix.map_apply]
  exact binary

/-- For a stage-one matrix with distinct rational columns, its rank-r
binary row code separates every mark index. -/
theorem retained_rank_of_column_separation (rel : Marking.Relations)
    (inj : Function.Injective (rel.matrix.map (Int.castRingHom ℚ)).col) :
    rel.marks.length ≤ 2^(rel.matrix.map (Int.castRingHom ℚ)).rank := by
  let A := rel.matrix.map (Int.castRingHom ℚ)
  obtain ⟨code,determines⟩ := binary_row_signatures A (incidence_binary rel)
  have unique : Function.Injective code := fun j k eq => inj (funext (determines j k eq))
  simpa only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] using Fintype.card_le_of_injective code unique

/-- Equal incidence columns have equal absolute polynomial values at
that retained mark in either field. -/
theorem retained_values_eq_of_eq_col {s : Marking.Input} {rel : Marking.Relations}
    (stage : Marking.stageOne s=some rel) (side : Bool) (j k : Fin rel.marks.length)
    (col : ∀ i, rel.matrix i j=rel.matrix i k) :
    let f := Marking.polynomial (s.coeffs side)
    (f.eval (rel.marks.get j:ℤ)).natAbs=(f.eval (rel.marks.get k:ℤ)).natAbs := by
  intro f
  have left := retained_prime_log stage side j
  have right := retained_prime_log stage side k
  simp_rw [col] at left
  have eq := left.symm.trans right
  have nz := (stageOne_mark_primes stage side).1
  have pos (i : Fin rel.marks.length) : 0<((f.eval (rel.marks.get i:ℤ)).natAbs:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (nz i).1
  exact_mod_cast Real.log_injOn_pos (pos j) (pos k) eq

/-- At most 2d distinct integer arguments of a nonconstant polynomial
of degree d can have the same absolute value. -/
theorem card_equal_absolute_values {I : Type*} [Fintype I] (f : ℤ[X]) (degree : 0<f.natDegree)
    (a : I→ℤ) (inj : Function.Injective a) (v : ℤ) (same : ∀ i, (f.eval (a i)).natAbs=v.natAbs) :
    Fintype.card I ≤ 2*f.natDegree := by
  let g := f^2-C (v^2)
  have dg : g.natDegree=2*f.natDegree := by rw [show g=f^2-C (v^2) from rfl,natDegree_sub_C,natDegree_pow,Nat.mul_comm]
  by_contra! large
  have z : g=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero g inj (fun i => by
    simp only [g,eval_sub,eval_pow,eval_C,sub_eq_zero]
    exact Int.natAbs_eq_iff_sq_eq.mp (same i)) (dg ▸ large)
  rw [z,natDegree_zero] at dg
  omega

/-- The nonconstant first polynomial and the squarefree prime rows force a
lower bound on the rational rank from any finite set of distinct retained
marks in the actual stage-one output. -/
theorem retained_column_rank_bound {n ell u v w z : ℕ} (degree : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel)
    (Y : Finset ℕ) (retained : ∀ a∈Y, a∈rel.marks) :
    Y.card ≤ 2*Fixed.d (n.log2+1)*2^(rel.matrix.map (Int.castRingHom ℚ)).rank := by
  classical
  let A := rel.matrix.map (Int.castRingHom ℚ)
  obtain ⟨code,determines⟩ := binary_row_signatures A (incidence_binary rel)
  choose idx indices using fun a : Y => List.mem_iff_get.mp (retained a a.property)
  let colour := fun a : Y => code (idx a)
  let f := Marking.polynomial (construct n ell u v w z).first
  have dg : f.natDegree=Fixed.d (n.log2+1) := (constructed_rational_fields degree target u v w z).1.1
  have fg : 0<f.natDegree := by omega
  by_contra! large
  have exceeds : (univ : Finset (Fin A.rank→Bool)).card*(2*f.natDegree)<(univ : Finset Y).card := by
    simpa only [card_univ,Fintype.card_coe,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,dg,
      Nat.mul_comm (2^A.rank)] using large
  obtain ⟨c,_,hc⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun x (_ : x∈(univ : Finset Y)) => mem_univ (colour x)) exceeds
  let F := (univ : Finset Y).filter (fun x => colour x=c)
  change 2*f.natDegree < F.card at hc
  obtain ⟨base,hb⟩ := card_pos.mp ((Nat.zero_le _).trans_lt hc)
  let a := fun x : F => (x.val.val:ℤ)
  have inj : Function.Injective a := fun x y he => Subtype.ext (Subtype.ext (Int.natCast_inj.mp he))
  have same (x : F) : (f.eval (a x)).natAbs=(f.eval (base.val:ℤ)).natAbs := by
    have eq := (show colour x.val=c from (mem_filter.mp x.property).2).trans (show colour base=c from (mem_filter.mp hb).2).symm
    have cols := determines (idx x.val) (idx base) eq
    have vals := retained_values_eq_of_eq_col stage false (idx x.val) (idx base) (fun i => by
      have h : (rel.matrix i (idx x.val):ℚ)=(rel.matrix i (idx base):ℚ) := cols i
      exact_mod_cast h)
    change (f.eval (rel.marks.get (idx x.val):ℤ)).natAbs=(f.eval (rel.marks.get (idx base):ℤ)).natAbs at vals
    simpa only [indices] using vals
  exact hc.not_ge (by simpa only [Fintype.card_coe] using card_equal_absolute_values f fg a inj _ same)

theorem retained_column_log2_le_rank {n ell u v w z : ℕ} (degree : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel)
    (Y : Finset ℕ) (retained : ∀ a∈Y, a∈rel.marks) :
    (Y.card/(2*Fixed.d (n.log2+1))).log2 ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank := by
  have bound := Nat.div_le_of_le_mul (retained_column_rank_bound degree target stage Y retained)
  by_cases zero : Y.card/(2*Fixed.d (n.log2+1))=0
  · simp [zero]
  · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.log2_self_le zero).trans bound)

/-- The retained cell population forces at least 3990 h independent
rational incidence rows, uniformly over admissible moduli up to B⁴. -/
theorem rank_of_retained_cell_count {n ell u v w z q : ℕ} (degree : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (qp : 0<q) (cap : q≤(Fixed.B (n.log2+1))^4)
    {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel)
    (Y : Finset ℕ) (retained : ∀ a∈Y, a∈rel.marks) :
    let b := n.log2+1
    (cellMarkCount b:ℝ)/(32*q*(Fixed.B b:ℝ)^2)≤Y.card → 3990*Fixed.h b≤(rel.matrix.map (Int.castRingHom ℚ)).rank := by
  intro b pop
  let d := Fixed.d b; let h := Fixed.h b; let B := Fixed.B b
  have dp : 0<d := (by decide : 0<3).trans_le degree
  have dh : d≤h := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hp := dp.trans_le dh
  have bp : 0<B := Nat.pow_pos (by decide)
  have dcap : d≤2^h := dh.trans (Nat.lt_two_pow_self (n:=h)).le
  have count : (2*d*2^(3990*h))*(32*q*B^2)≤cellMarkCount b := calc
    _ ≤ (2*2^h*2^(3990*h))*(32*B^4*B^2) := by gcongr
    _ = 2^(6+h+3990*h+2*(1000*h)+4*(1000*h)) := by
      change (2*2^h*2^(3990*h))*(32*(2^(1000*h))^4*(2^(1000*h))^2)=_
      rw [show (32:ℕ)=2^5 by decide,←pow_mul,←pow_mul]
      rw [show 2*2^h=2^(1+h) by rw [pow_add];simp]
      simp only [←pow_add]
      congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by change _≤9997*h;omega)
  have qpos : 0 < 32*(q:ℝ)*(B:ℝ)^2 := by positivity
  have low := (le_div_iff₀ qpos).mpr (show ((2*d*2^(3990*h):ℕ):ℝ)*(32*(q:ℝ)*(B:ℝ)^2) ≤ cellMarkCount b by exact_mod_cast count)
  have nat : 2*d*2^(3990*h) ≤ Y.card := by exact_mod_cast low.trans pop
  have upper := retained_column_rank_bound degree target stage Y retained
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (Nat.le_of_mul_le_mul_left (nat.trans upper) (Nat.mul_pos (by decide) dp))

end Cogentic.Construction

#print axioms Cogentic.Construction.rank_of_retained_cell_count
