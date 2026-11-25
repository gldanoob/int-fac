import Cogentic.PolynomialSmooth
import Cogentic.EliminationUnits

namespace Cogentic.Construction
open Finset Marking

/-- The squarefree value divides the difference of any two retained marks
with equal incidence columns. On the construction grid the value is larger
than the entire mark interval, so distinct retained marks have distinct columns. -/
theorem constructed_columns_injective {n ell u v w z : ℕ}
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b)
    {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel) :
    Function.Injective (rel.matrix.map (Int.castRingHom ℚ)).col := by
  classical
  let s := TryPair.fixedInput n ell (construct n ell u v w z)
  have nd : rel.marks.Nodup := by
    simp only [Marking.stageOne] at stage
    split at stage <;> cases stage
    exact List.Nodup.filter _ (Finset.sort_nodup _ _)
  intro j k cols
  let a := rel.marks.get j; let b := rel.marks.get k
  let f := polynomial s.first
  let V := (f.eval (a:ℤ)).natAbs
  have points (i : Fin rel.marks.length) : rel.marks.get i ∈ (construct n ell u v w z).marks := by
    have elig := ((retained_iff stage _).mp (rel.marks.get_mem i)).1
    unfold Input.eligibleMarks at elig
    simp only [mem_sort,mem_filter,List.mem_toFinset] at elig
    exact elig.1
  have ag := (constructed_marks_iff ..).mp (points j)
  have bg := (constructed_marks_iff ..).mp (points k)
  have vlarge : Fixed.A (n.log2+1)<V := by
    have hv := (signed_box_value_size hn big target ag.2.1 ag.2.2.1 box false).2
    change Fixed.A (n.log2+1)<value s.first a at hv
    have eq : value s.first a=V := by simp only [value,horner_correct]; rfl
    exact eq ▸ hv
  have sf := ((stageOne_mark_primes stage false).1 j).2.1
  change Squarefree V at sf
  have rows := (rows_and_guards stage).2.2.2.1
  have mods (p : ℕ) (pm : p∈V.primeFactors) : a ≡ b [MOD p] := by
    obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp pm
    have hit : (p:ℤ)∣f.eval (a:ℤ) := Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using dvd)
    have mem : Row.mk false p (a%p)∈rel.rows := rows ▸ (stageOne_mark_primes stage false).2 p prime j hit
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp mem
    have val := congrFun cols i.succ
    change (↑(if a%(rel.rows.get i).q=(rel.rows.get i).r then (1:ℤ) else 0):ℚ)=
      ↑(if b%(rel.rows.get i).q=(rel.rows.get i).r then (1:ℤ) else 0) at val
    rw [hi] at val
    change a%p=b%p
    simp at val
    exact val.symm
  have factors := Finset.prod_dvd_of_coprime (t:=V.primeFactors) (s:=fun p : ℕ => (p:ℤ))
    (fun p hp q hq ne => ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr ne).isCoprime) (fun p hp => Nat.modEq_iff_dvd.mp (mods p hp))
  have prod : (∏ p∈V.primeFactors, (p:ℤ))=V := by
    rw [←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree sf]
  rw [prod] at factors
  have same := (Nat.modEq_iff_dvd.mpr factors).eq_of_lt_of_lt (ag.2.1.trans_lt vlarge) (bg.2.1.trans_lt vlarge)
  exact nd.injective_get same

end Cogentic.Construction
