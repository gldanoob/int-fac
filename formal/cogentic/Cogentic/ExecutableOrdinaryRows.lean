import Cogentic.OrdinaryMass

namespace Cogentic.Construction

open Finset Real
open scoped Classical
noncomputable section

/-- Row indexing for a subset of the executable on one coefficient draw. -/
structure BoxedOrdinaryRows (n ell : ℕ) (x y : ℤ×ℤ) (A : Finset Marking.Row) where
  row : ↥A ↪ ↥(admissibleOrdinaryRows n ell)
  row_eq (i : ↥A) : Marking.Row.mk (row i).val.1 (bandRowPrime (row i).val) (row i).val.2.2.val=i.val
  admitted (i : ↥A) : (row i).val∈admittedOrdinaryRows n ell x y

def executable_ordinary_rows {n ell : ℕ} (hn : 2≤n) (hd : 3≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (x y : ℤ×ℤ) (bx : inCoefficientBox n x) (by' : inCoefficientBox n y)
    (A : Finset Marking.Row)
    (sub : A⊆(TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)).rows.toFinset)
    (ordinary : ∀ i∈A,i.q≠ell) : BoxedOrdinaryRows n ell x y A := by
  let row := fun j : BandRow (n.log2+1)=>Marking.Row.mk j.1 (bandRowPrime j) j.2.2.val
  have choose (i : ↥A) : ∃ j∈admittedOrdinaryRows n ell x y, row j=i.val := by
    apply mem_image.mp
    rw [admitted_ordinary_rows_eq hn hd composite target sieved x y bx by']
    exact mem_filter.mpr ⟨sub i.prop,ordinary i.val i.prop⟩
  choose j mem eq using choose
  let emb := fun i : ↥A=>(⟨j i,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem i)).2.1⟩⟩ : ↥(admissibleOrdinaryRows n ell))
  refine ⟨⟨emb,?_⟩,eq,mem⟩
  intro a b h;apply Subtype.ext
  exact (eq a).symm.trans ((congrArg (fun i : ↥(admissibleOrdinaryRows n ell)=>row i.val) h).trans (eq b))

/-- Ordered pairs of executable rows whose primes differ. -/
def distinctOrdinaryRowPairs (A : Finset Marking.Row) : Finset (↥A×↥A) :=
  univ.filter (fun k=>k.1.val.q≠k.2.val.q)

theorem distinctOrdinaryRowPairs_sum (A : Finset Marking.Row) (f : ↥A→↥A→ℝ) :
    (∑ i : ↥A,∑ j : ↥A,if i.val.q≠j.val.q then f i j else 0) =
      ∑ k : ↥(distinctOrdinaryRowPairs A),f k.val.1 k.val.2 := by
  rw [sum_coe_sort (distinctOrdinaryRowPairs A) (fun k=>f k.1 k.2)]
  simp only [distinctOrdinaryRowPairs,sum_filter,Fintype.sum_prod_type]

namespace BoxedOrdinaryRows

variable {n ell : ℕ} {x y : ℤ×ℤ} {A : Finset Marking.Row} (rows : BoxedOrdinaryRows n ell x y A)

theorem prime (i : ↥A) : bandRowPrime (rows.row i).val=i.val.q := congrArg Marking.Row.q (rows.row_eq i)

def pair : ↥(distinctOrdinaryRowPairs A) ↪ ↥(admissibleOrdinaryPairs n ell) where
  toFun k := ⟨((rows.row k.val.1).val,(rows.row k.val.2).val),mem_filter.mpr
    ⟨mem_univ _,(mem_filter.mp (rows.row _).prop).2,(mem_filter.mp (rows.row _).prop).2,by
      rw [rows.prime,rows.prime];exact (mem_filter.mp k.prop).2⟩⟩
  inj' := by
    rintro k l h
    apply Subtype.ext; apply Prod.ext
    · exact rows.row.injective (Subtype.ext (congrArg (fun a : ↥(admissibleOrdinaryPairs n ell)=>a.val.1) h))
    · exact rows.row.injective (Subtype.ext (congrArg (fun a : ↥(admissibleOrdinaryPairs n ell)=>a.val.2) h))

private theorem restrict_sum {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (f : J→ℝ) (nn : ∀ j,0≤f j) :
    (∑ i,f (e i)) ≤ ∑ j,f j := by
  rw [←sum_map univ e f]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>nn j)

/-- On the boxed draw, the unrestricted physical scores on the chosen rows
are bounded by the cost on all admissible rows. -/
theorem single_cost (bx : inCoefficientBox n x) (by' : inCoefficientBox n y)
    (β : ℝ) (w : ↥(admissibleOrdinaryRows n ell)→ℕ→ℝ) :
    let O := PrescribedRows.unrestricted n ell
    let score := fun i=>twoFieldScore (univ.biUnion (constructorCellMarks n ell)) (w (rows.row i))
      (smoothMarkEvent O false) (smoothMarkEvent O true) x y
    (∑ i : ↥A,(i.val.q:ℝ)^(-β)*(score i)^2) ≤ boxedPhysicalSingleCost β w x y := by
  intro O score
  let f := fun i : ↥(admissibleOrdinaryRows n ell)=>(bandRowPrime i.val:ℝ)^(-β)*
    (boxedAdmittedScore (n:=n) (ell:=ell) (fun x y=>i.val∈admittedOrdinaryRows n ell x y) (w i) x y)^2
  have res := restrict_sum rows.row f (fun i=>mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
  change _ ≤ ∑ j,f j
  apply le_trans _ res
  apply le_of_eq
  apply sum_congr rfl;intro i _
  simp only [f,boxedAdmittedScore,bx,by',rows.admitted,true_and,if_true,rows.prime,score,O]

/-- The squared errors on all ordered pairs with distinct primes are paid
by the pair budget on the same coefficient draw. -/
theorem pair_cost (bx : inCoefficientBox n x) (by' : inCoefficientBox n y)
    (β : ℝ) (w : ↥(admissibleOrdinaryPairs n ell)→ℕ→ℝ) :
    let O := PrescribedRows.unrestricted n ell
    let score := fun k=>twoFieldScore (univ.biUnion (constructorCellMarks n ell)) (w (rows.pair k))
      (smoothMarkEvent O false) (smoothMarkEvent O true) x y
    (∑ k : ↥(distinctOrdinaryRowPairs A),(k.val.1.val.q:ℝ)^(-β)*(k.val.2.val.q:ℝ)^(-β)*(score k)^2)
      ≤ boxedPhysicalPairCost β w x y := by
  intro O score
  let f := fun k : ↥(admissibleOrdinaryPairs n ell)=>(bandRowPrime k.val.1:ℝ)^(-β)*(bandRowPrime k.val.2:ℝ)^(-β)*
    (boxedPhysicalPairScore k (w k) x y)^2
  have res := restrict_sum rows.pair f (fun k=>mul_nonneg
    (mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
  change _ ≤ ∑ j,f j
  apply le_trans _ res
  apply le_of_eq
  apply sum_congr rfl;intro k _
  have p₁ : (rows.pair k).val.1=(rows.row k.val.1).val := rfl
  have p₂ : (rows.pair k).val.2=(rows.row k.val.2).val := rfl
  simp only [f,boxedPhysicalPairScore,boxedAdmittedScore,p₁,p₂,bx,by',rows.admitted,
    true_and,if_true,rows.prime,score,O]

end BoxedOrdinaryRows
end
end Cogentic.Construction

#print axioms Cogentic.Construction.BoxedOrdinaryRows.single_cost
#print axioms Cogentic.Construction.BoxedOrdinaryRows.pair_cost
