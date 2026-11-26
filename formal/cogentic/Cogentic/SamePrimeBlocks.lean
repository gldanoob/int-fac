import Cogentic.CleanWindows
import Cogentic.ConstructionTarget

namespace Cogentic.Construction
open Finset Polynomial
open scoped Classical
noncomputable section

private theorem ordinary_leading_unit {n p : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (mem : p∈primeBand (n.log2+1)) : (leadingCoefficient n : ZMod p)≠0 := by
  let b := n.log2+1
  let d := Fixed.d b
  obtain ⟨pp,_,sq⟩ := mem_primeBand.mp mem
  change 3≤d at hd
  have dh : d≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have pow : (2^d)^2≤Fixed.B b := by
    rw [←Nat.pow_mul]; apply Nat.pow_le_pow_right (by decide)
    change d*2≤1000*Fixed.h b; omega
  have dp : d<p := by
    by_contra! small
    have cap := Nat.pow_le_pow_left (small.trans (Nat.lt_two_pow_self (n:=d)).le) 2
    exact sq.not_ge (cap.trans pow)
  have pd := pp.coprime_iff_not_dvd.mpr (fun h => dp.not_ge (pp.dvd_primorial_iff.mp h))
  have half := pd.symm.of_dvd_left (Nat.div_dvd_of_dvd (Nat.prime_two.dvd_primorial_iff.mpr (by omega : 2≤d)))
  have three : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three pp).mpr (by omega)
  have cop : (leadingCoefficient n).Coprime p := Nat.coprime_mul_iff_left.mpr ⟨half,three.pow_left _⟩
  exact fun z => (pp.coprime_iff_not_dvd.mp cop.symm) ((ZMod.natCast_eq_zero_iff ..).mp z)

/-- The actual row list contains at most two degree-many residues of each
ordinary prime across the two fields, on every coefficient tuple. -/
theorem ordinary_rows_per_prime {n ell p : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (mem : p∈primeBand (n.log2+1))
    (a b c d : ℕ) :
    let s := TryPair.fixedInput n ell (construct n ell a b c d)
    (s.rows.toFinset.filter (fun row => row.q=p)).card ≤ 2*Fixed.d (n.log2+1) := by
  classical
  intro s
  let deg := Fixed.d (n.log2+1)
  let : Fact p.Prime := ⟨(mem_primeBand.mp mem).1⟩
  let pol (side : Bool) := (Marking.polynomial (s.coeffs side)).map (Int.castRingHom (ZMod p))
  have high := ordinary_leading_unit hd mem
  have top (t : Bool) : (pol t).coeff deg = (leadingCoefficient n:ZMod p) := by
    have h : (s.coeffs t).length=deg+1 ∧ (s.coeffs t).getLast?=some (leadingCoefficient n:ℤ) := by
      cases t <;> first | exact shape (ell:=ell) hd false a b | exact shape (ell:=ell) hd true c d
    have last : (s.coeffs t)[deg]?=some (leadingCoefficient n:ℤ) := by
      simpa [List.getLast?_eq_getElem?,h.1] using h.2
    dsimp only [pol]; rw [coefficient_rep]
    simp [List.getD_eq_getElem?_getD,last]
  have nz (t : Bool) : pol t≠0 := fun h => high (by rw [←top t,h,coeff_zero])
  have fields := constructed_rational_fields hd target a b c d
  have bound (t : Bool) : (pol t).roots.toFinset.card≤deg := by
    apply ((Multiset.toFinset_card_le _).trans (card_roots' _)).trans
    apply natDegree_map_le.trans
    cases t <;> first | exact fields.1.1.le | exact fields.2.1.le
  let A := s.rows.toFinset.filter (fun row => row.q=p)
  let Z := ({false} ×ˢ (pol false).roots.toFinset) ∪ ({true} ×ˢ (pol true).roots.toFinset)
  let code (i : Marking.Row) := (i.second,(i.r:ZMod p))
  have inj : A.card≤Z.card := card_le_card_of_injOn code (by
    intro i hi
    obtain ⟨im,iq⟩ := mem_filter.mp hi
    have root := (Marking.mem_rows.mp (List.mem_toFinset.mp im)).2.2
    rw [iq] at root
    have h : (i.r:ZMod p)∈(pol i.second).roots := (mem_roots (nz _)).mpr (by
      exact (Polynomial.eval_map ..).trans root)
    cases t : i.second
    · exact mem_union_left _ (mem_product.mpr ⟨by simp [code,t],Multiset.mem_toFinset.mpr (t ▸ h)⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨by simp [code,t],Multiset.mem_toFinset.mpr (t ▸ h)⟩)) (by
    rintro ⟨t,q,r⟩ hi ⟨t',q',r'⟩ hj eq
    obtain ⟨im,iq⟩ := mem_filter.mp hi
    obtain ⟨jm,jq⟩ := mem_filter.mp hj
    change q=p at iq
    change q'=p at jq
    subst q q'
    obtain ⟨one,two⟩ := Prod.mk.inj eq
    have ir := (Marking.mem_rows.mp (List.mem_toFinset.mp im)).2.1
    have jr := (Marking.mem_rows.mp (List.mem_toFinset.mp jm)).2.1
    have rr := congrArg ZMod.val two
    change ((r:ZMod p)).val = ((r':ZMod p)).val at rr
    rw [ZMod.val_natCast_of_lt ir,ZMod.val_natCast_of_lt jr] at rr
    cases one; cases rr; rfl)
  exact inj.trans ((card_union_le ..).trans (by simpa using (show (pol false).roots.toFinset.card+
    (pol true).roots.toFinset.card≤2*deg by have := bound false; have := bound true; omega)))

/-- Same-prime off-diagonal errors may have either sign. Each block on any
subset of the admitted rows costs at most 2d times its maximum entry. -/
theorem same_prime_gram_error {n ell : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a b c d : ℕ) :
    let s := TryPair.fixedInput n ell (construct n ell a b c d)
    ∀ (A : Finset Marking.Row), A⊆s.rows.toFinset →
      (∀ i∈A, i.q∈primeBand (n.log2+1)) →
      ∀ (E : Marking.Row→Marking.Row→ℝ) (δ : ℝ), 0≤δ →
        (∀ i∈A, ∀ j∈A, i.q≠j.q → E i j=0) →
        (∀ i∈A, ∀ j∈A, i.q=j.q → |E i j|≤δ) →
        ∀ v : Marking.Row→ℝ, |∑ i∈A,∑ j∈A, v i*E i j*v j|≤
          (2*(Fixed.d (n.log2+1):ℝ)*δ)*(∑ i∈A,(v i)^2) := by
  classical
  intro s A sub band E δ dp outside bound v
  let cap : ℝ := 2*(Fixed.d (n.log2+1):ℝ)*δ
  have count (i : Marking.Row) (hi : i∈A) : ((A.filter (fun j => j.q=i.q)).card:ℝ) ≤ 2*(Fixed.d (n.log2+1):ℝ) := by
    have n := ordinary_rows_per_prime hd target (band i hi) a b c d
    have smaller := card_le_card (filter_subset_filter (p:=fun j : Marking.Row => j.q=i.q) sub)
    exact_mod_cast smaller.trans n
  have line (i : Marking.Row) (hi : i∈A) (f : Marking.Row→ℝ)
      (zero : ∀j∈A,j.q≠i.q → f j=0) (size : ∀j∈A,j.q=i.q → |f j|≤δ) :
      ∑ j∈A,|f j|≤cap := by
    let B := A.filter (fun j=>j.q=i.q)
    calc ∑ j∈A,|f j| = ∑ j∈B,|f j| := by
           dsimp only [B]; rw [sum_filter]; apply sum_congr rfl; intro j hj
           split <;> first | rfl | simp_all
         _ ≤ ∑ _j∈B,δ := sum_le_sum (fun j h => size j (mem_filter.mp h).1 (mem_filter.mp h).2)
         _ ≤ cap := by simpa only [sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (count i hi) dp
  have row (i) (hi : i∈A) := line i hi (E i) (fun j hj h=>outside i hi j hj h.symm)
    (fun j hj h=>bound i hi j hj h.symm)
  have col (j) (hj : j∈A) := line j hj (fun i=>E i j) (fun i hi=>outside i hi j hj) (fun i hi=>bound i hi j hj)
  let e := ∑ i∈A, ∑ j∈A, |v i*E i j*v j|
  have ab : |∑ i∈A,∑ j∈A,v i*E i j*v j|≤e :=
    (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun _ _=>abs_sum_le_sum_abs ..))
  have pt (i j) : 2*|v i*E i j*v j| ≤ |E i j| *(v i)^2+|E i j| *(v j)^2 := by
    have sq := sq_nonneg (|v i|-|v j|)
    rw [sub_sq,sq_abs,sq_abs] at sq
    simp only [abs_mul]
    nlinarith only [mul_nonneg (abs_nonneg (E i j)) sq]
  have total := sum_le_sum (s:=A) (fun i _ => sum_le_sum (s:=A) (fun j _ => pt i j))
  let V := ∑ i∈A,(v i)^2
  have first : (∑ i∈A,∑ j∈A,|E i j| *(v i)^2)≤cap*V := by
    simp only [V,←sum_mul,mul_sum]
    exact sum_le_sum (fun i h=>mul_le_mul_of_nonneg_right (row i h) (sq_nonneg _))
  have second : (∑ i∈A,∑ j∈A, |E i j| *(v j)^2)≤cap*V := by
    rw [sum_comm]; simp only [V,←sum_mul,mul_sum]
    exact sum_le_sum (fun i h=>mul_le_mul_of_nonneg_right (col i h) (sq_nonneg _))
  simp only [←mul_sum,sum_add_distrib] at total
  change 2*e≤_ at total
  exact ab.trans (by linarith only [total,first,second])


end
end Cogentic.Construction

#print axioms Cogentic.Construction.ordinary_rows_per_prime
#print axioms Cogentic.Construction.same_prime_gram_error
