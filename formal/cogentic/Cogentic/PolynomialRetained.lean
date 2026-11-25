import Cogentic.PolynomialSmooth

namespace Cogentic.Construction
open Cogentic.Window

/-- The minimum size of an allowed prime and the elementary Horner
    height guard imply the executable relation-length guard at every
    smooth point. No smooth-number asymptotic is needed for this step. -/
theorem mark_sparsity {n ell a u v w z : ℕ} (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (amin : 1≤a) (cap : a≤Fixed.A (n.log2+1))
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    ∀ (side : Bool), let m := Marking.value (s.coeffs side) a
    Marking.SquarefreeSmooth s.base m → 4*m.primeFactors.card ≤ s.L₀ := by
  let b := n.log2+1; let d := Fixed.d b; let h := Fixed.h b
  let s := TryPair.fixedInput n ell (construct n ell u v w z)
  have dlim := Fixed.degree_le_bits b
  have hlim : d≤h := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have dexp : d+1≤2^b := (Nat.succ_le_succ dlim).trans (Nat.lt_two_pow_self (n := b))
  have guards := Fixed.stage_guards hn (by omega : 10004≤Fixed.d (n.log2+1))
  have acap : a≤2^b := cap.trans guards.heights.2.2.1
  have ⟨left,right⟩ := box_polynomialGuards hn big comp target none box
  intro _ side m smooth
  have input : s.polynomialGuard (s.coeffs side) := by cases side <;> assumption
  have value : m≤2^((d+3)*b) := Marking.value_size input amin acap dexp
  have lower (q : ℕ) (hq : q∈m.primeFactors) : 2^(500*h) ≤ q := by
    have mem := (Marking.mem_base.mp (smooth.2.2 q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq))).1
    have large := ((constructed_factorBase_iff n ell u v w z q).mp mem).2.2.1
    by_contra! small
    have pow : q^2 ≤ (2^(500*h))^2 := Nat.pow_le_pow_left small.le 2
    have bb : Fixed.B b= (2^(500*h))^2 := by
      change 2^(1000*h)=(2^(500*h))^2; rw [←pow_mul]; congr 1; ring
    exact large.not_ge (bb ▸ pow)
  have pbound : 2^(500*h*m.primeFactors.card) ≤ m := by
    rw [pow_mul]
    calc _ = ∏ _q ∈ m.primeFactors, 2^(500*h) := by simp
         _ ≤ ∏ q ∈ m.primeFactors, q := Finset.prod_le_prod' lower
         _=m := Nat.prod_primeFactors_of_squarefree smooth.2.1
  have small := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (pbound.trans value)
  have scale : 4*(d+3)≤500*h := by change 130000≤d at big; omega
  have bound : (d+3)*(4*m.primeFactors.card)≤(d+3)*b :=
    (by rw [←Nat.mul_assoc,Nat.mul_comm (d+3) 4]; exact (Nat.mul_le_mul_right _ scale).trans small)
  exact (Nat.le_of_mul_le_mul_left bound (by omega : 0<d+3))

/-- The executable marker retains precisely the points where both signed
    polynomial models succeed and every bad row is avoided. The auxiliary
    gcd and relation-size tests are derived from the true presieve and box. -/
theorem retained_from_polynomial_events {n ell a u v w z : ℕ} (R T : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (mark : a∈(construct n ell u v w z).marks)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b)
    (l : R.compatible false u v) (r : T.compatible true w z) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel →
    (a∈rel.marks ↔ supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false u v) ∧
      supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true w z) ∧
      ∀ row∈s.badRows, a%row.q ≠ row.r) := by
  let s := TryPair.fixedInput n ell (construct n ell u v w z)
  obtain ⟨amin,cap,grid,_⟩ := (constructed_marks_iff n ell u v w z a).mp mark
  have large : 10004≤Fixed.d (n.log2+1) := by omega
  have left := R.box_smooth_iff hn large comp target none cap grid ⟨box.1,box.2.1⟩ false l
  have right := T.box_smooth_iff hn large comp target none cap grid box.2.2 true r
  have eligible : a∈s.eligibleMarks := by
    have h := (n_coprime_gap hn large amin cap none).symm
    unfold Marking.Input.eligibleMarks
    simpa only [Finset.mem_sort,Finset.mem_filter,List.mem_toFinset] using
      (show a∈s.marks ∧ 1≤a ∧ a ≤ s.A ∧ ((a:ℤ)-s.m).natAbs.Coprime s.n from
      ⟨mark,amin,cap,by change ((a:ℤ)-Fixed.rootBase n).natAbs.Coprime n; rw [natAbs_gap (mark_range hn large cap).le]; exact h⟩)
  have len := mark_sparsity (ell := ell) hn big comp target none amin cap box
  intro _ rel stage
  rw [Marking.retained_iff stage]
  constructor
  · rintro ⟨_,ls,rs,_,avoid⟩
    exact ⟨left.mpr ls,right.mpr rs,avoid⟩
  · rintro ⟨ls,rs,avoid⟩
    have ls' := left.mp ls; have rs' := right.mp rs
    have one := len false ls'; have two := len true rs'
    change 4*(Marking.value s.first a).primeFactors.card≤n.log2+1 at one
    change 4*(Marking.value s.second a).primeFactors.card≤n.log2+1 at two
    refine ⟨eligible,ls',rs',?_,avoid⟩
    change 1+(Marking.value s.first a).primeFactors.card+(Marking.value s.second a).primeFactors.card≤n.log2+1
    omega

end Cogentic.Construction

#print axioms Cogentic.Construction.mark_sparsity
#print axioms Cogentic.Construction.retained_from_polynomial_events
