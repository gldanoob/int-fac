import Cogentic.BadRowGcd
import Cogentic.PolynomialRetained

namespace Cogentic.Construction

/-- The target rows are already simple, so on a smooth fiber one needs
only test ordinary primes outside any stride coprime to the value. -/
theorem derivative_coprime_of_ordinary {n ell : ℕ} (hd : 3≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (u v w z a : ℕ) (side : Bool) (M : ℕ) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    let f := s.coeffs side
    let val := Marking.value f a; let der := (Marking.horner (a:ℤ) f).2.natAbs
    Marking.SquarefreeSmooth s.base val → val.Coprime M →
    (∀ p∈val.primeFactors, p≠ell → ¬p∣M → ¬p∣der) → val.Coprime der := by
  intro s f val der smooth stride regular
  apply Nat.coprime_of_dvd
  intro p prime hit slope
  have pf := Nat.mem_primeFactors.mpr ⟨prime,hit,smooth.1⟩
  by_cases he : p=ell
  · subst p
    let row := Marking.Row.mk side ell (a%ell)
    have root := (Marking.zero_at_mark f a ell).1.mpr hit
    have mem : row∈s.rows := Marking.mem_rows.mpr
      ⟨smooth.2.2 ell prime hit,Nat.mod_lt _ prime.pos,by simpa only [Marking.horner_correct] using root⟩
    have clean := Marking.mem_clean.mp ((target_rows_clean hd target u v w z row mem rfl).2)
    have singular := (Marking.zero_at_mark f a ell).2.mpr slope
    exact clean.2.1 (by simpa only [Marking.horner_correct] using singular)
  · exact regular p pf he (fun atM => Nat.not_coprime_of_dvd_of_dvd prime.one_lt hit atM stride) slope

/-- Smoothness, mutual coprimality, and both simple-root tests suffice for
membership in the actual list emitted by stage one. -/
theorem retained_of_regular_smooth {n ell a u v w z : ℕ} (R T : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell u v w z).marks)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b)
    (l : R.compatible false u v) (r : T.compatible true w z) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel →
    Marking.SquarefreeSmooth s.base (Marking.value s.first a) →
    Marking.SquarefreeSmooth s.base (Marking.value s.second a) →
    (Marking.value s.first a).Coprime (Marking.value s.second a) →
    (∀ side : Bool, (Marking.value (s.coeffs side) a).Coprime (Marking.horner (a:ℤ) (s.coeffs side)).2.natAbs) →
    a∈rel.marks := by
  intro s rel stage ls rs shared simple
  have avoid := (Marking.avoids_badRows_iff_coprime s a (fun i => by cases i <;> assumption)).mpr ⟨shared,simple⟩
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have degree := (show 10004≤130000 by decide).trans big
  have left := R.box_smooth_iff hn degree comp target absent cap grid ⟨box.1,box.2.1⟩ false l
  have right := T.box_smooth_iff hn degree comp target absent cap grid box.2.2 true r
  exact (retained_from_polynomial_events R T hn big comp target absent mark box l r stage).mpr
    ⟨left.mpr ls,right.mpr rs,avoid⟩

end Cogentic.Construction
