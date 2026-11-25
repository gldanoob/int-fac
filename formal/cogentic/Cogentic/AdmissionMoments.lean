import Cogentic.TwoFieldMoments
import Cogentic.PolynomialSmooth
import Cogentic.BadRowGcd

namespace Cogentic.Construction
open Real Finset
open scoped Classical
noncomputable section

def PrescribedRows.unrestricted (n ell : ℕ) : PrescribedRows n ell :=
  ⟨∅,fun _ => 0,by simp,by simp,by simp,by simp⟩

/-- Admission of the signed coefficient pair is exactly the presence of
each prescribed root in the program's row list before cleaning. -/
theorem PrescribedRows.compatible_iff_listed {n ell : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 3≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (u v w z : ℕ) (side : Bool) :
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    let x := if side then (w:ℤ) else u
    let y := if side then (z:ℤ) else v
    R.compatible side x y ↔ ∀ p∈R.primes, Marking.Row.mk side p (R.residue p % p)∈s.rows := by
  intro s x y
  have same (p : ℕ) (pm : p∈R.primes) :
      (p:ℤ) ∣ affineValue n ell (R.residue p) side (x+R.residue p*y) ↔
        Marking.Row.mk side p (R.residue p % p)∈s.rows := by
    let a := R.residue p
    let f := s.coeffs side
    have cap : p ∈ s.base := by
      apply List.mem_toFinset.mp
      rw [←sieveBand_executable (ell:=ell) hn big comp absent u v w z]
      exact R.member pm
    have ev : eval (a:ℤ) f=affineValue n ell a side (x+a*y) := by
      have fl := affine_at_constructed (ell:=ell) big a u v w z
      cases side <;> first | exact fl.1 | exact fl.2
    have div : (p:ℤ)∣affineValue n ell a side (x+a*y) ↔ p ∣ Marking.value f a := by
      rw [←ev,Marking.value,horner_eval_int]
      exact Int.natAbs_dvd_natAbs.symm.trans (by simp)
    have cl := (Marking.zero_at_mark f a p).1
    rw [Marking.mem_rows,and_iff_right cap,and_iff_right (Nat.mod_lt _ (R.prime pm).pos)]
    exact div.trans (by simpa only [Marking.horner_correct] using cl.symm)
  exact ⟨fun ok p h => (same p h).mp (ok p h),fun rows p h => (same p h).mpr (rows p h)⟩

/-- Transfer an arbitrary event from the conditioned lattice back to the
original coefficient law. The same admission factor works for every event. -/
theorem PrescribedRows.uncondition {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) :
    ∃ A : ℝ, 0<A ∧ |(prodPrimes R.primes:ℝ)*A-1| ≤ 72*exp (-(Fixed.U (n.log2+1):ℝ)) ∧
    ∀ (E : ℤ×ℤ→Prop) [DecidablePred E],
      prescribedProbability (PrescribedRows.unrestricted n ell) side
        (fun k => R.compatible side k.1 k.2 ∧ E k) = A*prescribedProbability R side E := by
  classical
  let S := PrescribedRows.unrestricted n ell
  let C := R.CoeffPoint side
  let total := ∑' k, coefficientWeight n k
  let sub := ∑' k : C, coefficientWeight n k.val
  obtain ⟨tp,sp,rate⟩ := R.admission_probability target side
  change 0 < total at tp
  change 0 < sub at sp
  refine ⟨sub/total,div_pos sp tp,rate,?_⟩
  intro E inst
  let F := fun k : ℤ×ℤ => if R.compatible side k.1 k.2 ∧ E k then coefficientWeight n k else 0
  have all (k : ℤ×ℤ) : S.compatible side k.1 k.2 := by simp [S,unrestricted,compatible]
  let iso : S.CoeffPoint side ≃ ℤ×ℤ :=
    ⟨Subtype.val,fun k => ⟨k,all k⟩,fun _ => rfl,fun _ => rfl⟩
  have sup : Function.support F ⊆ Set.range (Subtype.val : C→ℤ×ℤ) := by
    intro k hk
    by_cases ok : R.compatible side k.1 k.2
    · exact ⟨⟨k,ok⟩,rfl⟩
    · exact (hk (by simp [F,ok])).elim
  have num : (∑' k : C, if E k.val then coefficientWeight n k.val else 0) = ∑' k,F k := by
    rw [←(Subtype.val_injective.tsum_eq sup)]
    exact tsum_congr (fun k => by simp [F,k.property])
  change (∑' k : S.CoeffPoint side,F (iso k))/(∑' k : S.CoeffPoint side,coefficientWeight n (iso k))=
    sub/total*((∑' k : C, if E k.val then coefficientWeight n k.val else 0)/sub)
  rw [iso.tsum_eq,iso.tsum_eq,num]
  change _/total = sub/total*(_/sub)
  field_simp

/-- Both raw moments of an admitted finite signed mark score have the
same scalar admission factor under the original two-polynomial distribution. -/
theorem twoField_admission_moments {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) :
    let S := PrescribedRows.unrestricted n ell
    let Q : ℝ := prodPrimes R.primes*prodPrimes T.primes
    let η := 72*exp (-(Fixed.U (n.log2+1):ℝ))
    ∃ A : ℝ, 0<A ∧ |Q*A-1|≤2*η+η^2 ∧
    ∀ (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop),
    let l := fun i (k : ℤ×ℤ) => R.compatible false k.1 k.2 ∧ E i k
    let r := fun i (k : ℤ×ℤ) => T.compatible true k.1 k.2 ∧ F i k
    twoFieldMean S S X w l r=A*twoFieldMean R T X w E F ∧
    twoFieldSecond S S X w l r=A*twoFieldSecond R T X w E F := by
  classical
  intro S Q η
  obtain ⟨a,ap,one,left⟩ := R.uncondition target false
  obtain ⟨b,bp,two,right⟩ := T.uncondition target true
  let x : ℝ := (prodPrimes R.primes:ℝ)*a-1
  let y : ℝ := (prodPrimes T.primes:ℝ)*b-1
  change |x|≤η at one
  change |y|≤η at two
  refine ⟨a*b,mul_pos ap bp,?_,?_⟩
  · have prod := mul_le_mul one two (abs_nonneg _) ((abs_nonneg x).trans one)
    have id : Q*(a*b)-1=(x+y)+x*y := by dsimp [Q,x,y]; ring
    calc |Q*(a*b)-1| = |(x+y)+x*y| := congrArg abs id
         _ ≤ (|x|+|y|)+|x*y| := (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
         _ ≤ _ := by rw [abs_mul]; linarith only [one,two,prod]
  · intro X w E F l r
    constructor
    · unfold twoFieldMean
      rw [mul_sum]; apply sum_congr rfl
      intro i _
      dsimp only [l,r]
      have move {Q : PrescribedRows n ell} {s : Bool} {P G : ℤ×ℤ→Prop} {c : ℝ}
          {d d' : DecidablePred G} {e e' : DecidablePred P}
          (h : @prescribedProbability n ell S s G d=c*@prescribedProbability n ell Q s P e) :
          @prescribedProbability n ell S s G d'=c*@prescribedProbability n ell Q s P e' := by
        rwa [Subsingleton.elim d' d,Subsingleton.elim e' e]
      calc _ = w i*((a*prescribedProbability R false (E i))*(b*prescribedProbability T true (F i))) :=
             congrArg (w i*·) (congrArg₂ (·*·) (move (left (E i))) (move (right (F i))))
           _ = _ := by ring
    · unfold twoFieldSecond
      rw [mul_sum]; apply sum_congr rfl
      intro i _
      rw [mul_sum]; apply sum_congr rfl
      intro j _
      have pair (D : ℤ×ℤ→Prop) (P : ι→ℤ×ℤ→Prop) :
          (fun k => (D k ∧ P i k) ∧ (D k ∧ P j k)) = fun k => D k ∧ (P i k ∧ P j k) :=
        funext (fun _ => propext (by tauto))
      dsimp only [l,r]
      simp_rw [pair]
      rw [left (fun k => E i k ∧ E j k),right (fun k => F i k ∧ F j k)]; ring

end
end Cogentic.Construction
