import Cogentic.FarNominalPair
import Cogentic.FarPairSavings
import Cogentic.FarPairIntegration
import Cogentic.TargetResidue
import Cogentic.FreeFirstLoss
import Cogentic.CleanObservationMass

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

private theorem twice_loss {ε η δ rate p x pts τ : ℝ} (e : 0≤ε)
    (d : 3*δ≤η) (r : 0≤rate) (a : 0≤p) (xp : 0≤x) (pp : 0≤pts) (t : 0≤τ) :
    (ε+(η+3*δ))*rate*p+x*(η+3*δ)*pts+(2+rate)*τ ≤
      2*((ε+η)*rate*p+x*η*pts+(2+rate)*τ) := by
  have one := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right d r) a
  have two := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d xp) pp
  nlinarith only [one,two,mul_nonneg (mul_nonneg e r) a,mul_nonneg r t,t]

/-- First-observation error bounds for the exceptional free and target
primes suffice on every separation above the near-pair cutoff. -/
theorem PrescribedRows.separated_joint_of_exception_estimates (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks → y≠a →
    (Fixed.A b:ℝ) ≤ |(y:ℝ)-a| * (dyadicUnit b:ℝ)^50 → ∀ side : Bool,
    (∀ p∈R.hit a, ¬p^2∣((y:ℤ)-a).natAbs) →
    let E := fun i (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor i side)) (R.intercept i side k.1 k.2)
    let P := fun i => prescribedProbability R side (E i)
    let corr := coprimeFactor (R.secondStep a y side).natAbs/coprimeFactor (firstStep n ell y side).natAbs
    let pred := (corr*P y)*P a
    (∀ p∈R.exceptionPrimes a y side, prescribedProbability R side (fun k =>
      E a k ∧ R.badFirstQuotient a y side p (R.intercept a side k.1 k.2)) ≤
      (36*(Fixed.B b:ℝ)^(-199/400:ℝ))*P a) →
    0<pred ∧ |prescribedProbability R side (fun k=>E a k ∧ E y k)/pred-1|≤C*exp (-v*(Fixed.z b:ℝ)^2) := by
  classical
  obtain ⟨C,cp,b₁,fiber⟩ := PrescribedRows.gcd_one_conditional_smooth line v hv
  obtain ⟨b₂,average⟩ := PrescribedRows.integrated_restriction_bound line
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 10004
  obtain ⟨b₄,clean⟩ := PrescribedRows.clean_observation_loss line
  obtain ⟨b₅,margin⟩ := PrescribedRows.smooth_probability_margin line
  obtain ⟨b₆,saving⟩ := integrated_difference_savings v hv
  refine ⟨2*(C+4344),by positivity,max (max b₁ b₂) (max (max b₃ b₄) (max b₅ b₆)),?_⟩
  intro n ell a y R b huge hn comp target absent am ym diff sep side squares E P corr pred rare
  obtain ⟨one,two⟩ := max_le_iff.mp (max_le_iff.mp huge).1
  obtain ⟨t,s⟩ := max_le_iff.mp (max_le_iff.mp huge).2
  obtain ⟨three,four⟩ := max_le_iff.mp t
  obtain ⟨five,six⟩ := max_le_iff.mp s
  have cap := ((constructed_marks_iff ..).mp am).2.1
  have yc := ((constructed_marks_iff ..).mp ym).2.1
  let J := sieveBand n ell (R.prefactor a side)
  let K := J \ bandDifferencePrimes b a y
  let keep (z : ℤ) := supportedValue K z ∧ ∀ p∈R.exceptionPrimes a y side, ¬R.badFirstQuotient a y side p z
  let Δ : ℝ := (Fixed.B b:ℝ)^(-199/400:ℝ)
  let δ := 36*Δ; let η := 720*Δ+360*exp (-(Fixed.U b:ℝ))
  let τ := (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2))
  let e := exp (-v*(Fixed.z b:ℝ)^2); let rate := corr*P y
  have keepSub (z : ℤ) (h : keep z) : supportedValue J z := by
    obtain ⟨x,hx,eq⟩ := mem_image.mp h.1
    obtain ⟨ps,hp,eqp⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨x,mem_image.mpr ⟨ps,mem_powerset.mpr ((mem_powerset.mp hp).trans sdiff_subset),eqp⟩,eq⟩
  have dx : 0≤Δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have dp : 0≤δ := by dsimp only [δ]; positivity
  have np : 0≤η := by dsimp only [η]; positivity
  have pp := margin R five hn comp target absent am side
  have py := margin R five hn comp target absent ym side
  change 8/(Fixed.B b:ℝ)≤P a at pp
  change 8/(Fixed.B b:ℝ)≤P y at py
  have c1 := R.second_correction_one_le (mark_range hn (degree b three) yc) (mem_dyadicTargets.mp target).1.pos diff side
  change 1≤corr at c1
  have lb : 0<8/(Fixed.B b:ℝ) := by dsimp [Fixed.B]; positivity
  have rt : 0<rate := mul_pos (zero_lt_one.trans_le c1) (lb.trans_le py)
  have pos : 0<pred := mul_pos rt (lb.trans_le pp)
  have loss := clean R four hn comp target absent am yc diff.symm side δ dp rare
  have est := average R two hn comp target absent am ym diff side rate (C*e) rt.le (by dsimp only [e]; positivity)
    keep (η+3*δ) (by positivity) keepSub loss (by
      intro u w ok x m y' key G bulk hit
      have gcd := R.unit_gcd_after_all_exclusions hn (degree b three) comp target absent ym diff side squares u w ok hit.1 hit.2
      obtain ⟨_,_,h⟩ := fiber R one hn comp target absent cap ym diff sep side u w ok bulk gcd
      let θ := (∑' j:ℤ, if E y (key j) then G j else 0)/(∑' j,G j)
      change |θ/rate-1|≤C*e at h
      change θ∈Set.Icc _ _
      obtain ⟨lo,hi⟩ := abs_le.mp h
      exact ⟨(le_div_iff₀ rt).mp (by linarith only [lo]),(div_le_iff₀ rt).mp (by linarith only [hi])⟩)
  let rough := exp (10*(Fixed.h b:ℝ))
  have small : 3*δ≤η := by dsimp only [η,δ]; linarith only [dx,(exp_pos (-(Fixed.U b:ℝ))).le]
  have absorb := twice_loss (x:=rough) (by dsimp only [e]; positivity : 0≤C*e) small rt.le (lb.trans_le pp).le
    (exp_pos _).le (mul_nonneg (lb.trans_le pp).le (lb.trans_le py).le) (by dsimp only [τ]; positivity : 0≤τ)
  have final := est.trans (absorb.trans (mul_le_mul_of_nonneg_left (saving b six (P a) (P y) corr C pp py c1) (by norm_num)))
  refine ⟨pos,?_⟩
  rw [div_sub_one pos.ne',abs_div,abs_of_pos pos,div_le_iff₀ pos]
  exact final.trans_eq (by dsimp only [pred]; ring)

/-- A separated pair of actual marks has its conductor-corrected product
density to arbitrary fixed logarithmic-square accuracy. This includes
common target hits and all permitted prescribed ordinary roots. -/
theorem PrescribedRows.separated_joint_relative (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks → y≠a →
    (Fixed.A b:ℝ) ≤ |(y:ℝ)-a| * (dyadicUnit b:ℝ)^50 → ∀ side : Bool,
    (∀ p∈R.hit a, ¬p^2∣((y:ℤ)-a).natAbs) →
    let E := fun i (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor i side)) (R.intercept i side k.1 k.2)
    let P := fun i => prescribedProbability R side (E i)
    let corr := coprimeFactor (R.secondStep a y side).natAbs/coprimeFactor (firstStep n ell y side).natAbs
    let pred := (corr*P y)*P a
    0<pred ∧ |prescribedProbability R side (fun k=>E a k ∧ E y k)/pred-1|≤C*exp (-v*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,b₁,joint⟩ := PrescribedRows.separated_joint_of_exception_estimates line v hv
  obtain ⟨b₂,freeLoss⟩ := PrescribedRows.free_bad_first_loss line
  obtain ⟨b₃,targetLoss⟩ := PrescribedRows.common_target_quotient_probability line
  refine ⟨C,cp,max b₁ (max b₂ b₃),?_⟩
  intro n ell a y R b huge hn comp target absent am ym diff sep side squares E P corr pred
  obtain ⟨one,rest⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp rest
  apply joint R one hn comp target absent am ym diff sep side squares
  intro p pm
  rcases mem_union.mp pm with free|special
  · exact freeLoss R two hn comp target absent am ym side p free
  · split at special
    next h =>
      obtain rfl := mem_singleton.mp special
      exact targetLoss R three hn comp target absent am side h.1 h.2.1 h.2.2
    next => simp at special

end
end Cogentic.Construction
