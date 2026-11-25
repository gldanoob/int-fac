import Cogentic.FiberIntegration
import Cogentic.RestrictedPairUpper

namespace Cogentic.Construction
open Finset Real Cogentic.Window
noncomputable section

theorem probability_congr {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (Q V : ℤ×ℤ→Prop) [iq : DecidablePred Q] [iv : DecidablePred V] (eq : Q=V) :
    prescribedProbability R side Q=prescribedProbability R side V := by
  subst V
  cases Subsingleton.elim iq iv
  rfl

private theorem integrated_error {j jc jb p pb rate ε η τ loss : ℝ}
    (rt : 0≤rate) (ep : 0≤ε) (np : 0≤p) (eta : 0≤η) (tp : 0≤τ) (el : 0≤loss)
    (center : jb∈Set.Icc ((1-ε)*rate*pb) ((1+ε)*rate*pb))
    (lower : jc≤j) (upper : j-jc≤loss+τ) (cut : |jc-jb|≤τ)
    (sub : pb≤p) (first : p-pb≤η*p+τ) :
    |j-rate*p|≤(ε+η)*rate*p+loss+(2+rate)*τ := by
  have small := mul_le_mul_of_nonneg_left sub (mul_nonneg ep rt)
  have lost := mul_le_mul_of_nonneg_left first rt
  have z := mul_nonneg rt (sub_nonneg.mpr sub)
  have c := abs_le.mp cut
  apply abs_le.mpr
  constructor
  · nlinarith only [center.1,lower,c.1,small,lost,el,tp]
  · nlinarith only [center.2,c.2,upper,small,z,mul_nonneg (mul_nonneg eta rt) np,mul_nonneg rt tp]

set_option maxHeartbeats 600000 in
/-- A pointwise estimate on the bulk unit fibers transfers to the full pair
probability, with explicit costs for excluded primes and Gaussian tails. -/
theorem PrescribedRows.integrated_restriction_bound (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → a'∈(construct n ell 0 0 0 0).marks →
    a'≠a → ∀ (side : Bool) (rate ε : ℝ), 0≤rate → 0≤ε →
    let E := fun i (k : ℤ×ℤ) => supportedValue (sieveBand n ell (R.prefactor i side)) (R.intercept i side k.1 k.2)
    let P := fun i => prescribedProbability R side (E i)
    ∀ (keep : ℤ→Prop) [DecidablePred keep] (η : ℝ), 0≤η →
    (∀ z, keep z → supportedValue (sieveBand n ell (R.prefactor a side)) z) →
    P a - prescribedProbability R side (fun k=>keep (R.intercept a side k.1 k.2)) ≤ η*P a →
    (∀ u v : ℤ, R.compatible side u v →
      let x := u+a*v; let m := prodPrimes (R.miss a); let y := fun j : ℤ => v+(m:ℤ)*j
      let key := fun j : ℤ => (x-a*y j,y j); let G := fun j : ℤ => coefficientWeight n (key j)
      |(x:ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a →
      keep (R.intercept a side u v) →
      (∑' j, if E a' (key j) then G j else 0)/(∑' j,G j)∈Set.Icc ((1-ε)*rate) ((1+ε)*rate)) →
    let τ := (1+90*exp (-(Fixed.U b:ℝ)))*(8*exp (-π*((b:ℝ)^3)^2/2))
    |prescribedProbability R side (fun k => E a k ∧ E a' k)-rate*P a| ≤
      (ε+η)*rate*P a + exp (10*(Fixed.h b:ℝ))*η*(P a*P a') + (2+rate)*τ := by
  classical
  obtain ⟨b₀,rough⟩ := PrescribedRows.restricted_joint_smooth_upper line
  refine ⟨b₀,?_⟩
  intro n ell a a' R b huge hn comp target absent am bm diff side rate ε rt ep E P keep dec η eta into firstLoss localBound τ
  have cap := ((constructed_marks_iff ..).mp am).2.1
  let B (x : ℤ) := |(x:ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a
  let C (k : ℤ×ℤ) := keep (R.intercept a side k.1 k.2)
  let F (x : ℤ) := B x ∧ keep (R.intercept a side x 0)
  let G (k : ℤ×ℤ) := F (k.1+(a:ℤ)*k.2)
  let prob (Q : ℤ×ℤ→Prop) [DecidablePred Q] := prescribedProbability R side Q
  have sub (k : ℤ×ℤ) (h : C k) : E a k := into _ h
  have first (k : ℤ×ℤ) : G k ↔ B (k.1+(a:ℤ)*k.2) ∧ C k := by
    simp only [G,F,C,PrescribedRows.intercept,mul_zero,add_zero]
  have integrated := R.integrate_fiber_bounds target cap side F (E a') ((1-ε)*rate) ((1+ε)*rate) (by
    intro u v ok x m y key w h
    have smooth : keep (R.intercept a side u v) := by
      simpa only [PrescribedRows.intercept,mul_zero,add_zero,x] using h.2
    exact localBound u v ok h.1 smooth)
  change prob (fun k => G k ∧ E a' k)∈Set.Icc (((1-ε)*rate)*prob G) (((1+ε)*rate)*prob G) at integrated
  have cut := R.observation_cut_error target cap side ((b:ℝ)^3) (by positivity) C G (by
    intro k h
    have hb : B (k.1+(a:ℤ)*k.2) := h.le
    rw [first, and_iff_right hb])
  have jointCut := R.observation_cut_error target cap side ((b:ℝ)^3) (by positivity)
    (fun k => C k ∧ E a' k) (fun k => G k ∧ E a' k) (by
      intro k h
      have hb : B (k.1+(a:ℤ)*k.2) := h.le
      rw [first,and_iff_right hb])
  change |prob C-prob G|≤τ at cut
  change |prob (fun k=>C k ∧ E a' k)-prob (fun k=>G k ∧ E a' k)|≤τ at jointCut
  change P a-prob C≤η*(P a) at firstLoss
  have bad := R.deleted_probability target side (E a) C sub
  change prob (fun k=>E a k ∧ ¬C k)=P a-prob C at bad
  have roughBound := rough R huge hn comp target absent cap bm diff side (fun z => ¬keep z)
  have p₂ : 0≤P a' := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)
  have jointLoss : prob (fun k=>(E a k ∧ ¬C k) ∧ E a' k) ≤ exp (10*(Fixed.h b:ℝ))*η*(P a*P a')+τ := by
    apply roughBound.trans
    change exp _*(prob (fun k=>E a k ∧ ¬C k)*P a')+τ ≤ _
    rw [bad]
    apply add_le_add _ le_rfl
    calc
      _ ≤ exp _*((η*P a)*P a') := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right firstLoss p₂) (exp_pos _).le
      _ = _ := by ring
  let D (k : ℤ×ℤ) := E a k ∧ E a' k
  let Dc (k : ℤ×ℤ) := C k ∧ E a' k
  have pd := R.deleted_probability target side D Dc (fun k h => ⟨sub k h.1,h.2⟩)
  have extn : (fun k=>D k ∧ ¬Dc k)=(fun k=>(E a k ∧ ¬C k) ∧ E a' k) := by
    funext k; apply propext; dsimp only [D,Dc]; tauto
  have lossEq := (probability_congr R side _ _ extn.symm).trans pd
  change prob (fun k=>(E a k ∧ ¬C k) ∧ E a' k)=prob D-prob Dc at lossEq
  change prob (fun k=>(E a k ∧ ¬C k) ∧ E a' k) ≤ exp (10*(Fixed.h b:ℝ))*η*(P a*P a')+τ at jointLoss
  rw [lossEq] at jointLoss
  have nonneg (Q : ℤ×ℤ→Prop) [DecidablePred Q] : 0≤prob Q := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun _=>mul_nonneg (exp_pos _).le (exp_pos _).le)
  have mono (Q V : ℤ×ℤ→Prop) [DecidablePred Q] [DecidablePred V] (hv : ∀ k,V k→Q k) : prob V ≤ prob Q := by
    have d := R.deleted_probability target side Q V hv
    apply sub_nonneg.mp
    rw [←d]
    exact nonneg _
  have gc : prob G≤P a := mono (E a) G (fun k h=>sub k ((first k).mp h).2)
  have cd : prob Dc≤prob D := mono D Dc (fun k h=>⟨sub k h.1,h.2⟩)
  have dc1 := abs_le.mp cut
  have p₁ : 0≤P a := nonneg (E a)
  have tp : 0≤τ := by dsimp only [τ]; positivity
  change |prob D-rate*P a|≤_
  exact integrated_error rt ep p₁ eta tp (mul_nonneg (mul_nonneg (exp_pos _).le eta) (mul_nonneg p₁ p₂))
    integrated cd jointLoss jointCut gc (by linarith only [firstLoss,dc1.2])

end
end Cogentic.Construction
