import Cogentic.PooledResidueMoment
import Cogentic.SharedInsertionProfile
import Cogentic.RetainedCellSelection

namespace Cogentic.Construction
open Finset Real
noncomputable section
open scoped Classical

/-- On a constructor cell the inverse unconditional marginal is uniformly
dominated by the inverse prescribed marginal with a polynomial insertion cost. -/
theorem cell_common_envelope (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (a : ℕ), a∈constructorCellMarks n ell cell →
    ∀ R T : PrescribedRows n ell, let O := PrescribedRows.unrestricted n ell
    1/smoothMarkProbability O O a ≤ ((1+C)*(3*(1760*(Fixed.d b:ℝ)+4)^4)^2)/smoothMarkProbability R T a := by
  obtain ⟨C,cp,b₁,profile⟩ := common_weight_cell_profiles line 1 le_rfl
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell b large hn comp target absent cell a am R T O
  have mark := (mem_filter.mp am).2
  obtain ⟨α,β,law,mesh⟩ := profile (max_le_iff.mp large).1 hn comp target absent {a} (by simpa using mark)
  let p := smoothMarkProbability R T a
  let po := smoothMarkProbability O O a
  have Bp : 0<(Fixed.B b:ℝ) := by dsimp [Fixed.B];positivity
  have pp : 0<p := by
    have each (U : PrescribedRows n ell) side : 0<prescribedProbability U side (smoothMarkEvent U side a) :=
      ((by positivity : 0<8/(Fixed.B b:ℝ)).trans_le (floor U (max_le_iff.mp large).2 hn comp target absent mark side)).trans_eq
        (probability_congr U side _ (smoothMarkEvent U side a) rfl)
    exact mul_pos (each R false) (each T true)
  let J := fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)
  let A := 3*(1760*(Fixed.d b:ℝ)+4)^4
  have ap : 0≤A := by dsimp only [A];positivity
  have logQ (U : PrescribedRows n ell) : 0<U.hitProduct a ∧ log (U.hitProduct a:ℝ)≤2*log (Fixed.B b:ℝ) := by
    obtain ⟨qp,qcap⟩ := U.subprod_bounds (s:=U.hit a) (filter_subset ..)
    refine ⟨qp,?_⟩
    have e := log_le_log (by exact_mod_cast qp : (0:ℝ)<U.hitProduct a) (by exact_mod_cast qcap : (U.hitProduct a:ℝ)≤(Fixed.B b:ℝ)^2)
    simpa only [log_pow,Nat.cast_ofNat] using e
  let L := firstCellMark b cell
  let M := cellMarkCount b
  have loc : a∈Ico L (L+M) := (mem_filter.mp am).1
  obtain ⟨j,aeq⟩ := Nat.exists_eq_add_of_le (mem_Ico.mp loc).1
  have jm : j<M := by have := (mem_Ico.mp loc).2;omega
  have each (U : PrescribedRows n ell) (side : Bool) :
      |fullBandInsertion b (U.hitProduct a) (if side then β a else α a)|≤A := by
    let D := (targetPart n ell a side:ℝ)
    have ep := (mem_dyadicTargets.mp target).1.pos
    have ec := (mem_dyadicTargets.mp target).2.2
    have src : 1≤targetPart n ell a side ∧ targetPart n ell a side≤Fixed.B b := by
      unfold targetPart;split <;> constructor <;> first | assumption | omega | exact Nat.pow_pos (by decide)
    have B1 : 1≤(Fixed.B b:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide) : 0<Fixed.B b)
    have Ac : 1≤(Fixed.A b:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide) : 0<Fixed.A b)
    have upper := (pow_le_pow_right₀ B1 (show 1≤40 by decide))
    rw [pow_one] at upper
    obtain ⟨γ,bind,sup⟩ := mesh cell side D (by dsimp only [D];exact_mod_cast src.1) ((by dsimp only [D];exact_mod_cast src.2 : D≤(Fixed.B b:ℝ)).trans
      (upper.trans (le_mul_of_one_le_left (by positivity) Ac)))
    have eq := (bind j jm).2.2 (by change L+j∈({a}:Finset ℕ);rw [←aeq];simp) (by change (targetPart n ell (L+j) side:ℝ)=D;rw [←aeq])
    change γ j=(if side then β (L+j) else α (L+j)) at eq
    rw [←aeq] at eq
    rw [←eq];exact (sup (U.hitProduct a) (logQ U).1 (logQ U).2).1 j jm
  have size : |J|≤A^2 := by
    rw [show |J|=|fullBandInsertion b (R.hitProduct a) (α a)| * |fullBandInsertion b (T.hitProduct a) (β a)| from abs_mul ..,pow_two]
    exact mul_le_mul (each R false) (each T true) (abs_nonneg _) ap
  let e := C*exp (-1*(Fixed.z b:ℝ)^2)
  have ep : 0≤e := by dsimp only [e];positivity
  have raw := law R T (fun _=>1)
  dsimp only [twoFieldSecond] at raw
  simp only [sum_singleton,one_mul,abs_one,and_self] at raw
  change (1/po-J/p)*(1/po-J/p)*p≤e^2*(J/p*(J/p)*p) at raw
  have sq : (1/po-J/p)^2≤(e*|J/p|)^2 := by
    rw [mul_pow,sq_abs];apply (mul_le_mul_iff_left₀ pp).mp
    simpa only [pow_two,mul_assoc] using raw
  have er := le_of_sq_le_sq sq (mul_nonneg ep (abs_nonneg _))
  have cmp : e≤C := mul_le_of_le_one_right cp.le (exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Fixed.z b:ℝ)]))
  have one : 1/po≤(1+e)*|J/p| := by linarith only [er,le_abs_self (J/p)]
  apply one.trans
  rw [abs_div,abs_of_pos pp,←mul_div_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul (by linarith only [cmp]) size (abs_nonneg _) (by positivity)) pp.le

private theorem correction_coprime {b p q : ℕ} (hp : p∈pairCorrectionPrimes b) (hq : q∈primeBand b) : p.Coprime q := by
  obtain ⟨pp,_,lim⟩ := mem_pairCorrectionPrimes.mp hp
  obtain ⟨qp,_,large⟩ := mem_primeBand.mp hq
  apply (Nat.coprime_primes pp qp).mpr
  rintro rfl
  apply large.not_ge
  calc p^2 ≤ (2^(200*Fixed.h b))^2 := Nat.pow_le_pow_left lim _
       _ = 2^(200*Fixed.h b*2) := (Nat.pow_mul ..).symm
       _ ≤ Fixed.B b := Nat.pow_le_pow_right (by decide) (by dsimp [Fixed.beta];omega)

/-- An uncentered envelope for the common-weight, kept-smooth pair entry on a
constructor cell, at two distinct ordinary primes. Each contributing mark is
actually retained by stage one for the same tuple. The CRT class accounts for
the product of the two ordinary incidence entries. -/
theorem kept_common_overlap_envelope (line : DirichletLZerosOnLine) :
    ∃ C H : ℝ, 0<C ∧ 0<H ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (p q r s : ℕ), p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q →
    let m := p*q; let O := PrescribedRows.unrestricted n ell
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ r [MOD p] ∧ a ≡ s [MOD q])
    let G := fun x y=> ∑ a∈X, if keptSmoothMark R T a x y then (m:ℝ)/smoothMarkProbability O O a else 0
    let M := (cellMarkCount b:ℝ); let B := (Fixed.B b:ℝ); let z := (Fixed.z b:ℝ); let e := exp (-z^2)
    let A := 3*(1760*(Fixed.d b:ℝ)+4)^4
    (∑' k : R.CoeffPoint false × T.CoeffPoint true,twoFieldWeight R T k*(G k.1.val k.2.val)^2) ≤
      ((1+H)*A^2)^2*(C*e*M^2+(M+(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ))+4*M^2/B*exp (48*z)) := by
  classical
  obtain ⟨C,cp,n₁,pool⟩ := pooled_residue_score_second (ι:=Unit) line 1 le_rfl
  obtain ⟨H,hp,b₁,common⟩ := cell_common_envelope line
  refine ⟨C,H,cp,hp,max n₁ (max 2 (2^b₁)),?_⟩
  intro n large ell target comp absent R T b cell p q r s pin qin diff m O X G M B z e A
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  have big : b₁≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  obtain ⟨pb,pok,_⟩ := mem_filter.mp pin
  obtain ⟨qb,qok,_⟩ := mem_filter.mp qin
  obtain ⟨pp,pbnd,_⟩ := mem_primeBand.mp pb
  obtain ⟨qp,qbnd,_⟩ := mem_primeBand.mp qb
  have cop := (Nat.coprime_primes pp qp).mpr diff
  have bound : m≤(Fixed.B b)^3 := (Nat.mul_le_mul pbnd qbnd).trans (by
    rw [←sq];exact Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by decide))
  have clean := Nat.coprime_mul_iff_left.mpr ⟨pp.coprime_iff_not_dvd.mpr pok,qp.coprime_iff_not_dvd.mpr qok⟩
  have small h (hx : h∈pairCorrectionPrimes b) : h.Coprime m :=
    Nat.coprime_mul_iff_right.mpr ⟨correction_coprime hx pb,correction_coprime hx qb⟩
  let v := crt p q r s
  let Y := (constructorCellMarks n ell cell).filter (fun a=>a ≡ v [MOD m])
  have xy : X=Y := by
    ext a
    have u := crt_spec cop r s
    simp only [X,Y,mem_filter]
    apply and_congr_right;intro _
    rw [←Nat.modEq_and_modEq_iff_modEq_mul cop]
    exact ⟨fun h=>⟨h.1.trans u.1.symm,h.2.trans u.2.symm⟩,fun h=>⟨h.1.trans u.1,h.2.trans u.2⟩⟩
  let P := smoothMarkProbability R T
  let E := smoothMarkEvent R false
  let F := smoothMarkEvent T true
  let w := fun a=>(m:ℝ)/P a
  let u := (1+H)*A^2
  have up : 0≤u := by dsimp only [u];positivity
  have pe (U V : PrescribedRows n ell) (a) : 0 ≤ smoothMarkProbability U V a := by
    have each (U : PrescribedRows n ell) side : 0 ≤ prescribedProbability U side (smoothMarkEvent U side a) := by
      rw [←(U.point_event side target (smoothMarkEvent U side a)).tsum_eq]
      exact tsum_nonneg (fun k=>by split <;> first | exact U.pointMass_nonneg side k | rfl)
    exact mul_nonneg (each U false) (each V true)
  have kept (x y : ℤ×ℤ) : G x y ≤ u*twoFieldScore Y w E F x y := by
    dsimp only [G,twoFieldScore];rw [xy,mul_sum]
    apply sum_le_sum; intro a ha
    have raw := common big hn comp target absent cell a (mem_filter.mp ha).1 R T
    by_cases keep : keptSmoothMark R T a x y
    · have both : E a x ∧ F a y := ⟨keep.1,keep.2.1⟩
      simp only [if_pos keep,if_pos both,mul_one]
      have v := mul_le_mul_of_nonneg_left raw (Nat.cast_nonneg (α:=ℝ) m)
      convert v using 1 <;> dsimp only [O,u,A,P,w] <;> ring
    · rw [if_neg keep]
      have wp : 0≤w a := div_nonneg (Nat.cast_nonneg _) (pe R T a)
      split <;> simp only [mul_one,mul_zero,le_refl]
      exact mul_nonneg up wp
  have source := pool n old ell target comp absent R T {()} (fun _=>cell) (fun _=>m) (fun _=>v)
    (fun _ _=>1) (fun _=>1) (fun _ _=>⟨Nat.mul_pos pp.pos qp.pos,(Nat.squarefree_mul cop).mpr ⟨pp.squarefree,qp.squarefree⟩,bound,clean,small⟩)
    (fun _ _=>⟨zero_le_one,by simp⟩)
  simp only [singleton_biUnion,pooledMarkWeight,card_singleton,Nat.cast_one,meshVariation,sub_self,abs_zero,sum_const_zero,
    add_zero,abs_one,sum_const,card_range,nsmul_eq_mul,mul_one,one_pow,one_mul,neg_one_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)] at source
  let bound' := C*e*M^2+(M+(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ))+4*M^2/B*exp (48*z)
  have model : twoFieldSecond R T Y w E F≤bound' := by
    apply le_trans _ source
    dsimp only [twoFieldSecond]
    apply sum_le_sum;intro a ha
    apply sum_le_sum;intro y hy
    change _ ≤ ((if a∈Y then (m:ℝ) else 0)/P a*((if y∈Y then (m:ℝ) else 0)/P y))*_
    rw [if_pos ha,if_pos hy]
  have hs := (twoField_score_second R T target Y w E F).mul_left (u^2)
  let lhs := fun k : R.CoeffPoint false × T.CoeffPoint true=>twoFieldWeight R T k*(G k.1.val k.2.val)^2
  have wt (k : R.CoeffPoint false × T.CoeffPoint true) : 0≤twoFieldWeight R T k :=
    mul_nonneg (R.pointMass_nonneg _ _) (T.pointMass_nonneg _ _)
  have nonn k : 0≤lhs k := mul_nonneg (wt k) (sq_nonneg _)
  have dom k : lhs k ≤ u^2*(twoFieldWeight R T k*(twoFieldScore Y w E F k.1.val k.2.val)^2) := by
    have gn : 0≤G k.1.val k.2.val := by
      apply sum_nonneg;intro a _;split <;> first | exact div_nonneg (Nat.cast_nonneg _) (pe O O a) | rfl
    have sq := pow_le_pow_left₀ gn (kept k.1.val k.2.val) 2
    rw [mul_pow] at sq
    exact (mul_le_mul_of_nonneg_left sq (wt k)).trans_eq (by ring)
  have total := (Summable.of_nonneg_of_le nonn dom hs.summable).tsum_le_tsum dom hs.summable
  rw [hs.tsum_eq] at total
  exact total.trans (mul_le_mul_of_nonneg_left model (sq_nonneg u))

end
end Cogentic.Construction

#print axioms Cogentic.Construction.kept_common_overlap_envelope
