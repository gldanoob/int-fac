import Cogentic.ForcedMarginalRatios

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- Full-band insertion at the saddle determined by a mark's unprescribed mean. -/
def fullBandInsertion (b Q : ℕ) (α : ℝ) : ℝ :=
  let M := shiftedMass (primeBand b) (primeProbability α) (fun p => log p) (log (Fixed.B b))
  (Q:ℝ)^(1-α) * (M (log Q)/M 0)

private theorem insertion_transfer {v r s A e : ℝ} (ap : 0 ≤ A) (ep : 0 ≤ e) (small : e ≤ 1/2)
    (hv : |v-1| ≤ A*e) (hr : |r-1| ≤ e) (hs : |s-1| ≤ e) :
    |v*r/s-1| ≤ (3*A+4)*e := by
  have slow : 1/2 ≤ s := by linarith only [(abs_le.mp hs).1,small]
  have sp : 0<s := by linarith only [slow]
  have ru : |r| ≤ 3/2 := by
    have h := abs_sub_le r 1 0
    simp only [sub_zero,abs_one] at h
    linarith only [h,hr,small]
  have err := mul_le_mul hv ru (abs_nonneg r) (mul_nonneg ap ep)
  rw [show v*r/s-1=((v-1)*r+((r-1)-(s-1)))/s by field_simp; ring,abs_div,abs_of_pos sp,div_le_iff₀ sp]
  apply (abs_add_le ..).trans
  rw [abs_mul]
  have bracket := (abs_sub (r-1) (s-1)).trans (add_le_add hr hs)
  have m := mul_le_mul_of_nonneg_left slow (show 0 ≤ (3*A+4)*e by positivity)
  linarith only [err,bracket,m]

/-- After dividing by the unrestricted marginal, ordinary hits affect the
one-mark law only through their product and the unprescribed saddle, up to
an arbitrarily prescribed logarithmic-square relative error. -/
theorem full_band_marginal_ratio (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let O := PrescribedRows.unrestricted n ell
    let y := (exactMean n ell a side:ℝ)/targetPart n ell a side
    let P := fun R : PrescribedRows n ell => prescribedProbability R side
      (fun k=>supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2))
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log y ∧ 0<P O ∧
      ∀ R : PrescribedRows n ell, let F := fullBandInsertion b (R.hitProduct a) α
      0<F ∧ |(P R/P O)/F-1|≤C*exp (-K*(Fixed.z b:ℝ)^2) := by
  classical
  obtain ⟨A,ap,b₁,actual⟩ := forced_marginal_ratio line K hk
  obtain ⟨b₂,remove⟩ := shifted_nested_nominal_density_ratio 3 K hk
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  obtain ⟨b₄,accuracy⟩ := fixed_class_accuracy 1
  refine ⟨3*A+4,by positivity,max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell a b huge hn comp target absent mark side O y P
  obtain ⟨one,two⟩ := max_le_iff.mp (max_le_iff.mp huge).1
  obtain ⟨three,four⟩ := max_le_iff.mp (max_le_iff.mp huge).2
  obtain ⟨α,ha,mean,po,ratio⟩ := actual one hn comp target absent mark side
  refine ⟨α,ha,mean,po,?_⟩
  let J := primeBand b; let H := log (Fixed.B b:ℝ); let u := log y/H
  let M := shiftedMass J (primeProbability α) (fun p=>log p) H
  let E := eulerMass J α
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  let T := fun R : PrescribedRows n ell => R.forcedCentralFactor a side α
  let Q := fun R : PrescribedRows n ell => (R.hitProduct a:ℝ)
  have big := deg b three
  have ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have op : O.hitProduct a=1 := by simp [O,PrescribedRows.unrestricted,PrescribedRows.hitProduct,PrescribedRows.hit,prodPrimes]
  have tp : O.prefactor a side=targetPart n ell a side := by simp [PrescribedRows.prefactor,op]
  have div := total_prefactor O side target (g:=1) (a:=a) (by decide)
    (show 1≤Fixed.A b*(Fixed.B b)^2 from Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide))))
  rw [tp,Nat.cast_one,mul_one] at div
  have win := one_point_window hn big target cap grid side _ div
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos _)).ne' (Nat.succ_ne_zero _))) (by decide) : 1 < Fixed.B b))
  have mag : H*u=log y := by dsimp only [u]; field_simp
  have control (S : PrescribedRows n ell) :
      0<E*M (log (Q S)) ∧ 0<T S ∧ |T S/(E*M (log (Q S)))-1|≤e := by
    let band := (sieveBand n ell (S.prefactor a side)).filter (fun p=>¬p∣(firstStep n ell a side).natAbs)
    have sub : band⊆J := fun _ hx => (mem_filter.mp (mem_filter.mp hx).1).1
    obtain ⟨s,v,ok,_⟩ := S.first_probability ((by decide : 3≤10004).trans big) target cap (mark_range hn big cap) side
    obtain ⟨_,_,ready⟩ := first_polynomial_data S hn big comp target absent mark side s v ok
    have card : (J\band).card≤b^3 := omitted_card hn big comp target absent ready.prepos ready.prebound (Int.natAbs_pos.mpr ready.nonzero) ready.cap
    have bounds := S.subprod_bounds (s:=S.hit a) (filter_subset ..)
    have q1 : 1≤Q S := by dsimp only [Q]; exact_mod_cast bounds.1
    have q2 : Q S≤(Fixed.B b:ℝ)^2 := by dsimp only [Q]; exact_mod_cast bounds.2
    have shift : |log (Q S)|≤2*H := by
      rw [abs_of_nonneg (log_nonneg q1)]
      exact (log_le_log (zero_lt_one.trans_le q1) q2).trans_eq (by rw [log_pow]; norm_num; rfl)
    have h := remove b two u α (log (Q S)) J band win.2.2.1 win.2.2.2.1 ha.1 (mean.trans mag.symm) shift sub (Subset.rfl) card
    simpa only [sdiff_self,Finset.bot_eq_empty,omittedMass,omittedCharacteristic,notMem_empty,ite_false,shiftedMass,saddleCharacteristic,
      Q,E,M,T,J,H,band,PrescribedRows.forcedCentralFactor] using h
  have epos : 0≤e := (exp_pos _).le
  have small : e≤1/2 := (exp_le_exp.mpr
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (Fixed.z b:ℝ))] :
       -K*(Fixed.z b:ℝ)^2 ≤ -(Fixed.z b:ℝ)^2)).trans (by simpa only [one_mul] using accuracy b four)
  have eq0 : log (Q O)=0 := by simp only [Q,op,Nat.cast_one,log_one]
  have cO := control O
  rw [eq0] at cO
  have eulerPos : 0<E := eulerMass_pos ..
  have m0 : 0 < M 0 := (mul_pos_iff_of_pos_left eulerPos).mp cO.1
  intro R F
  let q := (Q R)^(1-α)
  have qp : 0<q := rpow_pos_of_pos (by dsimp only [Q]; exact_mod_cast (R.subprod_bounds (s:=R.hit a) (filter_subset ..)).1) _
  have cR := control R
  have mR : 0<M (log (Q R)) := (mul_pos_iff_of_pos_left eulerPos).mp cR.1
  change 0<q*(M (log (Q R))/M 0) ∧ _
  refine ⟨mul_pos qp (div_pos mR m0),?_⟩
  let Φ := q*(T R/T O)
  let v := (P R/P O)/Φ
  let r := T R/(E*M (log (Q R))); let s := T O/(E*M 0)
  have h := ratio R
  change 0<Φ ∧ |v-1|≤A*e at h
  have id : (P R/P O)/F=v*r/s := by
    change (P R/P O)/(q*(M (log (Q R))/M 0)) = (P R/P O)/(q*(T R/T O))*(T R/(E*M (log (Q R))))/(T O/(E*M 0))
    field_simp [qp.ne',mR.ne',m0.ne',cR.2.1.ne',cO.2.1.ne',po.ne',eulerPos.ne']
  rw [id]
  exact insertion_transfer ap.le epos small h.2 cR.2.2 cO.2.2

end
end Cogentic.Construction

#print axioms Cogentic.Construction.full_band_marginal_ratio
