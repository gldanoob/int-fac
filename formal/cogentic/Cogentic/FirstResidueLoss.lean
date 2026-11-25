import Cogentic.PolynomialExceptions

namespace Cogentic.Construction
open Cogentic.Window Finset Real
noncomputable section

/-- In a unit class the restricted Gaussian sum may first remove every
prime dividing the step, for any condition on the smooth value. -/
private theorem classPart_filter_step {q : ℕ} (J : Finset ℕ) (pr : ∀ p∈J,p.Prime)
    (Y S : ℝ) (r : (ZMod q)ˣ) (E : ℕ→Prop) [DecidablePred E] :
    classPart J Y S r E = classPart (J.filter (fun p => ¬p∣q)) Y S r E := by
  let K := J.filter (fun p => ¬p∣q)
  have kp (p) (h : p∈K) := pr p (mem_filter.mp h).1
  have sub : (squarefreeSupport K).filter E ⊆ (squarefreeSupport J).filter E := by
    intro n hn
    obtain ⟨h,ev⟩ := mem_filter.mp hn
    obtain ⟨sq,fac⟩ := (mem_squarefreeSupport K kp n).mp h
    exact mem_filter.mpr ⟨(mem_squarefreeSupport J pr n).mpr ⟨sq,fac.trans (filter_subset ..)⟩,ev⟩
  unfold classPart
  symm
  apply sum_subset sub
  intro n hn miss
  apply if_neg
  intro eq
  have cop := (ZMod.isUnit_iff_coprime n q).mp (eq ▸ r.isUnit)
  obtain ⟨full,ev⟩ := mem_filter.mp hn
  obtain ⟨sq,fac⟩ := (mem_squarefreeSupport J pr n).mp full
  apply miss
  apply mem_filter.mpr
  refine ⟨(mem_squarefreeSupport K kp n).mpr ⟨sq,?_⟩,ev⟩
  intro p hp
  exact mem_filter.mpr ⟨fac hp,fun dv => Nat.not_coprime_of_dvd_of_dvd
    (Nat.prime_of_mem_primeFactors hp).one_lt (Nat.dvd_of_mem_primeFactors hp) dv cop⟩

private theorem finite_filtered_mass (J : Finset ℕ) (c s : ℤ) (sn : s≠0)
    (r : (ZMod s.natAbs)ˣ) (rr : (r:ZMod s.natAbs)=c) (Y S : ℝ)
    (E : ℕ→Prop) [DecidablePred E] :
    (finiteScalarMass ((squarefreeSupport J).filter E) c s Y S).re =
      (s.natAbs:ℝ)*classPart J Y S r E := by
  let A := (squarefreeSupport J).filter E
  change (s.natAbs:ℝ)/S*(∑' j : ℤ, if c+s*j∈A.image (fun k : ℕ => (k:ℤ)) then
    coeffGaussian (c+s*j:ℤ) Y S else 0) = _
  rw [affine_support_sum A c s sn (fun n => coeffGaussian n Y S)]
  unfold classPart
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro n _
  rw [rr]
  split <;> simp [coeffGaussian,gaussian]
  ring

/-- Transfer a relative class bound for any condition on the smooth first
quotient to its actual coefficient probability. The same unit class works
for every condition, including conditions modulo a multiple of the first step. -/
theorem PrescribedRows.first_filter_transfer {n ell a : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) :
    let b := n.log2+1
    let pre := R.prefactor a side; let q := (firstStep n ell a side).natAbs
    let J := sieveBand n ell pre; let K := J.filter (fun t => ¬t∣q)
    let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
    let val := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue J (val k)
    ∃ r : (ZMod q)ˣ, ∀ (F : ℤ→Prop) [DecidablePred F] (rate : ℝ), 0≤rate →
      classPart K Y S r (fun j : ℕ => F j) ≤ rate*classWeight K Y S r →
      prescribedProbability R side (fun k => smooth k ∧ F (val k)) ≤
        (1+270*exp (-(Fixed.U b:ℝ)))*rate*prescribedProbability R side smooth := by
  classical
  intro b pre q J K Y S val smooth
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  obtain ⟨u,v,ok,est⟩ := R.first_finite_probability (le_trans (by decide : 3≤10004) big)
    target cap (mark_range hn big cap) side
  let c := R.intercept a side u v; let s := firstStep n ell a side
  obtain ⟨cop,_,data⟩ := first_polynomial_data R hn big comp target absent mark side u v ok
  change commonDivisor c s=1 at cop
  let : NeZero s.natAbs := ⟨Int.natAbs_ne_zero.mpr data.nonzero⟩
  let r : (ZMod q)ˣ := ZMod.unitOfCoprime (scalarResidue c s) cop
  have rr : (r:ZMod q)=c := (ZMod.coe_unitOfCoprime _ _).trans (ZMod.natCast_zmod_val _)
  let ε : ℝ := 90*exp (-(Fixed.U b:ℝ))
  let full := (q:ℝ)*classWeight K Y S r
  have ep : 0<ε := by dsimp [ε]; positivity
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have up : 720≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 720≤2^10).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have small : ε≤1/8 := by
    dsimp [ε]; rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    linarith only [up,add_one_le_exp (Fixed.U b:ℝ)]
  have pr (p) (mem : p∈J) := (mem_primeBand.mp (mem_filter.mp mem).1).1
  have transfer (F : ℤ→Prop) [DecidablePred F] :
      let part := (q:ℝ)*classPart K Y S r (fun j : ℕ => F j)
      |prescribedProbability R side (fun k => smooth k ∧ F (val k)) - part| ≤ ε*part := by
    let A := (squarefreeSupport J).filter (fun j : ℕ => F j)
    have equiv (z : ℤ) : finiteValue A z ↔ supportedValue J z ∧ F z := by
      constructor
      · intro mem
        obtain ⟨t,ht,eq⟩ := mem_image.mp mem
        exact ⟨mem_image.mpr ⟨t,(mem_filter.mp ht).1,eq⟩,eq ▸ (mem_filter.mp ht).2⟩
      · rintro ⟨hit,ev⟩
        obtain ⟨t,ht,eq⟩ := mem_image.mp hit
        exact mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,eq.symm ▸ ev⟩,eq⟩
    have eq : (fun k : ℤ×ℤ => finiteValue A (val k)) = (fun k => smooth k ∧ F (val k)) :=
      funext (fun k => propext (equiv _))
    have mass := finite_filtered_mass J c s data.nonzero r rr Y S (fun j : ℕ => F j)
    rw [classPart_filter_step J pr] at mass
    have bound := est A
    change |prescribedProbability R side (fun k => finiteValue A (val k)) -
      (finiteScalarMass A c s Y S).re| ≤ ε*(finiteScalarMass A c s Y S).re at bound
    simpa only [eq,mass,A] using bound
  have base : |prescribedProbability R side smooth-full|≤ε*full := by
    have h := transfer (fun _ => True)
    simpa [full,classPart,classWeight] using h
  have fp : 0≤full := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans base) ep
  have scaled : (1+ε)*full ≤ (1+3*ε)*prescribedProbability R side smooth := by
    have low := (abs_le.mp base).1
    have a₁ : (1+ε)≤(1+3*ε)*(1-ε) := by nlinarith only [mul_nonneg ep.le (show 0≤1-3*ε by linarith only [small])]
    exact (mul_le_mul_of_nonneg_right a₁ fp).trans (by rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); linarith only [low])
  refine ⟨r,?_⟩
  intro F inst rate ratePos bound
  have part := transfer F
  dsimp only at part
  have hb := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg (α:=ℝ) q)
  have mult := mul_le_mul_of_nonneg_left hb (show 0≤1+ε by positivity)
  have scaled' := mul_le_mul_of_nonneg_left scaled ratePos
  change _ ≤ (1+270*exp (-(Fixed.U b:ℝ)))*rate*prescribedProbability R side smooth
  change (1+ε)*full ≤ _ at scaled
  have fe : 1+270*exp (-(Fixed.U b:ℝ))=1+3*ε := by dsimp only [ε]; ring
  rw [fe]
  dsimp only [full] at scaled'
  nlinarith only [(abs_le.mp part).2,mult,scaled']

/-- For any extra prime coprime to the first step, a nonzero class of the
actual first smooth quotient costs at most 9/(p-1). The zero class costs at
most 18 p^(-α). Both bounds include the coefficient Gaussian normalizer. -/
theorem PrescribedRows.first_residue_probability (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side
    let q := (firstStep n ell a side).natAbs
    let J := sieveBand n ell pre
    let val := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue J (val k)
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log ((exactMean n ell a side:ℝ)/pre) ∧
      ∀ p : ℕ, p.Prime → p≤Fixed.A b → q.Coprime p → ∀ z : ZMod p,
        prescribedProbability R side (fun k => smooth k ∧ z=(val k:ZMod p)) ≤
          (1+270*exp (-(Fixed.U b:ℝ)))*(if z=0 then 18*(p:ℝ)^(-α) else 9/((p:ℝ)-1))*
            prescribedProbability R side smooth := by
  classical
  obtain ⟨n₁,exception⟩ := first_polynomial_exceptional line
  obtain ⟨n₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max n₁ n₂,?_⟩
  intro n ell a R b large hn comp target absent mark side pre q J val smooth
  have big := degree b (max_le_iff.mp large).2
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  obtain ⟨u,v,ok,_⟩ := R.first_probability (le_trans (by decide : 3≤10004) big)
    target cap (mark_range hn big cap) side
  obtain ⟨α,ha,mean,exc⟩ := exception R (max_le_iff.mp large).1 hn comp target absent mark side u v ok
  refine ⟨α,ha,mean,?_⟩
  let K := J.filter (fun t => ¬t∣q)
  let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
  obtain ⟨r,transfer⟩ := R.first_filter_transfer hn big comp target absent mark side
  intro p pp capP copP z
  let : Fact p.Prime := ⟨pp⟩
  let rate : ℝ := if z=0 then 18*(p:ℝ)^(-α) else 9/((p:ℝ)-1)
  have pn : (1:ℝ)<p := by exact_mod_cast pp.one_lt
  have ratePos : 0≤rate := by dsimp [rate]; split <;> positivity
  have cl := exc p pp capP copP r
  have bound : classPart K Y S r (fun j : ℕ => z=(j:ZMod p)) ≤ rate*classWeight K Y S r := by
    by_cases zero : z=0
    · have eq : (fun j : ℕ => z=(j:ZMod p)) = (p∣·) := funext (fun j => propext (by rw [zero,eq_comm,ZMod.natCast_eq_zero_iff]))
      simp only [eq]
      have w := Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) p) (-α)
      have pw : primeProbability α p ≤ (p:ℝ)^(-α) := div_le_self w (by linarith only [w])
      obtain ⟨_,_,data⟩ := first_polynomial_data R hn big comp target absent mark side u v ok
      have sp := div_pos data.width (show 0<(pre:ℝ) by exact_mod_cast data.prepos)
      have wp : 0≤classWeight K Y S r := sum_nonneg (fun j _ => by split <;> first | exact (div_pos (exp_pos _) sp).le | rfl)
      simpa only [rate,if_pos zero] using cl.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pw (by norm_num : (0:ℝ)≤18)) wp)
    · have h := cl.1 (Units.mk0 z zero)
      simp only [Units.val_mk0] at h
      rw [show rate=9/((p:ℝ)-1) from if_neg zero]
      convert h using 1
      congr 1
  apply transfer (fun t : ℤ => z=(t:ZMod p)) rate ratePos
  simpa only [Int.cast_natCast] using bound

/-- Uniform loss of one exceptional first-value residue at a band prime,
including the passage to the Gaussian coefficient law. -/
theorem band_residue_rate {b p : ℕ} (bp : 0<b) (mem : p∈primeBand b) {α : ℝ}
    (ha : 199/200≤α) :
    (1+270*exp (-(Fixed.U b:ℝ)))*max (18*(p:ℝ)^(-α)) (9/((p:ℝ)-1)) ≤
      36*(Fixed.B b:ℝ)^(-199/400:ℝ) := by
  obtain ⟨pp,_,top⟩ := mem_primeBand.mp mem
  have two : (2:ℝ)≤p := by exact_mod_cast pp.two_le
  have one : (1:ℝ)≤p := by linarith only [two]
  have pos : (0:ℝ)<p := by linarith only [two]
  have BB : (0:ℝ)<Fixed.B b := by unfold Fixed.B; positivity
  let δ := (Fixed.B b:ℝ)^(-199/400:ℝ)
  have past : (p:ℝ)^(-(199/200):ℝ) ≤ δ := calc
    _ ≤ (sqrt (Fixed.B b:ℝ))^(-(199/200):ℝ) := by
      apply rpow_le_rpow_of_nonpos (sqrt_pos.mpr BB) _ (by norm_num)
      exact (sqrt_le_left pos.le).mpr (by exact_mod_cast top.le)
    _ = _ := by dsimp [δ]; rw [sqrt_eq_rpow,←rpow_mul BB.le]; norm_num
  have z := (rpow_le_rpow_of_exponent_le one (neg_le_neg ha)).trans past
  have u : 9/((p:ℝ)-1) ≤ 18*δ := calc
    _ ≤ 18/(p:ℝ) := by rw [div_le_div_iff₀ (by linarith only [two]) pos]; linarith only [two]
    _ = 18*(p:ℝ)^(-1:ℝ) := by rw [rpow_neg_one,div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((rpow_le_rpow_of_exponent_le one (by norm_num : (-1:ℝ)≤ -(199/200))).trans past) (by norm_num)
  have mx : max (18*(p:ℝ)^(-α)) (9/((p:ℝ)-1)) ≤ 18*δ :=
    max_le (mul_le_mul_of_nonneg_left z (by norm_num)) u
  have vp : 0<Fixed.v b := Nat.mul_pos (Fixed.degree_pos bp) (Nat.mul_pos (Fixed.degree_pos bp) (Nat.succ_pos _))
  have up : 270≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 270≤2^10).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have norm : 1+270*exp (-(Fixed.U b:ℝ))≤2 := by
    rw [exp_neg,←div_eq_mul_inv,←le_sub_iff_add_le',div_le_iff₀ (exp_pos _)]
    linarith only [up,add_one_le_exp (Fixed.U b:ℝ)]
  calc _ ≤ (1+270*exp (-(Fixed.U b:ℝ)))*(18*δ) := mul_le_mul_of_nonneg_left mx (by positivity)
       _ ≤ 2*(18*δ) := mul_le_mul_of_nonneg_right norm (by dsimp [δ]; positivity)
       _ = _ := by dsimp [δ]; ring

theorem PrescribedRows.band_first_residue_probability (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let J := sieveBand n ell (R.prefactor a side)
    let val := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue J (val k)
    ∀ p∈primeBand b, (firstStep n ell a side).natAbs.Coprime p → ∀ z : ZMod p,
      prescribedProbability R side (fun k => smooth k ∧ z=(val k:ZMod p)) ≤
        (36*(Fixed.B b:ℝ)^(-199/400:ℝ))*prescribedProbability R side smooth := by
  obtain ⟨b₀,all⟩ := PrescribedRows.first_residue_probability line
  refine ⟨b₀,?_⟩
  intro n ell a R b large hn comp target absent mark side J val smooth p pm co z
  obtain ⟨α,ha,_,cases⟩ := all R large hn comp target absent mark side
  obtain ⟨pp,upper,_⟩ := mem_primeBand.mp pm
  have cap : p≤Fixed.A b := upper.trans (Nat.pow_le_pow_right (by decide) (by dsimp [Fixed.beta]; omega))
  apply (cases p pp cap co z).trans
  have p0 : 0≤prescribedProbability R side smooth := by
    unfold prescribedProbability
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | rfl | exact mul_nonneg (exp_pos _).le (exp_pos _).le
    · exact tsum_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)
  apply mul_le_mul_of_nonneg_right _ p0
  apply le_trans _ (band_residue_rate (Nat.succ_pos _) pm ha.1)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  split <;> first | exact le_max_left .. | exact le_max_right ..

#print axioms PrescribedRows.band_first_residue_probability

#print axioms PrescribedRows.first_filter_transfer

#print axioms PrescribedRows.first_residue_probability

end
end Cogentic.Construction
