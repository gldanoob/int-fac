import Cogentic.FarNominalPair
import Cogentic.AdmissionMoments
import Cogentic.FixedPairCovariance

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- The dependence of the central factor on the prescribed ordinary roots,
with the saddle fixed at the mark's unprescribed center. -/
def PrescribedRows.forcedCentralFactor {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) (side : Bool) (α : ℝ) : ℝ :=
  let b := n.log2+1
  let band := (sieveBand n ell (R.prefactor a side)).filter (fun p=>¬p∣(firstStep n ell a side).natAbs)
  eulerMass band α * omittedMass (primeBand b) (primeBand b \ band) (primeProbability α)
    (fun p=>log p) (log (Fixed.B b)) (log (R.hitProduct a))

def PrescribedRows.forcedDensity {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) (side : Bool) (α : ℝ) : ℝ :=
  coprimeFactor (firstStep n ell a side).natAbs *
    ((exactMean n ell a side:ℝ)/(R.prefactor a side))^(α-1) * R.forcedCentralFactor a side α/(2*π)

private theorem transfer_density {p z m ε C η : ℝ} (mp : 0 < m) (cp : 0≤C) (ep : 0≤ε)
    (es : ε≤1) (ηs : η≤ε) (ηp : 0<η) (rough : |p-z|≤90*η*z) (model : |z-m|≤C*ε*m) :
    |p-m|≤(90*(1+C)+C)*ε*m := by
  have zp : 0≤z := by by_contra! neg; exact (not_lt_of_ge ((abs_nonneg _).trans rough)) (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ηp) neg)
  have small := mul_le_mul_of_nonneg_left es cp
  have bound : z≤(1+C)*m := by linarith only [(abs_le.mp model).2,mul_le_mul_of_nonneg_right small mp.le]
  have e := mul_le_mul (mul_le_mul_of_nonneg_left ηs (by norm_num : (0:ℝ)≤90)) bound zp (by positivity : 0≤90*ε)
  exact (abs_sub_le p z m).trans (by linarith only [rough,model,e])

/-- A single saddle serves all ordinary root prescriptions at one mark,
including every miss, either ordinary hit, both hits and either target status. -/
theorem common_saddle_marginals (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let y₀ := (exactMean n ell a side:ℝ)/targetPart n ell a side
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log y₀ ∧
      ∀ R : PrescribedRows n ell,
      let J := sieveBand n ell (R.prefactor a side)
      let p := prescribedProbability R side (fun k=>supportedValue J (R.intercept a side k.1 k.2))
      let m := R.forcedDensity a side α
      0 < m ∧ |p-m|≤C*exp (-K*(Fixed.z b:ℝ)^2)*m := by
  obtain ⟨C,cp,b₁,scalar⟩ := scalar_progression_relative line K hk
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  obtain ⟨b₃,save⟩ := fixed_band_power_savings K hk
  obtain ⟨_,_,b₄,baseSaddle⟩ := PrescribedRows.first_nominal_marginal line 1 le_rfl
  refine ⟨90*(1+C)+C,by positivity,max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell a b huge hn comp target absent mark side y₀
  obtain ⟨one,two⟩ := max_le_iff.mp (max_le_iff.mp huge).1
  obtain ⟨three,four⟩ := max_le_iff.mp (max_le_iff.mp huge).2
  let O := PrescribedRows.unrestricted n ell
  have basepre : O.prefactor a side=targetPart n ell a side := by
    simp [O,PrescribedRows.unrestricted,PrescribedRows.prefactor,PrescribedRows.hitProduct,PrescribedRows.hit,prodPrimes]
  obtain ⟨α,ha,mean,_,_⟩ := baseSaddle O four hn comp target absent mark side
  rw [basepre] at mean
  refine ⟨α,ha,mean,?_⟩
  intro R J p m
  let H := log (Fixed.B b:ℝ); let u := log y₀/H
  let Q := R.hitProduct a; let t := targetPart n ell a side
  let N : ℝ := exactMean n ell a side; let S := oneWidth n ell a
  let y := N/(R.prefactor a side:ℝ)
  have big := degree b two
  have ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have am := mark_range hn big cap
  obtain ⟨s₀,s₁,ok,prob⟩ := R.first_probability ((by decide : 3≤10004).trans big) target cap am side
  let c := R.intercept a side s₀ s₁; let s := firstStep n ell a side
  obtain ⟨unit,_,ready⟩ := first_polynomial_data R hn big comp target absent mark side s₀ s₁ ok
  change commonDivisor c s=1 at unit
  have Qb := R.subprod_bounds (s:=R.hit a) (filter_subset ..)
  have qp : 0 < (Q:ℝ) := by exact_mod_cast Qb.1
  have tp : 0 < (t:ℝ) := by
    have := (O.pre_bounds target a side).1
    rw [basepre] at this
    exact_mod_cast this
  have baseDiv := total_prefactor O side target (g:=1) (a:=a) (by decide)
    (show 1≤Fixed.A b*(Fixed.B b)^2 from Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide))))
  rw [basepre,Nat.cast_one,mul_one] at baseDiv
  have win := one_point_window hn big target cap grid side _ baseDiv
  have yp : 0<y₀ := zero_lt_one.trans_le win.2.1
  have bgt : 1 < Fixed.B b := Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos _)).ne' (Nat.succ_ne_zero _))) (by decide)
  have hp : 0<H := log_pos (by exact_mod_cast bgt)
  have mu : H*u=log y₀ := by dsimp only [u]; field_simp
  have eqY : y=y₀/Q := by dsimp only [y,y₀,N,PrescribedRows.prefactor,Q]; rw [Nat.cast_mul,div_div]
  have shift : H*u-log y=log Q := by rw [mu,eqY,log_div yp.ne' qp.ne']; ring
  have lg : |H*u-log y| ≤ 2*H := by
    rw [shift,abs_of_nonneg (log_nonneg (show 1≤(Q:ℝ) by exact_mod_cast Qb.1))]
    have upper : (Q:ℝ) ≤ (Fixed.B b:ℝ)^2 := by exact_mod_cast Qb.2
    exact (log_le_log qp upper).trans_eq (by rw [log_pow]; norm_num; rfl)
  have scale := scalar c s N S u one hn comp target absent ready.prepos ready.prebound
    ready.nonzero ready.cap ready.width ready.window win.2.2.1 win.2.2.2.1
  have lg' : |H*u-log (N/((R.prefactor a side:ℝ)*(commonDivisor c s:ℝ)))|≤2*H := by simpa only [unit,Nat.cast_one,mul_one] using lg
  have sup : commonDivisor c s∈squarefreeSupport J := by
    rw [unit]; exact mem_image.mpr ⟨∅,mem_powerset.mpr (empty_subset _),by simp⟩
  obtain ⟨β,hβ,mβ,mpos,estimate⟩ := (scale lg').2 sup
  have bg : (Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime=primeBand b := by simp [primeBand]
  have unique := band_saddle_unique (B:=(Fixed.B b:ℝ)) (by exact_mod_cast bgt) (by linarith only [hβ.1] : 0≤β) (by linarith only [ha.1] : 0≤α)
  dsimp only at unique
  rw [bg] at unique
  change saddleMean (primeBand b) β=H*u at mβ
  have up : 0<u := by
    have w : 90*(Fixed.d b:ℝ) ≤ u := win.2.2.1
    have dr : (10004:ℝ)≤Fixed.d b := by exact_mod_cast big
    linarith only [w,dr]
  have same : β=α := unique (mβ.symm ▸ mul_pos hp up) (mβ.trans (mu.trans mean.symm))
  subst β
  simp only [unit,Nat.div_one,Nat.cast_one,mul_one] at mpos estimate
  let band := J.filter (fun p=>¬p∣s.natAbs)
  let raw := ((s.natAbs:ℝ)/s.natAbs.totient)*(y^(α-1)*eulerMass band α)*
    omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p=>log p) H (H*u-log y)
  let z := (scalarMass J c s y (S/R.prefactor a side)).re
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  change 0 < raw at mpos
  have eq : m=raw/(2*π) := by
    dsimp only [m,PrescribedRows.forcedDensity,PrescribedRows.forcedCentralFactor,coprimeFactor,raw]
    rw [shift]
    ring
  have piPos : 0 < 2*π := by positivity
  have mp : 0 < m := eq ▸ div_pos mpos piPos
  have reEst := (Complex.abs_re_le_norm _).trans estimate
  simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re] at reEst
  change |(2*π)*z-raw|≤C*raw*e at reEst
  have err : |z-m|≤C*e*m := by
    rw [eq,show z-raw/(2*π)=((2*π)*z-raw)/(2*π) by field_simp,abs_div,abs_of_pos piPos,div_le_iff₀ piPos]
    exact reEst.trans_eq (by field_simp)
  refine ⟨mp,transfer_density mp cp.le (exp_pos _).le ?_ ?_ (exp_pos _) prob err⟩
  · exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hk]) (sq_nonneg _))
  · exact (normalization_band_saving (b:=b) (Nat.succ_pos _)).trans (save b three)

private theorem relative_quotient {x y m n ε : ℝ} (mp : 0 < m) (np : 0<n) (ep : 0≤ε) (small : ε≤1/2)
    (a : |x-m|≤ε*m) (b : |y-n|≤ε*n) :
    0<y ∧ |(x/y)/(m/n)-1|≤4*ε := by
  have near {z t : ℝ} (tp : 0<t) (h : |z-t|≤ε*t) : |z/t-1|≤ε := by
    rw [div_sub_one tp.ne',abs_div,abs_of_pos tp,div_le_iff₀ tp]
    exact h
  have M := near mp a
  have N := near np b
  have low : 1/2≤y/n := by linarith only [(abs_le.mp N).1,small]
  have pos : 0<y/n := (by norm_num : (0:ℝ)<1/2).trans_le low
  have yp : 0<y := (div_pos_iff_of_pos_right np).mp pos
  refine ⟨yp,?_⟩
  rw [show (x/y)/(m/n)-1=(x/m-y/n)/(y/n) by field_simp,abs_div,abs_of_pos pos,div_le_iff₀ pos]
  have dist := abs_sub_le (x/m) 1 (y/n)
  rw [abs_sub_comm 1] at dist
  linarith only [dist,M,N,mul_le_mul_of_nonneg_left low (show 0≤4*ε by positivity)]

private theorem forced_density_scale {n ell a : ℕ} (R : PrescribedRows n ell) (side : Bool) (α : ℝ)
    (qp : 0<(R.hitProduct a:ℝ)) (yp : 0<(exactMean n ell a side:ℝ)/(targetPart n ell a side:ℝ)) :
    let y := (exactMean n ell a side:ℝ)/(targetPart n ell a side:ℝ)
    let scale := coprimeFactor (firstStep n ell a side).natAbs*y^(α-1)/(2*π)
    R.forcedDensity a side α=scale*(R.hitProduct a:ℝ)^(1-α)*R.forcedCentralFactor a side α := by
  intro y scale
  have val : (exactMean n ell a side:ℝ)/(R.prefactor a side:ℝ) = y/(R.hitProduct a:ℝ) := by
    simp only [y,PrescribedRows.prefactor,Nat.cast_mul,div_div]
  unfold PrescribedRows.forcedDensity
  rw [val,div_rpow yp.le qp.le,show 1-α= -(α-1) by ring,rpow_neg qp.le]
  dsimp only [scale]
  ring

/-- Ratio of the prescribed mark probability to the true unrestricted
marginal. The remaining Euler and shifted central factors all use the
same unprescribed saddle. -/
theorem forced_marginal_ratio (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let O := PrescribedRows.unrestricted n ell
    let y := (exactMean n ell a side:ℝ)/targetPart n ell a side
    let P := fun R : PrescribedRows n ell => prescribedProbability R side
      (fun k=>supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2))
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log y ∧ 0<P O ∧
      ∀ R : PrescribedRows n ell,
      let Φ := (R.hitProduct a:ℝ)^(1-α)*(R.forcedCentralFactor a side α/O.forcedCentralFactor a side α)
      0<Φ ∧ |(P R/P O)/Φ-1|≤C*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨A,ap,b₁,model⟩ := common_saddle_marginals line K hk
  obtain ⟨b₂,accuracy⟩ := fixed_class_accuracy A
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 10004
  refine ⟨4*A,by positivity,max b₁ (max b₂ b₃),?_⟩
  intro n ell a b huge hn comp target absent mark side O y P
  obtain ⟨one,rest⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp rest
  obtain ⟨α,ha,mean,compare⟩ := model one hn comp target absent mark side
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  have small : A*e≤1/2 := (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
    (by nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (Fixed.z b:ℝ))] :
      -K*(Fixed.z b:ℝ)^2 ≤ -(Fixed.z b:ℝ)^2)) ap.le).trans (accuracy b two)
  let m := fun R : PrescribedRows n ell=>R.forcedDensity a side α
  have est (R : PrescribedRows n ell) := compare R
  change ∀ R, 0 < m R ∧ |P R-m R|≤A*e*m R at est
  have ep : 0≤A*e := mul_nonneg ap.le (exp_pos _).le
  have h (R : PrescribedRows n ell) := relative_quotient (est R).1 (est O).1 ep small (est R).2 (est O).2
  refine ⟨α,ha,mean,(h O).1,?_⟩
  intro R Φ
  have op : O.hitProduct a=1 := by simp [O,PrescribedRows.unrestricted,PrescribedRows.hitProduct,PrescribedRows.hit,prodPrimes]
  have tp : O.prefactor a side=targetPart n ell a side := by simp [PrescribedRows.prefactor,op]
  have ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have big := degree b three
  have Bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have div := total_prefactor O side target (g:=1) (a:=a) (by decide)
    (show 1≤Fixed.A b*(Fixed.B b)^2 from Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos Bp))
  rw [tp,Nat.cast_one,mul_one] at div
  have yp : 0<y := zero_lt_one.trans_le (one_point_window hn big target cap grid side _ div).2.1
  let scale := coprimeFactor (firstStep n ell a side).natAbs*y^(α-1)/(2*π)
  have sf (S : PrescribedRows n ell) : m S=scale*(S.hitProduct a:ℝ)^(1-α)*S.forcedCentralFactor a side α :=
    forced_density_scale S side α (by exact_mod_cast (S.subprod_bounds (s:=S.hit a) (filter_subset ..)).1) yp
  have base := sf O
  rw [op,Nat.cast_one,one_rpow,mul_one] at base
  have nz : scale*O.forcedCentralFactor a side α ≠ 0 := base ▸ (est O).1.ne'
  have id : m R/m O=Φ := by
    rw [sf R,base]
    dsimp only [Φ]
    field_simp [(mul_ne_zero_iff.mp nz).1,(mul_ne_zero_iff.mp nz).2]
  refine ⟨id ▸ div_pos (est R).1 (est O).1,?_⟩
  exact (id ▸ (h R).2).trans_eq (by ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.forced_marginal_ratio
