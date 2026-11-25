import Cogentic.BoxWitness
import Cogentic.PolynomialRelative

namespace Cogentic.Construction
open Real Cogentic.Window

private theorem model_floor (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (Y S α : ℝ) (band : Finset ℕ) (q : ℕ),
      InWindow b Y S → α∈Set.Icc (199/200:ℝ) 1 →
      saddleMean (primeBand b) α=log Y → 0<q →
      (primeBand b\band).card ≤ b^3 →
      let F := (q:ℝ)/q.totient*(Y^(α-1)*eulerMass band α)*
        omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p => log p) (log (Fixed.B b)) 0
      exp (-444*(Fixed.h b:ℝ)) ≤ F ∧ (1-α)*log (Fixed.B b) ≤ 4*(Fixed.z b:ℝ) ∧
        exp (-4*(Fixed.h b:ℝ))*(Y^(α-1)*eulerMass band α) ≤ F := by
  obtain ⟨b₁,lower⟩ := fixed_central_mass_lower 3
  obtain ⟨b₂,degrees⟩ := Fixed.degree_grows 50000
  obtain ⟨C,cp,tilt⟩ := fixed_saddle_euler_margin line
  obtain ⟨b₃,overhead⟩ := fixed_prime_overhead C cp 0
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro b hb Y S α band q win ha mean qp cnt
  let H := log (Fixed.B b); let d := Fixed.d b
  let u := log Y/H; let D := primeBand b\band
  let M := omittedMass (primeBand b) D (primeProbability α) (fun p => log p) H 0
  have ⟨two,three⟩ := max_le_iff.mp ((le_max_right ..).trans hb)
  have big := degrees b two
  change 50000≤d at big
  have bp := big.trans (Fixed.degree_le_bits b)
  have pos := (fixed_band_log_bounds b (by omega) (show 16≤d by omega)).1
  change 1000*(d:ℝ)≤H at pos
  have dp : 50000 ≤ (d:ℝ) := by exact_mod_cast big
  have Hpos : 0<H := by linarith
  have hu : H*u=log Y := by dsimp [u]; field_simp
  have low : 90*(d:ℝ) ≤ u := win.2.2.1
  have high : u ≤ 110*(d:ℝ) := win.2.2.2.1
  have ud : 1≤u := by linarith
  have eq : (Finset.Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime=primeBand b := by simp [primeBand]
  have L := lower b ((le_max_left ..).trans hb) u α 0 D
  dsimp only at L
  rw [eq] at L
  have ml : 1/(2*H*sqrt u) ≤ M := L low high ha.1 (mean.trans hu.symm)
    (by rw [abs_zero]; positivity) cnt Finset.sdiff_subset
  let z := (Fixed.z b:ℝ)
  let h := (Fixed.h b:ℝ)
  let B := (Fixed.B b:ℝ)
  have hz : 1≤z := by change (1:ℝ)≤(↑(b.log2+1):ℝ); exact_mod_cast Nat.le_add_left 1 b.log2
  have dh : (d:ℝ)*z = h := by simp only [h,Fixed.h,Nat.cast_mul,d,z]
  have zh : z≤h := by nlinarith only [dh,mul_nonneg (show 0≤(d:ℝ)-1 by linarith) (zero_le_one.trans hz)]
  have hb16 : 16≤B := by
    have Bp : 0<B := by dsimp [B,Fixed.B]; positivity
    have eh := add_one_le_exp H
    rw [show exp H = B from exp_log Bp] at eh
    linarith only [eh,pos,dp]
  have small := overhead b three ∅ (by simp)
  simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at small
  have mean' := mean.trans hu.symm
  have dl : log d ≤ z := by
    have db : (d:ℝ)≤b := by exact_mod_cast Fixed.degree_le_bits b
    have bz : (b:ℝ)≤(2:ℝ)^(Fixed.z b) := by exact_mod_cast Nat.lt_log2_self.le
    have ez := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
      (by linarith [exp_one_gt_d9] : (2:ℝ)≤exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at ez
    exact (log_le_iff_le_exp (by positivity : 0<(d:ℝ))).mpr (db.trans (bz.trans ez))
  have lam : (1-α)*H ≤ 4*z := by
    by_cases enough : 2 ≤ (1-α)*H
    · have input := tilt B α u ∅ hb16 ha.1 ha.2 (small.trans (by norm_num))
      dsimp only at input
      rw [eq] at input
      have logu := (input (Finset.empty_subset _) mean' enough).2.1
      have cap : 16*u+4 ≤ (d:ℝ)^2 := by nlinarith only [high,dp,mul_nonneg (show 0≤(d:ℝ)-1764 by linarith) (show 0≤(d:ℝ) by positivity)]
      have lg := log_le_log (show 0<16*u+4 by linarith) cap
      rw [log_pow] at lg
      change (1-α)*H ≤ 2*log (16*u+4) at logu
      norm_num only [Nat.cast_ofNat] at lg
      linarith only [lg,dl,logu]
    · linarith only [lt_of_not_ge enough,hz]
  have gain : exp (-440*h) ≤ Y^(α-1) := by
    rw [rpow_def_of_pos (zero_lt_one.trans_le win.2.1),exp_le_exp,←hu]
    have scale := mul_le_mul lam high (zero_le_one.trans ud) (show 0≤4*z by positivity)
    linarith only [scale,dh]
  have mc : exp (-4*h) ≤ M := by
    have bound := fixed_central_scale big high
    have num : (2000:ℝ)≤exp h := by
      have ge := mul_le_mul_of_nonneg_left hz (show 0≤(d:ℝ) by positivity)
      linarith only [ge,dh,dp,add_one_le_exp h]
    have cap : 2*H*sqrt u ≤ exp (4*h) := by
      refine bound.trans ((mul_le_mul num (exp_le_exp.mpr (show 3*z≤3*h by linarith only [zh])) (exp_pos _).le (exp_pos _).le).trans_eq ?_)
      rw [←exp_add]; ring_nf
    apply le_trans _ ml
    rw [show -4*h= -(4*h) by ring,exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by positivity) cap
  have rc : 1 ≤ (q:ℝ)/q.totient := (one_le_div (by exact_mod_cast Nat.totient_pos.mpr qp : (0:ℝ)<q.totient)).mpr
    (by exact_mod_cast Nat.totient_le q)
  have eu : 1 ≤ eulerMass band α := Finset.one_le_prod (fun p _ => by
    change 1 ≤ 1+(p:ℝ)^(-α); linarith [rpow_nonneg (Nat.cast_nonneg p) (-α)])
  have pref := mul_le_mul rc (mul_le_mul gain eu (by norm_num) (rpow_nonneg (by linarith only [win.2.1]) _))
    (show 0≤exp (-440*h)*1 by positivity) (zero_le_one.trans rc)
  simp only [mul_one,one_mul] at pref
  have main := mul_le_mul pref mc (exp_pos _).le ((exp_pos _).le.trans pref)
  rw [←exp_add,show -440*h+ -4*h = -444*h by ring] at main
  have pos : 0≤Y^(α-1)*eulerMass band α := mul_nonneg (rpow_nonneg (zero_lt_one.trans_le win.2.1).le _) (eulerMass_pos _ _).le
  refine ⟨main,lam,?_⟩
  rw [mul_comm (exp (-4*h))]
  exact mul_le_mul (le_mul_of_one_le_left pos rc) mc (exp_pos _).le (mul_nonneg (zero_le_one.trans rc) pos)

/-- At every eligible mark, the actual coefficient probability of the
prescribed smooth event has a uniform positive lower bound. -/
theorem PrescribedRows.smooth_probability_saddle_floor (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side
    let P := prescribedProbability R side
      (fun k => supportedValue (sieveBand n ell pre) (R.intercept a side k.1 k.2))
    let y := (exactMean n ell a side:ℝ)/pre
    let band := (sieveBand n ell pre).filter (fun p => ¬p∣(firstStep n ell a side).natAbs)
    8/(Fixed.B b:ℝ) ≤ P ∧ ∃ α∈Set.Icc (199/200:ℝ) 1, 0<y ∧ (1-α)*log (Fixed.B b)≤4*(Fixed.z b:ℝ) ∧
      exp (-4*(Fixed.h b:ℝ))*(y^(α-1)*eulerMass band α) ≤ 8*π*P := by
  obtain ⟨C,cp,b₁,estimate⟩ := first_polynomial_progression line 1 le_rfl
  obtain ⟨b₂,floor⟩ := model_floor line
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ (max b₂ (max b₃ (2^(⌈2*C⌉₊+1)))),?_⟩
  intro n ell a R b huge hn comp target absent mark side pre
  obtain ⟨one,rest⟩ := max_le_iff.mp huge
  obtain ⟨two,rest⟩ := max_le_iff.mp rest
  obtain ⟨three,four⟩ := max_le_iff.mp rest
  have big := degree b three
  let z : ℝ := Fixed.z b
  have logb := (Nat.le_log2 (by dsimp only [b]; omega : b≠0)).mpr four
  have cz : 2*C ≤ z := (Nat.le_ceil _).trans (by change (⌈2*C⌉₊:ℝ)≤(↑(b.log2+1):ℝ); exact_mod_cast (by omega : ⌈2*C⌉₊≤b.log2+1))
  have z1 : 1≤z := by change (1:ℝ)≤(↑(b.log2+1):ℝ); exact_mod_cast Nat.le_add_left 1 b.log2
  have decay : C*exp (-z^2) ≤ 1/2 := by
    rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    nlinarith only [add_one_le_exp (z^2),mul_nonneg (sub_nonneg.mpr z1) (zero_le_one.trans z1),cz]
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have Up : 180≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 180≤2^8).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have normSmall : 90*exp (-(Fixed.U b:ℝ))≤1/2 := by
    rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    linarith only [Up,add_one_le_exp (Fixed.U b:ℝ)]
  obtain ⟨_,cap,_,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  obtain ⟨u,v,ok,prob⟩ := R.first_probability ((by decide : 3≤10004).trans big) target cap (mark_range hn big cap) side
  let c := R.intercept a side u v; let s := firstStep n ell a side
  let J := sieveBand n ell pre; let Y := (exactMean n ell a side:ℝ)/pre
  let S := oneWidth n ell a/pre; let band := J.filter (fun p => ¬p∣s.natAbs)
  let P := prescribedProbability R side (fun k => supportedValue J (R.intercept a side k.1 k.2))
  let g := scalarMass J c s Y S
  obtain ⟨oneG,_,α,mod⟩ := estimate R one hn comp target absent mark side u v ok
  obtain ⟨_,_,ready⟩ := first_polynomial_data R hn big comp target absent mark side u v ok
  change ScalarReady n pre c s (exactMean n ell a side) (oneWidth n ell a) at ready
  change commonDivisor c s=1 at oneG
  have win := ready.window
  simp only [oneG,Nat.cast_one,mul_one] at win
  let F := (s.natAbs:ℝ)/s.natAbs.totient*(Y^(α-1)*eulerMass band α)*
    omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p => log p) (log (Fixed.B b)) 0
  change PositiveScalarModel n ell pre c s (exactMean n ell a side) (oneWidth n ell a) 1 C α at mod
  unfold PositiveScalarModel at mod
  simp only [oneG,Nat.div_one,Nat.cast_one,mul_one,neg_one_mul] at mod
  obtain ⟨ha,mean,fp,model⟩ := mod
  have positive : 0<F := fp
  have fit := omitted_card hn big comp target absent ready.prepos ready.prebound
    (Int.natAbs_pos.mpr ready.nonzero) ready.cap
  obtain ⟨fl,lam,rel⟩ := floor b two Y S α band s.natAbs win ha mean (Int.natAbs_pos.mpr ready.nonzero) fit
  change exp (-444*(Fixed.h b:ℝ)) ≤ F at fl
  have realEst := (Complex.abs_re_le_norm _).trans model
  simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re] at realEst
  change |2*π*g.re-F| ≤ C*F*exp (-z^2) at realEst
  have upper : C*F*exp (-z^2) ≤ F/2 := by
    linarith only [mul_le_mul_of_nonneg_right decay positive.le]
  have gbound := (abs_le.mp (realEst.trans upper)).1
  have gn : 0≤g.re := by
    by_contra! bad
    linarith only [gbound, mul_neg_of_pos_of_neg (show 0<2*π by positivity) bad,positive]
  change |P-g.re| ≤ 90*exp (-(Fixed.U b:ℝ))*g.re at prob
  have half := (abs_le.mp (prob.trans (mul_le_mul_of_nonneg_right normSmall gn))).1
  have floorP : F≤8*π*P := by linarith only [gbound,mul_le_mul_of_nonneg_left half (show 0≤4*π by positivity)]
  refine ⟨?_,α,ha,zero_lt_one.trans_le win.2.1,lam,rel.trans floorP⟩
  have raw : exp (-444*(Fixed.h b:ℝ))/(8*π) ≤ P := by
    apply (div_le_iff₀ (by positivity : 0<8*π)).mpr
    linarith only [fl,floorP]
  apply le_trans _ raw
  let h := (Fixed.h b:ℝ)
  have hpos : 1≤h := by change (1:ℝ)≤(↑(Fixed.h b):ℝ); exact_mod_cast Nat.mul_pos dp (Nat.succ_pos _)
  have Bp : (0:ℝ)<Fixed.B b := by dsimp [Fixed.B]; positivity
  have logBound : 500*h ≤ log (Fixed.B b) := by
    have eq : log (Fixed.B b) = 1000*h*log 2 := by simp only [h,Fixed.B,Fixed.beta,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
    rw [eq]; nlinarith only [mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9]) (zero_le_one.trans hpos)]
  have gain : 8*(8*π) ≤ exp (-444*h)*(Fixed.B b) := by
    have hg : (10004:ℝ) ≤ h := by
      change (10004:ℝ) ≤ (Fixed.h b:ℝ)
      exact_mod_cast (big.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos b.log2)) : 10004 ≤ Fixed.h b)
    rw [←exp_log Bp,←exp_add]
    linarith only [pi_lt_four,add_one_le_exp (-444*h+log (Fixed.B b)),logBound,hg]
  exact (div_le_div_iff₀ Bp (by positivity : 0<8*π)).mpr gain

theorem PrescribedRows.smooth_probability_margin (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side
    8/(Fixed.B b:ℝ) ≤ prescribedProbability R side
      (fun k => supportedValue (sieveBand n ell pre) (R.intercept a side k.1 k.2)) := by
  obtain ⟨b₀,floor⟩ := PrescribedRows.smooth_probability_saddle_floor line
  exact ⟨b₀,fun R h hn comp target absent mark side => (floor R h hn comp target absent mark side).1⟩

theorem PrescribedRows.smooth_probability_lower (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side
    1/(Fixed.B b:ℝ) ≤ prescribedProbability R side
      (fun k => supportedValue (sieveBand n ell pre) (R.intercept a side k.1 k.2)) := by
  obtain ⟨b₀,margin⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨b₀,?_⟩
  intro n ell a R b huge hn comp target absent mark side pre
  exact (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤8) (Nat.cast_nonneg _)).trans
    (margin R huge hn comp target absent mark side)

theorem coefficient_tail_lt_half_mark {b : ℕ} (big : 1000 ≤ b) :
    1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) < 1/(2*(Fixed.B b:ℝ)) := by
  let B : ℝ := Fixed.B b
  let t := (b:ℝ)
  have tr : 1000≤t := by dsimp only [t]; exact_mod_cast big
  have hl : Fixed.h b ≤ b := (Nat.mul_le_mul_right (Fixed.z b)
    (Nat.le_self_pow (by decide : 3≠0) (Fixed.d b))).trans (Fixed.degree_floor b).1
  have logBound : log B ≤ 1000*t := by
    have lg : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have heq : log B = 1000*(Fixed.h b:ℝ)*log 2 := by simp only [B,Fixed.B,Fixed.beta,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
    have hreal : (Fixed.h b:ℝ)≤t := by dsimp only [t]; exact_mod_cast hl
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_left lg (Nat.cast_nonneg (α:=ℝ) (Fixed.h b)),hreal]
  have four : (2:ℝ)<π := by linarith [pi_gt_three]
  have const : (2432:ℝ) ≤ exp 40000 := by linarith only [add_one_le_exp 40000]
  have Bp : 0<B := by dsimp only [B,Fixed.B]; exact_mod_cast (Nat.pow_pos (a:=2) (n:=Fixed.beta b) (by decide))
  have power : B^3 ≤ exp (3000*t) := by
    rw [←exp_log Bp,←exp_nat_mul]
    exact exp_le_exp.mpr (by push_cast; linarith)
  have cube : (1000:ℝ)^3 ≤ t^3 := pow_le_pow_left₀ (by norm_num) tr 3
  have t0 : 0≤t := by linarith
  have exponent : 40000+3000*t+ -π*(t^2)^2/2 < 0 := by
    nlinarith only [tr,mul_le_mul_of_nonneg_right cube t0,
      mul_le_mul_of_nonneg_right four.le (sq_nonneg (t^2))]
  apply (lt_div_iff₀ (by positivity : 0<2*B)).mpr
  change 1216*B^2*exp (-π*(t^2)^2/2)*(2*B) < 1
  rw [show 1216*B^2*exp (-π*(t^2)^2/2)*(2*B) = (2432*B^3)*exp (-π*(t^2)^2/2) by ring]
  refine (mul_le_mul_of_nonneg_right (mul_le_mul const power (by positivity) (exp_pos _).le) (exp_pos _).le).trans_lt ?_
  rw [←exp_add,←exp_add]
  exact exp_lt_one_iff.mpr exponent

end Cogentic.Construction
