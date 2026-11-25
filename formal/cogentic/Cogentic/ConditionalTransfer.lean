import Cogentic.CleanWindows
import Cogentic.GaussianMeans
import Cogentic.SaddleNormalization

namespace Cogentic.Construction
open Real Cogentic.Window

private theorem log_distance {a b L W : ℝ} (lp : 0<L) (al : L≤a) (bl : L≤b)
    (dev : |a-b| ≤ W) : |log a-log b| ≤ W/L := by
  have wp : 0≤W := (abs_nonneg _).trans dev
  have up (a b : ℝ) (ap : 0<a) (bp : L≤b) (h : a-b≤W) :
      log a-log b ≤ W/L := by
    have bpos := lp.trans_le bp
    rw [←log_div ap.ne' bpos.ne']
    calc _ ≤ a/b-1 := log_le_sub_one_of_pos (div_pos ap bpos)
         _ = (a-b)/b := by field_simp
         _ ≤ W/b := div_le_div_of_nonneg_right h bpos.le
         _ ≤ _ := div_le_div_of_nonneg_left wp lp bp
  have h := up a b (lp.trans_le al) bl (abs_le.mp dev).2
  have t := up b a (lp.trans_le bl) al (by linarith [(abs_le.mp dev).1])
  exact abs_le.mpr ⟨by linarith only [t],h⟩

set_option maxRecDepth 3500 in
/-- On the admitted first-coordinate Gaussian bulk, dividing both
    second-coordinate centers by any positive common divisor preserves an
    exponentially small actual logarithmic drift. -/
theorem conditional_log_drift {n ell a a' : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a≤Fixed.A (n.log2+1)) (cap' : a'≤Fixed.A (n.log2+1))
    (grid' : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a')
    (side : Bool) (observed D : ℝ) (dp : 0<D)
    (bulk : |observed-lineCenter n a| ≤ ((n.log2+1:ℕ):ℝ)^3*projectionScale n a) :
    let x := (dyadicUnit (n.log2+1):ℝ)
    let y := (exactMean n ell a' side:ℝ)
    let z := conditionalMean n ell a a' side observed
    0<y ∧ 0<z ∧ |log (z/D)-log (y/D)| ≤ 2/x^95 := by
  intro x y z
  let b := n.log2+1
  let X := (amplitude n:ℝ)
  let W := (referenceWidth n:ℝ)
  have ⟨xx,bx,k,Bx,Ax,_,_⟩ := dyadic_data (b:=b) (Nat.succ_pos _)
  have x2 : (2:ℝ)≤x := by dsimp [x]; exact_mod_cast xx
  have xp : 0<x := by linarith
  have bx' : (b:ℝ)≤x := by dsimp [x]; exact_mod_cast bx
  have w0 : 0≤W := Nat.cast_nonneg _
  have base := (centered_envelope hn big target cap' grid' side y (by change |y-y|≤_; rw [sub_self,abs_zero]; positivity))
  have move := conditional_center_error hn big target cap cap' side observed bulk
  change |z-y| ≤ 4*(b:ℝ)^3*W at move
  have next := centered_envelope hn big target cap' grid' side z move
  have one := one_point_window hn big target cap' grid' side 1
    (show 1≤(1:ℝ) ∧ (1:ℝ)≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 by
      have A : 1≤(Fixed.A b:ℝ) := by rw [Ax,Nat.cast_pow]; exact one_le_pow₀ (by change 1≤x; linarith)
      have B : 1≤(Fixed.B b:ℝ) := by rw [Bx,Nat.cast_pow]; exact one_le_pow₀ (by change 1≤x; linarith)
      exact ⟨le_rfl,one_le_mul_of_one_le_of_one_le A (one_le_pow₀ B)⟩)
  have yp : 0<y := zero_lt_one.trans_le (by simpa only [div_one] using one.2.1)
  change X/(2*x^4)≤y ∧ y≤2*X at base
  change X/(2*x^4)≤z ∧ z≤2*X at next
  have Xp : 0<X := by linarith only [base.2,yp]
  have Lp : 0<X/(2*x^4) := by positivity
  have zp := Lp.trans_le next.1
  rw [log_div zp.ne' dp.ne',log_div yp.ne' dp.ne',sub_sub_sub_cancel_right]
  refine ⟨yp,zp,(log_distance Lp next.1 base.1 move).trans ?_⟩
  have K : (Fixed.K₁ b:ℝ)=x^100 := by dsimp [x]; exact_mod_cast k
  have amp := (amplitude_compare hn big).1
  have ampR : 6*x^100*(b:ℝ)^2*W ≤ X := by rw [←K]; dsimp only [W,X,b]; exact_mod_cast amp
  rw [div_le_div_iff₀ Lp (by positivity),div_eq_mul_inv]
  apply (mul_le_mul_iff_right₀ (by positivity : 0<2*x^4)).mp
  rw [show (2*x^4)*(2*(X*(2*x^4)⁻¹))=2*X by field_simp]
  have xl := mul_le_mul_of_nonneg_right bx' (show 0≤(b:ℝ)^2*W*x^99 by positivity)
  have pos : 0 ≤ x^100*(b:ℝ)^2*W := mul_nonneg (mul_nonneg (pow_nonneg xp.le _) (sq_nonneg _)) w0
  nlinarith only [xl,ampR,pos]

end Cogentic.Construction

namespace Cogentic.Window
open Real

/-- The full Euler-scaled central saddle model, omitting D and using
    the exact fixed logarithmic reference center μ. -/
noncomputable def centralDensity (J D : Finset ℕ) (H u α Y : ℝ) : ℝ :=
    Y^(α-1)*eulerMass (J\D) α*
      omittedMass J D (primeProbability α) (fun t=>log t) H (H*u-log Y)

/-- At actual fixed band and degree, a small displacement of the
    positive argument costs at most fourteen times its logarithmic
    change, uniformly over polynomially many omitted primes. -/
theorem fixed_central_density_transfer (k : ℕ) :
    ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α Y Z : ℝ) (D : Finset ℕ),
    let H := log (Fixed.B b)
    let B := (Fixed.B b:ℝ)
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200≤α → α≤1 →
    saddleMean J α = H*u → log Y=H*u → 0<Y → 0<Z →
    |log Z-log Y| ≤ 1 → D.card ≤ b^k → D⊆J →
    0<centralDensity J D H u α Y ∧
      |centralDensity J D H u α Z / centralDensity J D H u α Y-1| ≤ 14*|log Z-log Y| := by
  obtain ⟨n₁,central⟩ := fixed_central_mass_lower k
  obtain ⟨n₂,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ n₂,?_⟩
  intro b huge u α Y Z D H B J lo hi ha ha1 mean logY yp zp close dc sub
  obtain ⟨one,two⟩ := max_le_iff.mp huge
  have hd := deg b two
  have db := Fixed.degree_le_bits b
  have dr : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast hd
  have HH := (fixed_band_log_bounds b (by omega) (by omega)).1
  change 1000*(Fixed.d b:ℝ) ≤ H at HH
  have hp : 0<H := by linarith only [dr,HH]
  have up : 0<u := by linarith only [lo,dr]
  have su : sqrt u ≤ (Fixed.d b:ℝ) := (sqrt_le_left (by positivity)).mpr (by
    nlinarith only [hi,mul_nonneg (show 0≤(Fixed.d b:ℝ)-110 by linarith only [dr]) (Nat.cast_nonneg (α:=ℝ) (Fixed.d b))])
  let m := omittedMass J D (primeProbability α) (fun p=>log p) H (H*u-log Y)
  have atom := central b one u α (H*u-log Y) D lo hi ha mean
    (by rw [logY,sub_self,abs_zero]; positivity) dc sub
  change 1/(2*H*sqrt u)≤ m at atom
  have mp : 0 < m := (by positivity : 0<1/(2*H*sqrt u)).trans_le atom
  have sqrtBound : sqrt u ≤ H := su.trans (by linarith only [HH,dr])
  have rescale : 1 ≤ (2*H*sqrt u)*m := by
    have t := (div_le_iff₀ (by positivity : 0<2*H*sqrt u)).mp atom
    rwa [mul_comm] at t
  have productBound := mul_le_mul_of_nonneg_right sqrtBound (mul_nonneg hp.le mp.le)
  have scale : 1/2 ≤ H^2*m := by nlinarith only [rescale,productBound]
  have cost : 2+6/(H^2*m) ≤ 14 := by
    have e : 6/(H^2*m) ≤ 12 := (div_le_iff₀ (by positivity)).mpr (by linarith only [scale])
    linarith only [e]
  have r0 (t : ℕ) (_ : t∈J) : 0≤primeProbability α t := by unfold primeProbability; positivity
  have r1 (t : ℕ) (_ : t∈J) : primeProbability α t ≤ 1 := by
    unfold primeProbability
    rw [div_le_one (by positivity)]; linarith
  have estimate := central_density_stability J D (primeProbability α) (fun t=>log t)
    H (H*u) (log Y) (log Z-log Y) α hp (abs_le.mpr ⟨by linarith,by linarith⟩) close r0 r1 mp
  let n := omittedMass J D (primeProbability α) (fun p=>log p) H (H*u-log Z)
  have sum : log Y+(log Z-log Y)=log Z := by ring
  dsimp only at estimate
  rw [sum,mul_comm (α-1) (log Z),←rpow_def_of_pos zp,mul_comm (α-1) (log Y),←rpow_def_of_pos yp] at estimate
  have fp : 0<Y^(α-1)*eulerMass (J\D) α := mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)
  refine ⟨mul_pos fp mp,?_⟩
  have id : centralDensity J D H u α Z/centralDensity J D H u α Y =
      (Z^(α-1)*n)/(Y^(α-1)*m) := by
    unfold centralDensity
    change Z^(α-1)*eulerMass (J\D) α*n/(Y^(α-1)*eulerMass (J\D) α*m)=_
    rw [show Z^(α-1)*eulerMass (J\D) α*n=eulerMass (J\D) α*(Z^(α-1)*n) by ring,
        show Y^(α-1)*eulerMass (J\D) α*m=eulerMass (J\D) α*(Y^(α-1)*m) by ring,
        mul_div_mul_left _ _ (eulerMass_pos _ _).ne']
  rw [id]
  exact estimate.trans (mul_le_mul_of_nonneg_right cost (abs_nonneg _))

end Cogentic.Window

namespace Cogentic.Construction
open Real Cogentic.Window

/-- The central second scalar-density factor at the observed conditional
    mean agrees relatively with its nominal value, to any fixed
    exp(−K z²) precision, after every allowed common divisor. -/
theorem observed_density_transfer (k : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ {n ell a a' : ℕ}, let b := n.log2+1
    n₀ ≤ b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    a≤Fixed.A b → a'≤Fixed.A b →
    onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) a' →
    ∀ (side : Bool) (obs D α : ℝ) (omitted : Finset ℕ),
    let H := log (Fixed.B b)
    let J := primeBand b
    let Y := (exactMean n ell a' side:ℝ)/D
    let Z := conditionalMean n ell a a' side obs/D
    let u := log Y/H
    |obs-lineCenter n a| ≤ (b:ℝ)^3*projectionScale n a →
    (1≤D ∧ D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40) →
    199/200≤α → α≤1 → saddleMean J α=log Y → omitted.card≤b^k → omitted⊆J →
    0<centralDensity J omitted H u α Y ∧
    |centralDensity J omitted H u α Z / centralDensity J omitted H u α Y-1| ≤ exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨n₁,transfer⟩ := fixed_central_density_transfer k
  obtain ⟨n₂,small⟩ := fixed_band_power_savings K hK
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ (max n₂ n₃),?_⟩
  intro n ell a a' b huge hn target cap cap' grid side obs D α omitted H J Y Z u bulk div ha ha1 mean card sub
  obtain ⟨one,h⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp h
  have db := deg b three
  have big : 10004≤Fixed.d b := by omega
  have bpos : 0<b := Nat.succ_pos _
  have HH := (fixed_band_log_bounds b bpos (by omega)).1
  have dr : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast db
  change 1000*(Fixed.d b:ℝ) ≤ H at HH
  have hp : 0<H := by linarith only [dr,HH]
  have dn := zero_lt_one.trans_le div.1
  have ⟨yp,zp,drift⟩ := conditional_log_drift hn big target cap cap' grid side obs D dn bulk
  change |log Z-log Y| ≤ 2/(dyadicUnit b:ℝ)^95 at drift
  let x := (dyadicUnit b:ℝ)
  have ⟨xx,_,_,Bx,_,_,_⟩ := dyadic_data bpos
  have x2 : (2:ℝ)≤x := by dsimp [x]; exact_mod_cast xx
  have xp : 0<x := by linarith
  have pow10 : 28≤x^10 := (by norm_num : (28:ℝ)≤2^10).trans (pow_le_pow_left₀ (by norm_num) x2 10)
  have bb : (Fixed.B b:ℝ) = x^1000 := by dsimp [x]; exact_mod_cast Bx
  have tiny : (Fixed.B b:ℝ)^(-17/200:ℝ)=(x^85)⁻¹ := by
    rw [bb,←rpow_natCast,←rpow_mul xp.le]
    norm_num [rpow_neg xp.le]
  have bound : 14*(2/x^95) ≤ (Fixed.B b:ℝ)^(-17/200:ℝ) := by
    rw [tiny,←one_div,←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
    have mag := mul_le_mul_of_nonneg_right pow10 (pow_nonneg xp.le 85)
    rw [←pow_add] at mag
    norm_num at mag ⊢; exact mag
  have little : (2:ℝ)/x^95 ≤ 1 := (div_le_one (by positivity)).mpr
    (x2.trans (le_self_pow₀ (by linarith) (by decide)))
  have close : |log Z-log Y|≤1 := drift.trans little
  have win := one_point_window hn big target cap' grid side D div
  have logY : log Y=H*u := by dsimp only [u]; field_simp
  specialize transfer b one u α Y Z omitted
  simp only [Nat.floor_natCast] at transfer
  change _ → _ → _ → _ → saddleMean J α=H*u → _ → _ → _ → _ → _ → _ →
    0<centralDensity J omitted H u α Y ∧
      |centralDensity J omitted H u α Z/centralDensity J omitted H u α Y-1| ≤ 14*|log Z-log Y| at transfer
  obtain ⟨pos,step⟩ := transfer win.2.2.1 win.2.2.2.1 ha ha1 (mean.trans logY) logY
    (div_pos yp dn) (div_pos zp dn) close card sub
  exact ⟨pos,step.trans ((mul_le_mul_of_nonneg_left drift (by norm_num)).trans (bound.trans (small b two)))⟩

end Cogentic.Construction
