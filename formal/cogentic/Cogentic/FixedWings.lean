import Cogentic.SaddleEuler
import Cogentic.FixedSchedule

open Real Set MeasureTheory
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

/-- Control of the actual rounded dyadic base by its integer degree. -/
theorem binary_log_degree (b : ℕ) (hb : 0 < b) (hd : 16 ≤ Fixed.d b) :
    2^(Fixed.z b) ≤ (Fixed.d b)^8 := by
  let d := Fixed.d b
  let z := Fixed.z b
  have dn : 16 ≤ d := hd
  have zp : 0 < z := by dsimp [z,Fixed.z]; omega
  have bmin : 16 ≤ b := hd.trans (Fixed.degree_le_bits b)
  have z4 : 4 ≤ z := by
    have hh := (Nat.le_log2 hb.ne').mpr (show 2^4 ≤ b by simpa using bmin)
    dsimp [z,Fixed.z]
    omega
  have sqpow (n : ℕ) (h : 4 ≤ n) : n^2 ≤ 2^n := by
    induction n, h using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      rw [pow_succ 2]
      nlinarith [Nat.mul_le_mul_left n hn]
  have zz := sqpow z z4
  have twoz : 2^z ≤ 2*b := by
    dsimp only [z,Fixed.z]
    rw [pow_succ,mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.log2_self_le hb.ne')
  have bb : b ≤ 8*d^3*z := by
    obtain ⟨_,top⟩ := Fixed.degree_floor b
    change b < (d+1)^3*z at top
    calc b ≤ (d+1)^3*z := top.le
         _ ≤ (2*d)^3*z := by gcongr; omega
         _ = _ := by ring
  have double : 2*b ≤ 16*d^3*z := (Nat.mul_le_mul_left 2 bb).trans_eq (by ring)
  have zz' : z^2 ≤ 16*d^3*z := zz.trans (twoz.trans double)
  have zcap : z ≤ 16*d^3 := by
    apply Nat.le_of_mul_le_mul_right _ zp
    simpa [pow_two] using zz'
  have dp : d^8 = d^6*d^2 := by ring
  have big : 256 ≤ d^2 := by nlinarith
  have zlarge : 2^z ≤ d^8 := by
    calc 2^z ≤ 16*d^3*z := twoz.trans double
         _ ≤ 16*d^3*(16*d^3) := Nat.mul_le_mul_left _ zcap
         _ = 256*d^6 := by ring
         _ ≤ d^8 := by rw [dp,mul_comm 256]; exact Nat.mul_le_mul_left _ big
  exact zlarge

/-- Control of the actual rounded dyadic base by its integer degree. -/
theorem fixed_band_log_bounds (b : ℕ) (hb : 0 < b) (hd : 16 ≤ Fixed.d b) :
    1000*(Fixed.d b:ℝ) ≤ Real.log (Fixed.B b) ∧
      Real.log (Fixed.B b) ≤ 8000*(Fixed.d b:ℝ)*Real.log (Fixed.d b) := by
  let d := Fixed.d b
  let z := Fixed.z b
  have dn : 16 ≤ d := hd
  have zp : 0 < z := by dsimp [z,Fixed.z]; omega
  have bmin : 16 ≤ b := hd.trans (Fixed.degree_le_bits b)
  have z4 : 4 ≤ z := by
    have hh := (Nat.le_log2 hb.ne').mpr (show 2^4 ≤ b by simpa using bmin)
    dsimp [z,Fixed.z]
    omega
  have zlarge := binary_log_degree b hb hd
  have casted : (2:ℝ)^z ≤ (d:ℝ)^8 := by exact_mod_cast zlarge
  have lg := Real.log_le_log (by positivity) casted
  rw [Real.log_pow,Real.log_pow] at lg
  have half : (1/2:ℝ) ≤ Real.log 2 := by
    have t := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one] at t
    linarith
  have logB : Real.log (Fixed.B b) = 1000*(d:ℝ)*((z:ℝ)*Real.log 2) := by
    dsimp [Fixed.B,Fixed.beta,Fixed.h,d,z]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [logB]
  change _ ≤ _ ∧ _ ≤ 8000*(d:ℝ)*Real.log d
  constructor
  · have bigz : ∀ n : ℕ, 4 ≤ n → (4:ℝ) ≤ n := fun n h => by exact_mod_cast h
    have hg := mul_le_mul (bigz z z4) half (by norm_num) (Nat.cast_nonneg z)
    nlinarith [mul_nonneg (show 0 ≤ (1000:ℝ)*d by positivity)
      (show 0 ≤ (z:ℝ)*Real.log 2-1 by linarith)]
  · norm_num at lg
    nlinarith only [mul_le_mul_of_nonneg_left lg (show 0 ≤ (1000:ℝ)*d by positivity)]

/-- The shifted first vertical loses more than its entire length, while
    the first horizontal Euler exponent costs at most a quarter of u. -/
theorem fixed_first_contour_losses (b : ℕ) (hb : 0 < b) (hd : 50000 ≤ Fixed.d b)
    (u lam : ℝ) (ulo : 90*(Fixed.d b:ℝ) ≤ u) (uhi : u ≤ 110*(Fixed.d b:ℝ))
    (sharp : Real.exp lam ≤ 2*lam*(4*u+1))
    (logarithmic : lam ≤ 2*Real.log (16*u+4)) :
    let d := (Fixed.d b:ℝ)
    let H := Real.log (Fixed.B b)
    let shift := Real.log d/2
    H/200 ≤ u*shift ∧ 6*Real.exp (lam+shift)/H ≤ u/4 ∧
      lam+shift ≤ H/200 ∧ lam ≤ H/400 := by
  let d := (Fixed.d b:ℝ)
  let H := Real.log (Fixed.B b)
  let shift := Real.log d/2
  have dn : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have dpos : 0 < d := by linarith
  have dp : 1 ≤ d := by linarith
  have sp := Real.sqrt_pos.mpr dpos
  have sq := Real.sq_sqrt dpos.le
  have sqrt1 : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).mpr dp
  have sqrtle : Real.sqrt d ≤ d := by nlinarith [mul_nonneg sp.le (sub_nonneg.mpr sqrt1)]
  have lb := fixed_band_log_bounds b hb (by omega)
  change 1000*d ≤ H ∧ H ≤ 8000*d*Real.log d at lb
  have hp : 0 < H := by linarith [lb.1]
  have uPos : 1 ≤ u := by change 90*d ≤ u at ulo; linarith
  have logu : Real.log (16*u+4) ≤ Real.sqrt d := by
    apply (Real.log_le_iff_le_exp (by linarith)).mpr
    have t := Real.pow_div_factorial_le_exp (Real.sqrt d) (Real.sqrt_nonneg d) 4
    norm_num [Nat.factorial] at t
    have d4 : (Real.sqrt d)^4=d^2 := by rw [show (Real.sqrt d)^4=((Real.sqrt d)^2)^2 by ring,sq]
    rw [d4] at t
    change u ≤ 110*d at uhi
    nlinarith [mul_nonneg dpos.le (show 0 ≤ d-50000 by linarith)]
  have exs : Real.exp shift = Real.sqrt d := by
    dsimp [shift]
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos dpos]
    congr 1
    ring
  have hlog : 0 ≤ Real.log d := Real.log_nonneg dp
  have self : Real.log d ≤ Real.sqrt d := (Real.log_le_log dpos (by linarith : d ≤ 16*u+4)).trans logu
  have lsmall : lam ≤ 2*Real.sqrt d := logarithmic.trans (by linarith)
  change H/200 ≤ u*shift ∧ 6*Real.exp (lam+shift)/H ≤ u/4 ∧ lam+shift ≤ H/200 ∧ lam ≤ H/400
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [shift]
    nlinarith only [lb.2,mul_le_mul_of_nonneg_right ulo hlog,mul_nonneg dpos.le hlog]
  · rw [Real.exp_add,exs,div_le_iff₀ hp]
    have l1 := mul_le_mul_of_nonneg_right sharp sp.le
    have l2 := mul_le_mul_of_nonneg_right lsmall (mul_nonneg (by linarith : 0 ≤ 4*u+1) sp.le)
    have bound : 6 * (Real.exp lam*Real.sqrt d) ≤ 24*d*(4*u+1) := by
      nlinarith only [l1,l2,congrArg (fun x : ℝ => x*(4*u+1)) sq]
    nlinarith only [bound,mul_le_mul_of_nonneg_right lb.1 (show 0 ≤ u by linarith),
      mul_le_mul_of_nonneg_left uPos dpos.le,mul_nonneg dpos.le (show 0 ≤ u by linarith),dpos.le]
  · dsimp [shift]
    linarith only [lsmall,self,lb.1,sqrtle,dpos.le]
  · linarith only [lsmall,lb.1,sqrtle,dpos.le]

private theorem contour_cap_le (C B Y D l r α t H u v length L E : ℝ)
    (hy : 0 < Y) (hp : H = Real.log B) (saddle : Real.log Y=H*v)
    (ePos : 0 < E) (hE : 7*u/8 ≤ Real.log E) (leng : length ≤ Real.exp L)
    (trade : L+(r-α)*(H*v) ≤ 0) (peak : 6*B^(1-l)/(t*H) ≤ u/4)
    (err : Real.log (8*Real.exp 1+16) + C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) +
      D*B^(-199/400:ℝ)+(∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2 ≤ u/8) :
    length*contourCap C B Y D l r t ≤ Y^(α-1)*E*Real.exp (-u/2) := by
  let K := 8*Real.exp 1+16
  have kp : 0 < K := by dsimp [K]; positivity
  let loss := C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+D*B^(-199/400:ℝ)+(∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2
  let A := 6*B^(1-l)/(t*H)
  have cap : contourCap C B Y D l r t = Real.exp (Real.log K+(r-1)*(H*v)+A+loss) := by
    dsimp only [contourCap,A,loss]
    rw [Real.rpow_def_of_pos hy,saddle,← hp]
    rw [show Real.log K+(r-1)*(H*v)+6*B^(1-l)/(t*H)+
      (C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+D*B^(-199/400:ℝ)+(∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2)
      = Real.log K + (H*v)*(r-1) + (6*B^(1-l)/(t*H) + C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) +
        D*B^(-199/400:ℝ)+(∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2) by ring]
    simp only [Real.exp_add,Real.exp_log kp,K]
  have target : Y^(α-1)*E*Real.exp (-u/2) = Real.exp ((α-1)*(H*v)+Real.log E-u/2) := by
    rw [Real.rpow_def_of_pos hy,saddle,mul_comm (H*v),show (α-1)*(H*v)+Real.log E-u/2=
      ((α-1)*(H*v)+Real.log E)+(-u/2) by ring,Real.exp_add,Real.exp_add,Real.exp_log ePos]
  rw [cap,target]
  apply (mul_le_mul_of_nonneg_right leng (Real.exp_pos _).le).trans
  rw [← Real.exp_add,Real.exp_le_exp]
  change A ≤ u/4 at peak
  have er : Real.log K+loss ≤ u/8 := by dsimp only [K,loss]; linarith only [err]
  nlinarith only [trade,hE,peak,er]

/-- All five pieces of either high-frequency wing are exponentially small
    relative to the tilted Euler mass on the actual dyadic schedule. The
    evaluation center may differ from the common saddle center. -/
theorem fixed_rectangle_terms (b : ℕ) (hb : 0 < b) (hd : 50000 ≤ Fixed.d b)
    (C Y α u v E k : ℝ) (hy : 0 < Y) (ePos : 0 < E) (a1 : α ≤ 1)
    (ulo : 90*(Fixed.d b:ℝ) ≤ u) (uhi : u ≤ 110*(Fixed.d b:ℝ))
    (vlo : 80*(Fixed.d b:ℝ) ≤ v) :
    let d := (Fixed.d b:ℝ)
    let B := (Fixed.B b:ℝ)
    let H := Real.log B
    let lam := (1-α)*H
    let shift := Real.log d/2
    let γ := α-shift/H
    let β := (199/200:ℝ)
    let T₁ := B^(1/200:ℝ)
    let T := B^(1/5:ℝ)
    let cap := contourCap C B Y k
    Real.log Y=H*v → 7*u/8 ≤ Real.log E → Real.exp lam ≤ 2*lam*(4*u+1) →
    lam ≤ 2*Real.log (16*u+4) →
    Real.log (8*Real.exp 1+16) + C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) +
      k*B^(-199/400:ℝ)+(∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2 ≤ u/8 →
    β ≤ γ ∧ γ ≤ α ∧
      (T₁-1)*cap γ γ 1+(T-T₁)*cap β β T₁+(α-γ)*cap γ α 1+
        (γ-β)*cap β γ T₁+(α-β)*cap β α T ≤ 5*(Y^(α-1)*E)*Real.exp (-u/2) := by
  dsimp only
  let d := (Fixed.d b:ℝ)
  let B := (Fixed.B b:ℝ)
  let H := Real.log B
  let lam := (1-α)*H
  let shift := Real.log d/2
  let γ := α-shift/H
  let β := (199/200:ℝ)
  let T₁ := B^(1/200:ℝ)
  let T := B^(1/5:ℝ)
  let cap := contourCap C B Y k
  intro center hE sharp logarithmic small
  have dn : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  change 90*d ≤ u at ulo
  change 80*d ≤ v at vlo
  have vp : 80 ≤ v := by linarith
  have dn1 : 1 ≤ d := by linarith
  have dpos : 0 < d := by linarith
  have lb := fixed_band_log_bounds b hb (by omega)
  change 1000*d ≤ H ∧ H ≤ 8000*d*Real.log d at lb
  have hp : 0 < H := by linarith [lb.1]
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have first := fixed_first_contour_losses b hb hd u lam ulo uhi sharp logarithmic
  change H/200 ≤ u*shift ∧ 6*Real.exp (lam+shift)/H ≤ u/4 ∧ lam+shift ≤ H/200 ∧ lam ≤ H/400 at first
  have hshift : 0 ≤ shift := by dsimp [shift]; linarith [Real.log_nonneg dn1]
  have γa : γ ≤ α := sub_le_self _ (div_nonneg hshift hp.le)
  have bg : β ≤ γ := by
    change (199/200:ℝ) ≤ α-shift/H
    have h := first.2.2.1
    dsimp only [lam] at h
    apply (le_sub_iff_add_le).mpr
    rw [add_comm,← le_sub_iff_add_le,div_le_iff₀ hp]
    linarith only [h]
  have ba : 1/400 ≤ α-β := by
    apply le_of_mul_le_mul_left (a := H) _ hp
    have h := first.2.2.2
    dsimp only [lam,β] at h ⊢
    linarith only [h,mul_comm H α]
  have powE (s : ℝ) : B^s=Real.exp (H*s) := Real.rpow_def_of_pos bp _
  have w0 : 6*B^(1-γ)/(1*H) ≤ u/4 := by
    rw [one_mul,powE,show H*(1-γ)=lam+shift by dsimp only [γ,lam]; field_simp; ring]
    exact first.2.1
  have t1pos : 0 < T₁ := Real.rpow_pos_of_pos bp _
  have t12 : T₁ ≤ T := by
    dsimp only [T₁,T]
    rw [powE,powE,Real.exp_le_exp]
    linarith
  have six : 6/H ≤ u/4 := by
    rw [div_le_iff₀ hp]
    nlinarith [lb.1,mul_le_mul_of_nonneg_right lb.1 (by linarith : 0 ≤ u),
      mul_le_mul_of_nonneg_left (by linarith : 1 ≤ u) dpos.le]
  have w1 : 6*B^(1-β)/(T₁*H) ≤ u/4 := by
    change 6*B^(1-(199/200:ℝ))/(T₁*H) ≤ u/4
    rw [show 1-(199/200:ℝ)=1/200 by norm_num]
    change 6*T₁/(T₁*H) ≤ u/4
    rw [show 6*T₁/(T₁*H)=6/H by field_simp]
    exact six
  have w2 : 6*B^(1-β)/(T*H) ≤ u/4 :=
    (div_le_div_of_nonneg_left (by positivity) (mul_pos t1pos hp)
      (mul_le_mul_of_nonneg_right t12 hp.le)).trans w1
  have trade0 : H/200+(γ-α)*(H*v) ≤ 0 := by
    have hlog := Real.log_nonneg dn1
    rw [show (γ-α)*(H*v)= -shift*v by dsimp only [γ]; field_simp; ring]
    dsimp only [shift]
    nlinarith only [lb.2,mul_le_mul_of_nonneg_right vlo hlog]
  have trade1 : H/5+(β-α)*(H*v) ≤ 0 := by
    have t := mul_le_mul ba vp (by norm_num : 0 ≤ (80:ℝ)) (by linarith : 0 ≤ α-β)
    have z := mul_le_mul_of_nonneg_left t hp.le
    nlinarith only [z]
  have w (l r t len L : ℝ) (le : len ≤ Real.exp L) (loss : L+(r-α)*(H*v) ≤ 0)
      (pk : 6*B^(1-l)/(t*H) ≤ u/4) :
      len*cap l r t ≤ Y^(α-1)*E*Real.exp (-u/2) :=
    contour_cap_le C B Y k l r α t H u v len L E hy rfl center ePos hE le loss pk small
  have len₁ : T₁-1 ≤ Real.exp (H/200) := by dsimp [T₁]; rw [powE,show H*(1/200)=H/200 by ring]; linarith only
  have len₂ : T-T₁ ≤ Real.exp (H/5) := by dsimp only [T]; rw [powE,show H*(1/5)=H/5 by ring]; linarith only [t1pos]
  have len₃ : α-γ ≤ Real.exp 0 := by rw [Real.exp_zero]; change (199/200:ℝ) ≤ γ at bg; linarith
  have len₄ : γ-β ≤ Real.exp 0 := by rw [Real.exp_zero]; dsimp [β]; linarith
  have len₅ : α-β ≤ Real.exp 0 := by rw [Real.exp_zero]; dsimp [β]; linarith
  have c₁ := w γ γ 1 (T₁-1) (H/200) len₁ trade0 w0
  have c₂ := w β β T₁ (T-T₁) (H/5) len₂ trade1 w1
  have c₃ := w γ α 1 (α-γ) 0 len₃ (by simp) w0
  have c₄ := w β γ T₁ (γ-β) 0 len₄ (by
    rw [zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr γa) (mul_nonneg hp.le (by linarith))) w1
  have c₅ := w β α T (α-β) 0 len₅ (by simp) w2
  refine ⟨bg,γa,?_⟩
  change (T₁-1)*cap γ γ 1+(T-T₁)*cap β β T₁+(α-γ)*cap γ α 1+
    (γ-β)*cap β γ T₁+(α-β)*cap β α T ≤ _
  linarith only [c₁,c₂,c₃,c₄,c₅]

/-- Polynomially many omissions and the prime-measure approximation both
    have vanishing cost on the fixed binary schedule. -/
theorem fixed_prime_overhead (C : ℝ) (cpos : 0 ≤ C) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ D : Finset ℕ, D.card ≤ b^k →
      let B := (Fixed.B b:ℝ)
      C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+D.card*B^(-199/400:ℝ) ≤ 1/4 := by
  let target := max 50000 (max k ⌈10000*(C+1)⌉₊)
  obtain ⟨n,hn⟩ := Fixed.degree_grows target
  refine ⟨max n 1,fun b big D omitted => ?_⟩
  have deg := hn b ((le_max_left ..).trans big)
  have hb : 0 < b := (le_max_right ..).trans big
  have hd : 50000 ≤ Fixed.d b := (le_max_left ..).trans deg
  have hk : k ≤ Fixed.d b := (le_max_left ..).trans ((le_max_right ..).trans deg)
  have huge : 10000*(C+1) ≤ (Fixed.d b:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right ..).trans ((le_max_right ..).trans deg))
  let B := (Fixed.B b:ℝ)
  let H := Real.log B
  let d := (Fixed.d b:ℝ)
  let z := Fixed.z b
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have dn : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have low := (fixed_band_log_bounds b hb (by omega)).1
  change 1000*d ≤ H at low
  have hp : 0 < H := by linarith
  have logB : H = 1000*d*((z:ℝ)*Real.log 2) := by
    dsimp [H,B,d,z,Fixed.B,Fixed.beta,Fixed.h]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have castB : (b:ℝ) ≤ (2:ℝ)^z := by exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^z)
  have hk' : (k:ℝ) ≤ d := by dsimp [d]; exact_mod_cast hk
  have nn : 0 ≤ (z:ℝ)*Real.log 2 := by positivity
  have card : (D.card:ℝ) ≤ Real.exp (H/1000) := by
    have c := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) b) castB k
    have exp : ((2:ℝ)^z)^k = Real.exp ((k:ℝ)*((z:ℝ)*Real.log 2)) := by
      rw [Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (by norm_num : 0 < (2:ℝ))]
    rw [exp] at c
    exact (by exact_mod_cast omitted : (D.card:ℝ) ≤ (b:ℝ)^k).trans (c.trans (Real.exp_le_exp.mpr
      (by rw [logB]; nlinarith only [mul_le_mul_of_nonneg_right hk' nn])))
  have del : (D.card:ℝ)*B^(-199/400:ℝ) ≤ 1/8 := by
    rw [Real.rpow_def_of_pos bp]
    change (D.card:ℝ)*Real.exp (H*(-199/400:ℝ)) ≤ 1/8
    apply (mul_le_mul_of_nonneg_right card (Real.exp_pos _).le).trans
    rw [← Real.exp_add,show H/1000+H*(-199/400:ℝ) = -(993*H/2000) by ring,Real.exp_neg]
    have bnd : 8 ≤ Real.exp (993*H/2000) := by linarith [Real.add_one_le_exp (993*H/2000),low,dn]
    exact (inv_anti₀ (by norm_num : 0 < (8:ℝ)) bnd).trans_eq (by ring)
  have approx : C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) ≤ 1/8 := by
    have clog : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
    have pos : 0 ≤ 1+Real.log 3+H := by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
    have sq := pow_le_pow_left₀ pos (by linarith : 1+Real.log 3+H ≤ 2*H) 2
    have grow := Real.pow_div_factorial_le_exp (19*H/400) (by positivity) 3
    norm_num [Nat.factorial] at grow
    have shift := mul_le_mul_of_nonneg_right huge (sq_nonneg H)
    have scale := mul_le_mul_of_nonneg_right low (sq_nonneg H)
    have c2 := mul_le_mul_of_nonneg_left sq cpos
    rw [Real.log_mul (by norm_num) bp.ne',Real.rpow_def_of_pos bp]
    change C*(1+(Real.log 3+H))^2*Real.exp (H*(-19/400:ℝ)) ≤ 1/8
    rw [show H*(-19/400:ℝ) = -(19*H/400) by ring,Real.exp_neg,← div_eq_mul_inv,
      div_le_iff₀ (Real.exp_pos _)]
    change 10000*(C+1) ≤ d at huge
    change 10000*(C+1)*H^2 ≤ d*H^2 at shift
    nlinarith only [grow,shift,scale,c2,sq_nonneg H,mul_nonneg cpos (sq_nonneg H)]
  change C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)+D.card*B^(-199/400:ℝ) ≤ 1/4
  linarith only [approx,del]

/-- Uniform fixed-schedule rectangle estimate at a genuine saddle of the
    full prime band, for every polynomial omission budget and every
    displaced evaluation center in the working range. -/
theorem eventual_fixed_saddle_wings (line : DirichletLZerosOnLine) (Cw : ℝ) (cw : 0 ≤ Cw) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u v Y : ℝ) (D : Finset ℕ),
      90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 80*(Fixed.d b:ℝ) ≤ v →
      D.card ≤ b^k → 0 < Y →
      let B := (Fixed.B b:ℝ)
      let H := Real.log B
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J → Real.log Y=H*v →
      ∃ α ∈ Icc (199/200:ℝ) 1, saddleMean J α=H*u ∧ 2 ≤ (1-α)*H ∧
      let γ := α-(Real.log (Fixed.d b)/2)/H
      let β := (199/200:ℝ)
      let T₁ := B^(1/200:ℝ)
      let T := B^(1/5:ℝ)
      let cap := contourCap Cw B Y D.card
      β ≤ γ ∧ γ ≤ α ∧
        (T₁-1)*cap γ γ 1+(T-T₁)*cap β β T₁+(α-γ)*cap γ α 1+
          (γ-β)*cap β γ T₁+(α-β)*cap β α T ≤
            5*(Y^(α-1)*eulerMass (J\D) α)*Real.exp (-u/2) := by
  obtain ⟨Cn,cn,locate⟩ := prime_saddle_nonresonance line
  obtain ⟨Ce,ce,euler⟩ := fixed_saddle_euler_margin line
  obtain ⟨nw,hw⟩ := fixed_prime_overhead Cw cw k
  obtain ⟨nn,hn⟩ := fixed_prime_overhead Cn cn k
  obtain ⟨ne,he⟩ := fixed_prime_overhead Ce ce k
  let Z := (∑' n : ℕ, (n:ℝ)^(-3/2:ℝ))/2
  let K := Real.log (8*Real.exp 1+16)+Z+1
  obtain ⟨nd,hdeg⟩ := Fixed.degree_grows (max 50000 ⌈K⌉₊)
  refine ⟨max 1 (max nw (max nn (max ne nd))),fun b big u v Y D ulo uhi vlo dc yPos => ?_⟩
  dsimp only
  intro om center
  obtain ⟨hb,rest⟩ := max_le_iff.mp big
  obtain ⟨bw,rest⟩ := max_le_iff.mp rest
  obtain ⟨bn,rest⟩ := max_le_iff.mp rest
  obtain ⟨be,bd⟩ := max_le_iff.mp rest
  obtain ⟨hd,hK⟩ := max_le_iff.mp (hdeg b bd)
  let d := (Fixed.d b:ℝ)
  let B := (Fixed.B b:ℝ)
  let H := Real.log B
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  have dn : 50000 ≤ d := by dsimp [d]; exact_mod_cast hd
  have cost : K ≤ d := (Nat.le_ceil _).trans (by dsimp [d]; exact_mod_cast hK)
  change 90*d ≤ u at ulo
  change u ≤ 110*d at uhi
  have low := (fixed_band_log_bounds b hb (by omega)).1
  change 1000*d ≤ H at low
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have b16 : 16 ≤ B := by
    have le := Real.add_one_le_exp H
    rw [show 16 ≤ B ↔ 16 ≤ Real.exp H by dsimp only [H]; rw [Real.exp_log bp]]
    linarith
  have umax : u ≤ B^(1/400:ℝ)/32 := by
    rw [Real.rpow_def_of_pos bp]
    change u ≤ Real.exp (H*(1/400:ℝ))/32
    have g := Real.pow_div_factorial_le_exp (H*(1/400:ℝ)) (by linarith : 0 ≤ H*(1/400:ℝ)) 2
    norm_num [Nat.factorial] at g
    have sq := pow_le_pow_left₀ (by linarith : 0 ≤ 1000*d) low 2
    nlinarith only [g,sq,uhi,mul_nonneg (show 0 ≤ d by linarith) (show 0 ≤ d-50000 by linarith)]
  let e := fun C : ℝ => C*(1+Real.log (3*B))^2*B^(-19/400:ℝ)
  let loss := (D.card:ℝ)*B^(-199/400:ℝ)
  have nwSmall : e Cw+loss ≤ 1/4 := hw b bw D dc
  have eo : ∀ C : ℝ, 0 ≤ C → 0 ≤ e C := by intro C hp; dsimp [e]; positivity
  have dome : loss ≤ 1/4 := by linarith [eo Cw cw]
  have no : (∅ : Finset ℕ).card ≤ b^k := by simp
  have nl := hn b bn ∅ no
  have el := he b be ∅ no
  simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at nl el
  obtain ⟨α,range,sm,lam,decay⟩ := locate B u ∅ b16 (by simpa using nl) (by linarith) umax
    (Finset.empty_subset J)
  rw [Finset.sdiff_empty] at sm
  obtain ⟨sharp,logarithmic,strong⟩ := euler B α u D b16 range.1 range.2 (el.trans (by norm_num))
    om sm lam
  have mass : 7*u/8 ≤ Real.log (eulerMass (J\D) α) := by
    change u-loss ≤ Real.log (eulerMass (J\D) α) at strong
    linarith
  have budget : Real.log (8*Real.exp 1+16)+Cw*(1+Real.log (3*B))^2*B^(-19/400:ℝ) +
      D.card*B^(-199/400:ℝ)+Z ≤ u/8 := by
    change Real.log (8*Real.exp 1+16)+e Cw+loss+Z ≤ u/8
    dsimp only [K] at cost
    linarith
  exact ⟨α,range,sm,lam,fixed_rectangle_terms b hb hd Cw Y α u v (eulerMass (J\D) α) D.card yPos
    (eulerMass_pos ..) range.2 ulo uhi vlo center mass sharp logarithmic budget⟩

end

end Cogentic.Window
