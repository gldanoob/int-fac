import Cogentic.FixedPairCovariance
import Cogentic.RelativePrincipalMass

namespace Cogentic.Window
open Real Set

private theorem transfer_one_ratio {a b x y e : ℝ} (ap : 0<a) (bp : 0<b) (small : e≤1/2)
    (ea : |x/a-1| ≤ e) (eb : |y/b-1| ≤ e) (cap : |a/b| ≤ 3) :
    0<y ∧ |x/y-a/b| ≤ 12*e ∧ |x/y| ≤ 9 := by
  have A := abs_le.mp ea
  have B := abs_le.mp eb
  have bylow : 1/2 ≤ y/b := by linarith
  have db : 0<y/b := by linarith
  have yp : 0<y := (div_pos_iff_of_pos_right bp).mp db
  have sep : |x/a-y/b| ≤ 2*e :=
    (abs_sub_le (x/a) 1 (y/b)).trans (by rw [abs_sub_comm 1]; linarith)
  have hq : |(x/a)/(y/b)-1| ≤ 4*e := by
    rw [show (x/a)/(y/b)-1=(x/a-y/b)/(y/b) by field_simp,abs_div,abs_of_pos db]
    apply (div_le_iff₀ db).mpr
    linarith only [sep, mul_le_mul_of_nonneg_left bylow (show 0≤4*e by linarith [abs_nonneg (y/b-1)])]
  have clos : |x/y-a/b| ≤ 12*e := by
    rw [show x/y-a/b=(a/b)*((x/a)/(y/b)-1) by field_simp,abs_mul]
    exact (mul_le_mul cap hq (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have tri := abs_sub_le (x/y) (a/b) 0
  simp only [sub_zero] at tri
  exact ⟨yp,clos,by linarith⟩

private theorem transfer_four_ratios (f g : ℝ → ℝ) (h j c e E : ℝ)
    (small : e ≤ 1/2) (eb : 0≤e) (curv : |c| ≤ 2)
    (pos : ∀ x ∈ ({0,h,j,h+j}:Finset ℝ), 0 < f x)
    (near : ∀ x ∈ ({0,h,j,h+j}:Finset ℝ), |g x/f x-1| ≤ e)
    (cap : ∀ x ∈ ({h,j,h+j}:Finset ℝ), |f x/f 0| ≤ 3)
    (pair : |f (h+j)/f 0-(f h/f 0)*(f j/f 0)*c| ≤ E) :
    0<g 0 ∧ |g h/g 0-f h/f 0| ≤ 12*e ∧ |g j/g 0-f j/f 0| ≤ 12*e ∧
    |g (h+j)/g 0-(g h/g 0)*(g j/g 0)*c| ≤ E+300*e := by
  classical
  have z : (0:ℝ)∈({0,h,j,h+j}:Finset ℝ) := by simp
  have single (x : ℝ) (hx : x∈({h,j,h+j}:Finset ℝ)) := transfer_one_ratio
    (pos x (Finset.mem_insert_of_mem hx)) (pos 0 z) small
    (near x (Finset.mem_insert_of_mem hx)) (near 0 z) (cap x hx)
  obtain ⟨gp,dh,gh⟩ := single h (by simp)
  obtain ⟨_,dj,_⟩ := single j (by simp)
  obtain ⟨_,ds,_⟩ := single (h+j) (by simp)
  have hj : |f j/f 0| ≤ 3 := cap j (by simp)
  let A := g h/g 0
  let B := g j/g 0
  let a := f h/f 0
  let b := f j/f 0
  have diff : |a*b-A*B| ≤ 144*e := by
    rw [show a*b-A*B= -(A-a)*b-A*(B-b) by ring]
    apply (abs_sub_le _ 0 _).trans
    rw [sub_zero,zero_sub,abs_neg,abs_mul,abs_neg,abs_mul]
    exact (add_le_add (mul_le_mul dh hj (abs_nonneg _) (by positivity))
      (mul_le_mul gh dj (abs_nonneg _) (by norm_num))).trans_eq (by ring)
  have d := (mul_le_mul diff curv (abs_nonneg _) (show 0 ≤ 144*e by positivity))
  rw [←abs_mul] at d
  refine ⟨gp,dh,dj,?_⟩
  calc _ ≤ |g (h+j)/g 0-f (h+j)/f 0| + |f (h+j)/f 0-A*B*c| := abs_sub_le ..
       _ ≤ |g (h+j)/g 0-f (h+j)/f 0| + (|f (h+j)/f 0-a*b*c|+|a*b*c-A*B*c|) :=
           add_le_add_right (abs_sub_le ..) _
       _ ≤ _ := by rw [←sub_mul]; linarith only [ds,pair,d]

private theorem exponential_to_covariance (b : ℕ) {C u : ℝ} (up : 0 < u)
    (c : C ≤ u) (ui : u ≤ 110*(Fixed.d b:ℝ)) :
    C*exp (-400*(Fixed.z b:ℝ)^2) ≤ 1/u^2 := by
  let z := (Fixed.z b:ℝ)
  have z1 : 1 ≤ z := by dsimp [z,Fixed.z]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le b.log2))
  have bz : (b:ℝ) ≤ exp z := by
    have n : (b:ℝ) ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^(Fixed.z b))
    have t := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
      (by linarith [exp_one_gt_d9] : (2:ℝ) ≤ exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at t
    exact n.trans t
  have dez : (Fixed.d b:ℝ) ≤ exp z := (show (Fixed.d b:ℝ) ≤ b by exact_mod_cast Fixed.degree_le_bits b).trans bz
  have cb : 110 ≤ exp (110*z) := by linarith [add_one_le_exp (110*z)]
  have uz : u ≤ exp (111*z) := ui.trans ((mul_le_mul cb dez (by positivity) (exp_pos _).le).trans_eq (by rw [←exp_add]; congr 1; ring))
  have cube := pow_le_pow_left₀ up.le uz 3
  rw [←exp_nat_mul] at cube
  have growth : u^3 ≤ exp (400*z^2) := cube.trans (exp_le_exp.mpr (by
    norm_num
    nlinarith only [mul_nonneg (sub_nonneg.mpr z1) (by linarith : 0≤z),z1]))
  rw [le_div_iff₀ (by positivity)]
  have h := mul_le_mul_of_nonneg_right growth (exp_pos (-(400*z^2))).le
  have finish : exp (400*z^2)*exp (-(400*z^2))=1 := by rw [←exp_add]; simp
  rw [finish] at h
  have h' := mul_le_mul_of_nonneg_right c (sq_nonneg u)
  change C*exp (-400*z^2)*u^2 ≤ 1
  calc _ ≤ u^3*exp (-(400*z^2)) := by
           rw [show -400*z^2= -(400*z^2) by ring]
           nlinarith only [mul_le_mul_of_nonneg_right h' (exp_pos (-(400*z^2))).le]
       _ ≤ _ := h

/-- Normalized complete smooth Gaussian after a logarithmic shift, using
    one real Euler tilt throughout the four insertion estimates. -/
noncomputable def shiftedGaussianAtom (J D : Finset ℕ) (Y S α a : ℝ) : ℝ :=
    2*π*gaussianMass (J\D) (Y/exp a) (S/exp a) /
      ((Y/exp a)^(α-1)*eulerMass (J\D) α)

/-- The actual complete squarefree Gaussian has the Bernoulli curvature
    correction for two insertions at the fixed degree schedule. -/
theorem fixed_full_insertions (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α Y S h j : ℝ) (D : ℝ → Finset ℕ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    let g := fun a : ℝ => shiftedGaussianAtom J (D a) Y S α a
    let V := saddleVariance J (primeProbability α) (fun p=>log p)
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    saddleMean J α = H*u → log Y = H*u → 0 < Y → 0 < S →
    B^(17/200:ℝ) ≤ Y/S → Y/S ≤ B^(17/100:ℝ) → |h| ≤ H → |j| ≤ H →
    (∀ a : ℝ, |a| ≤ 2*H → (D a).card ≤ b^k ∧ D a ⊆ J) →
    0 < g 0 ∧ |g h/g 0-1| ≤ 48/u ∧ |g j/g 0-1| ≤ 48/u ∧
    |g (h+j)/g 0-(g h/g 0)*(g j/g 0)*(1-h*j/V)| ≤ C/u^2 := by
  obtain ⟨C,cp,n₁,central⟩ := fixed_central_insertions k
  obtain ⟨A,ap,n₂,full⟩ := fixed_relative_principal_mass line k 400 (by norm_num)
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows (max 50000 ⌈A⌉₊)
  obtain ⟨n₄,dele⟩ := fixed_prime_deletions k
  refine ⟨C+300,by positivity,max (max n₁ n₂) (max n₃ n₄),?_⟩
  intro b huge u α Y S h j D B H J g V lo hi ha mean logY yp sp rlo rhi hh hj ds
  obtain ⟨g12,g34⟩ := max_le_iff.mp huge
  obtain ⟨one,two⟩ := max_le_iff.mp g12
  obtain ⟨three,four⟩ := max_le_iff.mp g34
  have db := deg b three
  have amp : A ≤ (Fixed.d b:ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast (le_max_right ..).trans db)
  have dr : (50000:ℝ) ≤ Fixed.d b := by exact_mod_cast (le_max_left ..).trans db
  obtain ⟨hp,large,_,_,_,rb,_⟩ := dele b four u α lo hi ha
  change 0<H at hp
  have up : 0<u := by linarith
  have u4 : 4≤u := by linarith only [lo,dr]
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have B1 : 1<B := (one_lt_exp_iff.mpr hp).trans_eq (exp_log bp)
  let M := fun a : ℝ => omittedMass J (D a) (primeProbability α) (fun p=>log p) H a
  have bound (x : ℝ) (hx : |x| ≤ 2*H) : 0<M x ∧ |g x/M x-1| ≤ 1/u^2 := by
    have xlog : log (Y/exp x)=H*u-x := by rw [log_div yp.ne' (exp_pos x).ne',logY,log_exp]
    have same : (Y/exp x)/(S/exp x)=Y/S := by field_simp
    have lower : H*(80*(Fixed.d b:ℝ)) ≤ log (Y/exp x) := by
      rw [xlog]
      linarith only [(abs_le.mp hx).2, mul_le_mul_of_nonneg_left
        (show 80*(Fixed.d b:ℝ)+2 ≤ u by linarith only [lo,dr]) hp.le]
    have off : H*u-log (Y/exp x)=x := by rw [xlog]; ring
    obtain ⟨β,hβ,mu,good⟩ := full b two u (Y/exp x) (S/exp x) (D x) lo hi lower
      (show |H*u-log (Y/exp x)| ≤ 2*H by rw [off]; exact hx)
      (by positivity) (by positivity) (same ▸ rlo) (same ▸ rhi) (ds x hx).1 (ds x hx).2
    have eq := band_saddle_unique B1 (by linarith : 0≤α) (by linarith [hβ.1] : 0≤β)
      (mean ▸ mul_pos hp up) (mean.trans mu.symm)
    subst β
    dsimp only at good
    rw [off] at good
    have mpos : 0<M x := good.1
    have val : g x/M x=(2*π*gaussianMass (J\D x) (Y/exp x) (S/exp x))/
        (((Y/exp x)^(α-1)*eulerMass (J\D x) α)*M x) := by dsimp [g,shiftedGaussianAtom]; ring
    rw [val]
    exact ⟨mpos,good.2.trans (exponential_to_covariance b up (by linarith only [amp,dr,lo]) hi)⟩
  have fullCentral := central b one u α h j D lo hi ha mean hh hj (fun a hx=>(ds a hx).1)
  have centralCap (x : ℝ) (hx : |x| ≤ 2*H) : |M x/M 0-1| ≤ 36/u ∧ |M x/M 0| ≤ 3 := fullCentral.2.1 x hx
  have pset : ∀ x∈({0,h,j,h+j}:Finset ℝ), |x| ≤ 2*H := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · rw [abs_zero]; positivity
    · linarith
    · linarith
    · exact (abs_add_le ..).trans (by linarith)
  have vg := (prime_saddle_variance_bounds J α H (by linarith) hp.le
    (fun p hx => (Finset.mem_filter.mp hx).2.one_le) (fun p hx => (rb p hx).2)).1
  rw [mean] at vg
  change H*(H*u)/4≤V at vg
  have vp : 0<V := (by positivity : 0<H*(H*u)/4).trans_le vg
  have hv : |h*j/V| ≤ 1 := by
    rw [abs_div,abs_mul,abs_of_pos vp,div_le_one vp]
    exact (mul_le_mul hh hj (abs_nonneg _) hp.le).trans (by
      nlinarith only [vg,mul_le_mul_of_nonneg_left u4 (sq_nonneg H)])
  have curve : |1-h*j/V| ≤ 2 := abs_le.mpr ⟨by linarith [(abs_le.mp hv).2],by linarith [(abs_le.mp hv).1]⟩
  have short : 1/u^2≤1/2 := div_le_div_of_nonneg_left zero_le_one (by norm_num)
    (by nlinarith only [large,mul_le_mul_of_nonneg_right large up.le])
  obtain ⟨gp,dh,dj,dx⟩ := transfer_four_ratios M g h j (1-h*j/V) (1/u^2) (C/u^2)
    short (by positivity) curve (fun x hx => (bound x (pset x hx)).1)
    (fun x hx => (bound x (pset x hx)).2)
    (fun x hx=> (centralCap x (pset x (Finset.mem_insert_of_mem hx))).2) fullCentral.2.2
  have onepow : 1/u^2≤1/u := div_le_div_of_nonneg_left zero_le_one up
    (by nlinarith only [mul_le_mul_of_nonneg_right (by linarith : 1≤u) up.le])
  have single (x : ℝ) (hx : |x| ≤ H) (e : |g x/g 0 - M x/M 0| ≤ 12*(1/u^2)) :
      |g x/g 0-1| ≤ 48/u := by
    apply (abs_sub_le _ (M x/M 0) _).trans
    exact (add_le_add (e.trans (mul_le_mul_of_nonneg_left onepow (by norm_num))) (centralCap x (by linarith)).1).trans_eq (by ring)
  exact ⟨gp,single h hh dh,single j hj dj,dx.trans_eq (by ring)⟩

end Cogentic.Window
