import Cogentic.DividedMarkTilts
import Cogentic.OrdinaryBranchMasks

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- Averaging a density equal to one on two misses only changes its baseline
through the two rare hit classes. -/
private theorem two_hit_mean_error (x y A : ℝ) (hx : x∈Set.Icc (0:ℝ) 1)
    (hy : y∈Set.Icc (0:ℝ) 1) (F : Bool→Bool→ℝ) (base : F false false=1)
    (bound : ∀ i j, |F i j-1|≤A) :
    |(∑ i : Bool, ∑ j : Bool, residueBranchMass x i*residueBranchMass y j*F i j)-1| ≤ (x+y)*A := by
  have t (k l : ℝ) (kp : 0≤k) (lp : 0≤l) (i j : Bool) :
      |k*l*(F i j-1)|≤k*l*A := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg kp lp)]
    exact mul_le_mul_of_nonneg_left (bound i j) (mul_nonneg kp lp)
  have a := t x y hx.1 hy.1 true true
  have b := t x (1-y) hx.1 (sub_nonneg.mpr hy.2) true false
  have c := t (1-x) y (sub_nonneg.mpr hx.2) hy.1 false true
  have nn : 0≤A := (abs_nonneg _).trans (bound true true)
  simp only [Fintype.sum_bool,residueBranchMass,if_true,if_false,Bool.false_eq_true,base,mul_one]
  rw [show _-1=(x*y*(F true true-1)+x*(1-y)*(F true false-1))+(1-x)*y*(F false true-1) by ring]
  exact (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add a b)) c).trans
    (by nlinarith only [mul_nonneg (mul_nonneg hx.1 hy.1) nn]))

/-- The empty insertion is one on every raw target branch at a legitimate saddle. -/
theorem grid_empty_insertion :
    ∃ b₀ : ℕ, ∀ {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ α : ℝ, 199/200≤α →
    InMarkSaddleRange n (saddleMean (primeBand b) α) →
    ∀ p∈primeBand b, fullBandInsertion b 1 α=1 := by
  obtain ⟨_,_,b₁,atoms⟩ := grid_scale_insertions
  obtain ⟨b₂,grow⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n b large α aa ma p pm
  obtain ⟨one,two⟩ := max_le_iff.mp large
  let H := log (Fixed.B b:ℝ)
  let u := 90*(Fixed.d b:ℝ)
  let μ := shiftedMass (primeBand b) (primeProbability α) (fun q=>log q) H 0
  have dr : (10004:ℝ)≤Fixed.d b := by exact_mod_cast grow b two
  have up : 88<u := by dsimp only [u];linarith only [dr]
  have atom := (atoms one α α aa (by linarith only [aa]) ma ma p pm p pm).1
  have pos : μ≠0 := by
    intro z
    have gone : fullBandInsertion b p α=0 := by dsimp only [fullBandInsertion];rw [show shiftedMass _ _ _ _ 0=0 from z];simp
    change |fullBandInsertion b p α/_ - 1|≤88/u at atom
    rw [gone,zero_div,zero_sub,abs_neg,abs_one] at atom
    exact ((div_lt_one (lt_trans (by norm_num) up)).mpr up).not_ge atom
  simpa only [fullBandInsertion,Nat.cast_one,log_one,one_rpow,one_mul] using div_self pos

set_option maxHeartbeats 600000 in
/-- On either target branch, conditioning on up to two ordinary roots changes
the mesh mean of the common smooth denominator by an arbitrarily small
logarithmic-square error. The estimate holds at each raw mesh position. -/
theorem ordinary_branch_normalizer (K : ℝ) (hk : 1≤K) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ∀ (α : Bool→ℝ), (∀ side, α side∈Set.Icc (199/200:ℝ) 1) →
    (∀ side, InMarkSaddleRange n (saddleMean (primeBand b) (α side))) →
    ∀ p∈primeBand b, ∀ q∈primeBand b, ∀ R T : PrescribedRows n ell,
    let F := fun i j => fullBandInsertion b (R.pairBranchProduct p q i j) (α false) *
      fullBandInsertion b (T.pairBranchProduct p q i j) (α true)
    |(∑ i : Bool, ∑ j : Bool,
      residueBranchMass (p:ℝ)⁻¹ i*residueBranchMass (q:ℝ)⁻¹ j*F i j)-1| ≤ 20*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨b₁,save⟩ := fixed_band_power_savings K hk
  obtain ⟨b₂,control⟩ := fullBandInsertion_saddle_control
  obtain ⟨b₃,emptyInsertion⟩ := grid_empty_insertion
  refine ⟨max (max b₁ b₂) b₃,?_⟩
  intro n ell b large α aa centers p pm q qm R T F
  obtain ⟨left,right⟩ := max_le_iff.mp large
  let B : ℝ := Fixed.B b; let H := log B
  have B1 : 1<B := by
    dsimp only [B]
    exact_mod_cast (Nat.one_lt_pow (Nat.mul_ne_zero (by decide)
      (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have Bp : 0<B := zero_lt_one.trans B1
  have Hp : 0<H := log_pos B1
  have window (s : Bool) : 90*(Fixed.d b:ℝ) ≤ saddleMean (primeBand b) (α s)/H ∧
      saddleMean (primeBand b) (α s)/H≤110*(Fixed.d b:ℝ) := by
    have h := centers s
    exact ⟨(le_div_iff₀ Hp).mpr (by simpa only [mul_comm] using h.1),
      (div_le_iff₀ Hp).mpr (by simpa only [mul_comm] using h.2.1)⟩
  have empty (s : Bool) : fullBandInsertion b 1 (α s)=1 := emptyInsertion right (α s) (aa s).1 (centers s) p pm
  have half (k : ℕ) (km : k∈primeBand b) : (k:ℝ)⁻¹≤B^(-1/2:ℝ) := by
    have ⟨pr,_,low⟩ := mem_primeBand.mp km
    have root : B^(1/2:ℝ)≤(k:ℝ) := by
      rw [←sqrt_eq_rpow]
      exact (sqrt_le_iff).mpr ⟨Nat.cast_nonneg _,by dsimp only [B];exact_mod_cast low.le⟩
    rw [show (-1/2:ℝ)= -(1/2) by ring,rpow_neg Bp.le]
    exact inv_anti₀ (rpow_pos_of_pos Bp _) root
  have single (s : Bool) (Q : ℕ) (Qp : 0<Q) (cap : Q ≤ (Fixed.B b)^2) :
      |fullBandInsertion b Q (α s)|≤3*B^(1/100:ℝ) := by
    have Qone : (1:ℝ)≤Q := by exact_mod_cast Qp
    have hcap : (Q:ℝ)≤B^2 := by dsimp only [B];exact_mod_cast cap
    have lg : log (Q:ℝ) ≤ 2*H := (log_le_log (zero_lt_one.trans_le Qone) hcap).trans_eq (by dsimp only [H]; rw [log_pow]; norm_num)
    have h := (control b (max_le_iff.mp left).2 Q (α s) (α s) Qp lg (aa s).1 (aa s).1
      (window s).1 (window s).2 (window s).1 (window s).2).1
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc (Q:ℝ)^(1-α s) ≤ (Q:ℝ)^(1/200:ℝ) := rpow_le_rpow_of_exponent_le Qone (by linarith only [(aa s).1])
         _ ≤ (B^2)^(1/200:ℝ) := rpow_le_rpow (Nat.cast_nonneg _) hcap (by norm_num)
         _ = B^(1/100:ℝ) := by rw [←rpow_natCast_mul Bp.le]; norm_num
  have part (W : PrescribedRows n ell) i j : 0<W.pairBranchProduct p q i j ∧ W.pairBranchProduct p q i j≤(Fixed.B b)^2 := by
    obtain ⟨pp,pc,_⟩ := mem_primeBand.mp pm
    obtain ⟨qp,qc,_⟩ := mem_primeBand.mp qm
    have one : 1≤Fixed.B b := Nat.one_le_two_pow
    have x : 0<(if p∈W.primes ∧ i then p else 1) ∧ (if p∈W.primes ∧ i then p else 1)≤Fixed.B b := by split <;> simp_all [pp.pos]
    have y : 0<(if q∈W.primes ∧ j then q else 1) ∧ (if q∈W.primes ∧ j then q else 1)≤Fixed.B b := by split <;> simp_all [qp.pos]
    exact ⟨Nat.mul_pos x.1 y.1,(Nat.mul_le_mul x.2 y.2).trans_eq (sq _).symm⟩
  have size (i j : Bool) : |F i j|≤9*B^(1/50:ℝ) := by
    dsimp only [F];rw [abs_mul]
    have a := part R i j;have b' := part T i j
    apply (mul_le_mul (single false _ a.1 a.2) (single true _ b'.1 b'.2) (abs_nonneg _) (by positivity)).trans_eq
    rw [show (1/50:ℝ)=1/100+1/100 by norm_num,rpow_add Bp];ring
  have E : 1≤B^(1/50:ℝ) := one_le_rpow B1.le (by norm_num)
  have err (i j : Bool) : |F i j-1|≤10*B^(1/50:ℝ) := by
    have d := (abs_sub (F i j) 1).trans (add_le_add (size i j) (le_refl |(1:ℝ)|))
    rw [abs_one] at d;linarith only [d,E]
  have base : F false false=1 := by simp [F,PrescribedRows.pairBranchProduct,empty]
  have frac (k : ℕ) (km : k∈primeBand b) : (k:ℝ)⁻¹∈Set.Icc (0:ℝ) 1 :=
    ⟨by positivity,inv_le_one_of_one_le₀ (by exact_mod_cast (mem_primeBand.mp km).1.one_le)⟩
  apply (two_hit_mean_error _ _ _ (frac p pm) (frac q qm) F base err).trans
  have fr := add_le_add (half p pm) (half q qm)
  have estimate := mul_le_mul_of_nonneg_right fr (show 0≤10*B^(1/50:ℝ) by positivity)
  apply estimate.trans
  calc (B^(-1/2:ℝ)+B^(-1/2:ℝ))*(10*B^(1/50:ℝ)) = 20*B^(-12/25:ℝ) := by
         rw [show (-12/25:ℝ)=(-1/2)+1/50 by norm_num,rpow_add Bp];ring
       _ ≤ 20*B^(-17/200:ℝ) := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le B1.le (by norm_num)) (by norm_num)
       _ ≤ _ := mul_le_mul_of_nonneg_left (save b (max_le_iff.mp left).1) (by norm_num)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.ordinary_branch_normalizer
