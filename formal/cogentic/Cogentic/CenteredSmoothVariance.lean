import Cogentic.PairVarianceTransfer
import Cogentic.CellPairMoment

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

private theorem smooth_score_identity {n ell : ℕ} (R T : PrescribedRows n ell) (X : Finset ℕ)
    (w : ℕ→ℝ) (pos : ∀ a∈X,0<smoothMarkProbability R T a) :
    twoFieldSecond R T X (fun a=>w a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true) =
      ∑ a∈X, ∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y+1) := by
  unfold twoFieldSecond
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro y hy
  let p := smoothMarkProbability R T
  let j := prescribedProbability R false (fun k => smoothMarkEvent R false a k ∧ smoothMarkEvent R false y k)*
    prescribedProbability T true (fun k=>smoothMarkEvent T true a k ∧ smoothMarkEvent T true y k)
  change (w a/p a*(w y/p y))*j=w a*w y*((j-p a*p y)/(p a*p y)+1)
  field_simp [show p a≠0 from (pos a ha).ne',show p y≠0 from (pos y hy).ne']; ring

set_option maxHeartbeats 1100000 in
/-- For a bounded-variation weight centered on its integer cell, the
expected squared smooth-mark score is small on the actual joint
coefficient distribution, uniformly over the ordinary root prescriptions. -/
theorem centered_smooth_score_second (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (w : ℕ→ℝ) (D V : ℝ), let X := constructorCellMarks n ell cell
    let L := firstCellMark b cell; let M := cellMarkCount b; let B : ℝ := Fixed.B b
    0≤D → 0≤V → (∀ a∈X,|w a|≤D) → (∑ j∈range M,w (L+j))=0 →
    |w (L+(M-1))|+(∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|)≤V →
    let e := exp (-K*(Fixed.z b:ℝ)^2)
    let f := fun a => w a/smoothMarkProbability R T a
    (∑' k : R.CoeffPoint false × T.CoeffPoint true,
      twoFieldWeight R T k*(twoFieldScore X f (smoothMarkEvent R false) (smoothMarkEvent T true) k.1.val k.2.val)^2) ≤
      D^2*C*e*M^2 + (V*((1+2*exp 6)*M)*e)^2*exp (8/(Fixed.d b:ℝ))+
        (D*((M:ℝ)/B+1)*(D*M))*exp (48*(Fixed.z b:ℝ)) := by
  obtain ⟨C,cp,b₁,pair⟩ := cell_pair_covariance_approximation line K hK
  obtain ⟨n₁,centered⟩ := centered_cell_pair_moment line K hK
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨C,cp,max n₁ (max 2 (2^(max b₁ b₂))),?_⟩
  intro n large ell target comp absent R T b cell w D V X L M B dp vp bound zero variation e f
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,limit⟩ := max_le_iff.mp more
  have huge : max b₁ b₂≤b := ((Nat.le_log2 (by omega : n≠0)).mpr limit).trans (Nat.le_succ _)
  let P := pairCorrectionPrimes b; let g := fun x y=>pairGamma P (Fixed.rootBase n) x y
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    have mark := (mem_filter.mp ha).2
    have lb : 0<8/(Fixed.B b:ℝ) := by dsimp [Fixed.B]; positivity
    have each (S : PrescribedRows n ell) (s : Bool) :
        0<prescribedProbability S s (smoothMarkEvent S s a) := by
      have raw := lb.trans_le (floor S (max_le_iff.mp huge).2 hn comp target absent mark s)
      exact raw.trans_eq (probability_congr S s _ (smoothMarkEvent S s a) rfl)
    exact mul_pos (each R false) (each T true)
  have one : (1:ℕ)≤(Fixed.B b)^3 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
  have pair' := pair R T (max_le_iff.mp huge).1 hn comp target absent cell cell 1 1 0 0
    squarefree_one squarefree_one one one
  have err := pair' w w D D dp dp (fun a ha=>bound a (mem_filter.mp ha).1) (fun a ha=>bound a (mem_filter.mp ha).1)
  simp only [Nat.modEq_one,filter_true,Nat.cast_one,one_mul] at err
  change |∑ a∈X, ∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y-(g a y^2-1))|/(M:ℝ)^2 ≤ D*D*(C*e) at err
  have mp : 0<(M:ℝ)^2 := by dsimp [M,cellMarkCount]; positivity
  have raw := (div_le_iff₀ mp).mp err
  have primes (p : ℕ) (hp : p∈P) : p.Prime ∧ Fixed.d b<p ∧ p≤Fixed.B b := by
    obtain ⟨prime,lo,hi⟩ := mem_pairCorrectionPrimes.mp hp
    refine ⟨prime,lo,hi.trans ?_⟩
    apply Nat.pow_le_pow_right (by decide)
    change 200*Fixed.h b≤1000*Fixed.h b
    omega
  have model := centered n old ell target comp absent cell 0 0 0 0 P w D V primes dp vp bound zero variation
  have eq : (∑ a∈X,∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y+1)) =
      (∑ a∈X,∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y-(g a y^2-1)))+
      ∑ a∈X,∑ y∈X,w a*w y*g a y^2 := by
    rw [←sum_add_distrib]; apply sum_congr rfl; intro a ha
    rw [←sum_add_distrib]; apply sum_congr rfl; intro y hy; ring
  rw [(twoField_score_second R T target X f (smoothMarkEvent R false) (smoothMarkEvent T true)).tsum_eq,smooth_score_identity R T X w pos,eq]
  change (∑ a∈X,∑ y∈X,w a*w y*g a y^2) ≤ _ at model
  linarith only [(le_abs_self _).trans raw,model]

/-- After division by the squared cell length, the centered score's true
second moment decays faster than any prescribed logarithmic-square rate,
with the size and variation of the weights explicit. -/
theorem centered_smooth_score_decay (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (w : ℕ→ℝ) (D V : ℝ), let X := constructorCellMarks n ell cell
    let L := firstCellMark b cell; let M := cellMarkCount b
    0≤D → 0≤V → (∀ a∈X,|w a|≤D) → (∑ j∈range M,w (L+j))=0 →
    |w (L+(M-1))|+(∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|)≤V →
    let f := fun a=>w a/smoothMarkProbability R T a
    (∑' k : R.CoeffPoint false × T.CoeffPoint true,
      twoFieldWeight R T k*(twoFieldScore X f (smoothMarkEvent R false) (smoothMarkEvent T true) k.1.val k.2.val)^2)/(M:ℝ)^2 ≤
      C*(D^2+V^2)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,n₁,score⟩ := centered_smooth_score_second line K hK
  obtain ⟨b₂,save⟩ := fixed_band_power_savings (K+48) (by linarith)
  let H := (1+2*exp 6)^2*exp 8
  have hp : 0≤H := by dsimp only [H]; positivity
  refine ⟨C+2+H,by positivity,max n₁ (2^b₂),?_⟩
  intro n large ell target comp absent R T b cell w D V X L M dp vp bound zero variation f
  obtain ⟨old,limit⟩ := max_le_iff.mp large
  have hn : n≠0 := (Nat.pow_pos (by decide) : 0<2^b₂).trans_le limit |>.ne'
  have huge : b₂≤b := ((Nat.le_log2 hn).mpr limit).trans (Nat.le_succ _)
  let z : ℝ := Fixed.z b; let B : ℝ := Fixed.B b; let e := exp (-K*z^2)
  have ep : 0≤e := (exp_pos _).le
  have eo : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have zp : 1≤z := by dsimp only [z,Fixed.z]; exact_mod_cast (Nat.le_add_left 1 b.log2)
  have d : (1:ℝ)≤Fixed.d b := by exact_mod_cast Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
  have e8 : exp (8/(Fixed.d b:ℝ))≤exp 8 := exp_le_exp.mpr ((div_le_iff₀ (zero_lt_one.trans_le d)).mpr (by linarith))
  have mb : B≤M := by
    apply Nat.cast_le.mpr
    exact Nat.pow_le_pow_right (by decide : 0<2) (by change 1000*Fixed.h b≤9997*Fixed.h b; omega)
  have bo : 1≤B := by dsimp only [B,Fixed.B,Fixed.beta]; exact_mod_cast (Nat.one_le_two_pow (n:=1000*Fixed.h b))
  have bp := zero_lt_one.trans_le bo
  have mp := bp.trans_le mb
  have inv : 1/B≤exp (-(K+48)*z^2) := calc
    _ = B^(-(1:ℝ)) := by rw [rpow_neg bp.le,rpow_one,one_div]
    _ ≤ B^(-17/200:ℝ) := rpow_le_rpow_of_exponent_le bo (by norm_num)
    _ ≤ _ := save b huge
  have tail : 1/B*exp (48*z)≤e := calc
    _ ≤ exp (-(K+48)*z^2)*exp (48*z) := mul_le_mul_of_nonneg_right inv (exp_pos _).le
    _ ≤ _ := by rw [←exp_add]; apply exp_le_exp.mpr; nlinarith only [mul_nonneg (sub_nonneg.mpr zp) (zero_le_one.trans zp)]
  have mBound : (M:ℝ)/B+1≤2*((M:ℝ)/B) := by
    have h := (one_le_div bp).mpr mb
    linarith
  have tm := mul_le_mul_of_nonneg_left tail (sq_nonneg (D*(M:ℝ)))
  have hi := mul_le_mul_of_nonneg_right mBound (mul_nonneg (sq_nonneg D) (mul_nonneg mp.le (exp_pos (48*z)).le))
  have mid := mul_le_mul (mul_le_mul_of_nonneg_left eo ep)
    e8 (exp_pos _).le (by simpa only [mul_one] using ep)
  have mid2 := mul_le_mul_of_nonneg_left mid (sq_nonneg (V*(1+2*exp 6)*(M:ℝ)))
  have main := score n old ell target comp absent R T cell w D V dp vp bound zero variation
  apply (div_le_iff₀ (sq_pos_of_pos mp)).mpr
  apply main.trans
  change D^2*C*e*(M:ℝ)^2+(V*((1+2*exp 6)*(M:ℝ))*e)^2*exp (8/(Fixed.d b:ℝ))+
    (D*((M:ℝ)/B+1)*(D*M))*exp (48*z) ≤ (C+2+H)*(D^2+V^2)*e*(M:ℝ)^2
  have h1 : 0≤H*D^2*e*(M:ℝ)^2 := by positivity
  have h2 : 0≤(C+2)*V^2*e*(M:ℝ)^2 := by positivity
  have centerBound : (V*((1+2*exp 6)*(M:ℝ))*e)^2*exp (8/(Fixed.d b:ℝ))≤V^2*H*e*(M:ℝ)^2 := calc
    _ = (V*(1+2*exp 6)*(M:ℝ))^2*(e*e*exp (8/(Fixed.d b:ℝ))) := by ring
    _ ≤ _ := mid2
    _ = _ := by dsimp only [H]; ring
  have tailBound : (D*((M:ℝ)/B+1)*(D*M))*exp (48*z)≤2*D^2*e*(M:ℝ)^2 := calc
    _ = ((M:ℝ)/B+1)*(D^2*((M:ℝ)*exp (48*z))) := by ring
    _ ≤ _ := hi
    _ = 2*((D*(M:ℝ))^2*(1/B*exp (48*z))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left tm (by norm_num : (0:ℝ)≤2)
    _ = _ := by ring
  apply (add_le_add (add_le_add (le_refl _) centerBound) tailBound).trans
  linarith only [h1,h2]


end
end Cogentic.Construction
