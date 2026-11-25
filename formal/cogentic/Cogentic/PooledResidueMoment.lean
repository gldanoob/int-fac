import Cogentic.DistinctPrimeGram

namespace Cogentic.Construction
open Finset Real
noncomputable section
open scoped Classical

/-- Weights at repeated marks add before the second moment is taken. -/
def pooledMarkWeight {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ) (a : ℕ) : ℝ :=
  ∑ i∈S, if a∈Y i then f i a else 0

private theorem pool_sum {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ) (g : ℕ→ℝ) :
    ∑ a∈S.biUnion Y, pooledMarkWeight S Y f a*g a = ∑ i∈S, ∑ a∈Y i, f i a*g a := by
  simp only [pooledMarkWeight,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp only [ite_mul,zero_mul,←sum_filter]
  congr 1
  rw [filter_mem_eq_inter,inter_eq_right.mpr (subset_biUnion_of_mem Y hi)]

private theorem pool_class {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ)
    (P : ℕ→Prop) [DecidablePred P] :
    ∑ a∈S.biUnion Y with P a, pooledMarkWeight S Y f a =
      ∑ i∈S, ∑ a∈Y i with P a, f i a := by
  simpa only [mul_ite,mul_one,mul_zero,←sum_filter] using pool_sum S Y f (fun a=>if P a then 1 else 0)

private theorem pool_abs_class {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ)
    (P : ℕ→Prop) [DecidablePred P] :
    (∑ a∈S.biUnion Y with P a, |pooledMarkWeight S Y f a|) ≤
      ∑ i∈S, ∑ a∈Y i with P a, |f i a| := by
  rw [←pool_class]
  apply sum_le_sum
  intro a _
  apply (abs_sum_le_sum_abs ..).trans_eq
  apply sum_congr rfl
  intro i _
  split <;> simp_all

private theorem pool_bilinear {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ)
    (E : ℕ→ℕ→ℝ) :
    let Z := S.biUnion Y; let W := pooledMarkWeight S Y f
    ∑ a∈Z, ∑ y∈Z, W a*W y*E a y = ∑ i∈S,∑ j∈S,∑ a∈Y i,∑ y∈Y j,f i a*f j y*E a y := by
  intro Z W
  have row (a) : (∑ y∈Z,W a*W y*E a y) = W a*(∑ j∈S,∑ y∈Y j,f j y*E a y) := by
    rw [←pool_sum];simp only [Z,W,mul_sum,mul_assoc]
  simp_rw [row]
  rw [pool_sum]
  apply sum_congr rfl;intro i _
  simp only [mul_sum,mul_assoc]
  rw [sum_comm]

private theorem class_abs {L M q h r s : ℕ} (qp : 0<q) (hp : 0<h) (cop : h.Coprime q)
    (X : Finset ℕ) (sub : X⊆Ico L (L+M)) (f : ℕ→ℝ) (D : ℝ) (dp : 0≤D)
    (fb : ∀ a∈X, |f a|≤D) :
    let Y := X.filter (fun a=>a ≡ r [MOD q])
    (∑ a∈Y with a ≡ s [MOD h], |(q:ℝ)*f a|) ≤ D*((M:ℝ)/h+q) := by
  intro Y
  let Z := Y.filter (fun a=>a ≡ s [MOD h])
  let v := Nat.chineseRemainder cop s r
  have incl : Z ⊆ (Ico L (L+M)).filter (fun a=>a ≡ v.val [MOD h*q]) := by
    intro a ha
    obtain ⟨ay,hs⟩ := mem_filter.mp ha
    obtain ⟨ax,aq⟩ := mem_filter.mp ay
    exact mem_filter.mpr ⟨sub ax,Nat.chineseRemainder_modEq_unique cop hs aq⟩
  have cnt := (abs_le.mp (interval_residue_error (Nat.le_add_right L M) (Nat.mul_pos hp qp) v.val)).2
  simp only [Nat.cast_add,add_sub_cancel_left,Nat.cast_mul] at cnt
  have bound : (Z.card:ℝ)≤(M:ℝ)/(h*q)+1 :=
    (Nat.cast_le.mpr (card_le_card incl)).trans (by linarith only [cnt])
  have sum := sum_le_sum (s:=Z) (fun a ha=> mul_le_mul_of_nonneg_left (fb a (mem_filter.mp (mem_filter.mp ha).1).1) (Nat.cast_nonneg (α:=ℝ) q))
  simp only [sum_const,nsmul_eq_mul] at sum
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) q)]
  apply sum.trans ((mul_le_mul_of_nonneg_right bound (by positivity : 0≤(q:ℝ)*D)).trans_eq ?_)
  field_simp

/-- Joint second moment of signed congruence components across arbitrary
constructor cells, with a single coefficient draw. Only the sum of the raw
mesh means enters the shared small-divisor term. Cell components may overlap. -/
theorem pooled_residue_score_second {ι : Type*} (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (S : Finset ι) (cell : ι→Option (Bool×Fin (Fixed.d b))) (q r : ι→ℕ) (f : ι→ℕ→ℝ) (D : ι→ℝ),
    (∀ i∈S, 0<q i ∧ Squarefree (q i) ∧ q i≤(Fixed.B b)^3 ∧ (q i).Coprime (markModulus n ell) ∧
      ∀ p∈pairCorrectionPrimes b,p.Coprime (q i)) →
    (∀ i∈S, 0≤D i ∧ ∀ a∈constructorCellMarks n ell (cell i), |f i a|≤D i) →
    let M := cellMarkCount b; let L := fun i=>firstCellMark b (cell i)
    let Y := fun i=>(constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ r i [MOD q i])
    let X := S.biUnion Y; let W := pooledMarkWeight S Y (fun i a=>(q i:ℝ)*f i a)
    let δ := ∑ i∈S,∑ j∈range M,f i (L i+j)
    let V := ∑ i∈S,meshVariation (L i) M (f i); let A := ∑ i∈S,D i
    let z := (Fixed.z b:ℝ); let e := exp (-K*z^2); let B := (Fixed.B b:ℝ)
    twoFieldSecond R T X (fun a=>W a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true) ≤
      A^2*C*e*(M:ℝ)^2 + (|δ|+V*(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ)) +
        4*A^2*(M:ℝ)^2/B*exp (48*z) := by
  classical
  obtain ⟨n₀,drift⟩ := residue_class_contrast_drift line K hK
  obtain ⟨b₀,weight⟩ := fixed_pair_weight_sum line
  obtain ⟨C,cp,b₁,pair⟩ := cell_pair_covariance_approximation line K hK
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨C,cp,max n₀ (max 2 (2^max b₀ (max b₁ b₂))),?_⟩
  intro n large ell target comp absent R T b S cell q r f D props bounds M L Y X W δ V A z e B
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  obtain ⟨bw,bc⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  obtain ⟨bpair,bfloor⟩ := max_le_iff.mp bc
  let P := pairCorrectionPrimes b
  have pr (p) (pm : p∈P) := (mem_pairCorrectionPrimes.mp pm).1
  have sizes (p) (pm : p∈P) : Fixed.d b<p ∧ p≤Fixed.B b :=
    ⟨(mem_pairCorrectionPrimes.mp pm).2.1,(mem_pairCorrectionPrimes.mp pm).2.2.trans
      (Nat.pow_le_pow_right (by decide) (by change 200*Fixed.h b≤1000*Fixed.h b;omega))⟩
  have hp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have Br : 0<B := by dsimp only [B];exact_mod_cast bp
  have mp : 0<(M:ℝ) := by dsimp [M,cellMarkCount];positivity
  have ap : 0≤A := sum_nonneg (fun i h=>(bounds i h).1)
  let c := |δ|+V*(1+2*exp 6)*M*e
  let amp := fun i a=>(q i:ℝ)*f i a
  have cop (U) (sub : U⊆P) (i) (hi : i∈S) : (sieveProduct U).Coprime (q i) :=
    (Nat.coprime_prod_right_iff.mpr (fun p pm=>((props i hi).2.2.2.2 p (sub pm)).symm)).symm
  have short (U) (sub : U⊆P) (low : sieveProduct U≤Fixed.B b) (s) (ls : s<sieveProduct U)
      (good : ∀ p∈U, ¬s ≡ Fixed.rootBase n [MOD p]) :
      |∑ a∈X with a%(sieveProduct U)=s,W a|≤c/(sieveProduct U:ℝ) := by
    let h := sieveProduct U
    have hpos : 0<h := prod_pos (fun p pm=>(pr p (sub pm)).pos)
    have hr : (0:ℝ)<h := by exact_mod_cast hpos
    let ρ := ∏ p∈(markModulus n ell).primeFactors with ¬p∣h,(1-(p:ℝ)⁻¹)
    have rh : ρ∈Set.Icc (0:ℝ) 1 := by
      have unit (p) (pm : p∈(markModulus n ell).primeFactors) : (1:ℝ)≤p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors pm).one_le
      have pos (p) (pm : p∈(markModulus n ell).primeFactors) : 0≤1-(p:ℝ)⁻¹ :=
        sub_nonneg.mpr ((inv_le_one₀ (zero_lt_one.trans_le (unit p pm))).mpr (unit p pm))
      exact ⟨prod_nonneg (fun p ph=>pos p (mem_filter.mp ph).1),prod_le_one (fun p ph=>pos p (mem_filter.mp ph).1)
        (fun p _=>sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _)))⟩
    have elig (p) (pm : p∈(markModulus n ell).primeFactors) (ph : p∣h) : ¬s ≡ Fixed.rootBase n [MOD p] := by
      have pp := Nat.prime_of_mem_primeFactors pm
      obtain ⟨a,atU,pa⟩ := (pp.prime.dvd_finsetProd_iff id).mp ph
      exact good p (((Nat.prime_dvd_prime_iff_eq pp (pr a (sub atU))).mp pa) ▸ atU)
    let δi := fun i=> ∑ j∈range M,f i (L i+j)
    let xi := fun i=> ∑ a∈Y i with a ≡ s [MOD h],amp i a
    have localDrift (i) (hi : i∈S) :
        |xi i-δi i*(ρ/h)| ≤ meshVariation (L i) M (f i)*(1+2*exp 6)*((M:ℝ)/h)*e := by
      obtain ⟨qp,_,qb,clean,_⟩ := props i hi
      have est := drift n old ell target comp absent (cell i) h (q i) s (r i) hpos qp (cop U sub i hi) clean
        ((Nat.mul_le_mul low qb).trans_eq (by ring)) elig (f i) (fun _=>0)
      dsimp only [xi,Y,amp];rw [←mul_sum]
      have perm : (((constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ r i [MOD q i])).filter (fun a=>a ≡ s [MOD h])) =
        (((constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ s [MOD h])).filter (fun a=>a ≡ r i [MOD q i])) := filter_comm ..
      rw [perm];simpa only [sum_const_zero,sub_zero,abs_zero,add_zero,meshVariation] using est
    have folded := (abs_sum_le_sum_abs (fun i=>xi i-δi i*(ρ/h)) S).trans (sum_le_sum localDrift)
    simp only [sum_sub_distrib,←sum_mul] at folded
    change |(∑ i∈S,xi i)-δ*(ρ/h)|≤V*(1+2*exp 6)*((M:ℝ)/h)*e at folded
    have triangle := abs_add_le ((∑ i∈S,xi i)-δ*(ρ/h)) (δ*(ρ/h))
    rw [sub_add_cancel] at triangle
    have bias : |δ*(ρ/h)|≤|δ|/h := by
      rw [abs_mul,abs_of_nonneg (div_nonneg rh.1 hr.le),←mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) rh.2) hr.le
    have same : X.filter (fun a=>a%(sieveProduct U)=s)=X.filter (fun a=> a ≡ s [MOD h]) := by
      ext a;simp [h,Nat.ModEq,Nat.mod_eq_of_lt ls]
    rw [same,pool_class]
    exact triangle.trans ((add_le_add folded bias).trans_eq (by dsimp only [c];ring))
  have ml : (Fixed.B b)^4≤M := by change (2^(1000*Fixed.h b))^4≤2^(9997*Fixed.h b)
                                  rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  have qc (i) (hi : i∈S) : (q i:ℝ)≤M/B := by
    apply (le_div_iff₀ Br).mpr
    have h := (Nat.mul_le_mul_right (Fixed.B b) (props i hi).2.2.1).trans ((by ring : (Fixed.B b)^3*Fixed.B b=(Fixed.B b)^4) ▸ ml)
    dsimp only [B];exact_mod_cast h
  have classMass h s (hh : 0<h) (hc : ∀ i∈S,h.Coprime (q i)) :
      (∑ a∈X with a ≡ s [MOD h], |W a|)≤A*((M:ℝ)/h+M/B) := by
    apply (pool_abs_class S Y amp _).trans
    rw [show A*((M:ℝ)/h+M/B)=∑ i∈S,D i*((M:ℝ)/h+M/B) by rw [←sum_mul]]
    apply sum_le_sum
    intro i hi
    obtain ⟨di,fb⟩ := bounds i hi
    have est := class_abs (L:=L i) (M:=M) (q:=q i) (r:=r i) (s:=s) (props i hi).1 hh (hc i hi)
      (constructorCellMarks n ell (cell i)) (filter_subset ..) (f i) (D i) di fb
    exact est.trans (mul_le_mul_of_nonneg_left (add_le_add_right (qc i hi) _) di)
  let H := 2*A*(M/B)
  have Hp : 0≤H := by dsimp only [H];positivity
  have mid U (sub : U⊆P) (lo : Fixed.B b<sieveProduct U) (_ : sieveProduct U≤(Fixed.B b)^2) s :
      (∑ a∈X with a ≡ s [MOD sieveProduct U], |W a|)≤H := by
    have est := classMass (sieveProduct U) s (bp.trans lo) (cop U sub)
    have rat := div_le_div_of_nonneg_left mp.le Br (by dsimp only [B];exact_mod_cast lo.le : B≤(sieveProduct U:ℝ))
    exact est.trans ((mul_le_mul_of_nonneg_left (add_le_add_left rat _) ap).trans_eq (by dsimp only [H];ring))
  have mass : (∑ a∈X,|W a|)≤2*A*M := by
    have est := classMass 1 0 (by decide) (fun i _=>Nat.coprime_one_left _)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at est
    have rat : (M:ℝ)/B≤M := div_le_self mp.le (by dsimp only [B];exact_mod_cast bp : 1≤B)
    exact est.trans ((mul_le_mul_of_nonneg_left (add_le_add_right rat _) ap).trans_eq (by ring))
  have wtpos : 0≤∑ U∈P.powerset,pairDivisorWeight U := sum_nonneg (fun U h=>prod_nonneg (fun p pm=>by
    have lb : (2:ℝ)≤p := by exact_mod_cast (pr p ((mem_powerset.mp h) pm)).two_le
    exact div_nonneg (by linarith) (sq_nonneg _)))
  have gamma := centered_pair_bound X P pr (Fixed.rootBase n) (Fixed.d b) (Fixed.B b) hp bp sizes W c H short mid Hp
  have tail := mul_le_mul (mul_le_mul_of_nonneg_left mass Hp) (weight b bw P (fun p pm=>⟨pr p pm,sizes p pm⟩)) wtpos (by positivity)
  let γ := fun a y=>pairGamma P (Fixed.rootBase n) a y
  have model : (∑ a∈X,∑ y∈X,W a*W y*γ a y^2)≤c^2*exp (8/(Fixed.d b:ℝ))+4*A^2*(M:ℝ)^2/B*exp (48*z) :=
    gamma.trans (add_le_add le_rfl (tail.trans_eq (by dsimp only [H,z];ring)))
  let E := fun a y=>normalizedSmoothCovariance R T a y-(γ a y^2-1)
  have cross (i) (hi : i∈S) (j) (hj : j∈S) :
      (∑ a∈Y i,∑ y∈Y j,amp i a*amp j y*E a y)≤D i*D j*(C*e)*(M:ℝ)^2 := by
    obtain ⟨_,sqi,qi,_,_⟩ := props i hi
    obtain ⟨_,sqj,qj,_,_⟩ := props j hj
    obtain ⟨dpi,fi⟩ := bounds i hi
    obtain ⟨dpj,fj⟩ := bounds j hj
    have est := pair R T bpair hn comp target absent (cell i) (cell j) (q i) (q j) (r i) (r j)
      sqi sqj qi qj (f i) (f j) (D i) (D j) dpi dpj (fun a ha=>fi a (mem_filter.mp ha).1)
      (fun a ha=>fj a (mem_filter.mp ha).1)
    change (q i:ℝ)*q j*|∑ a∈Y i,∑ y∈Y j,f i a*f j y*E a y|/(M:ℝ)^2≤D i*D j*(C*e) at est
    have raw := (div_le_iff₀ (sq_pos_of_pos mp)).mp est
    have lhs : (∑ a∈Y i,∑ y∈Y j,amp i a*amp j y*E a y) =
        (q i:ℝ)*q j*(∑ a∈Y i,∑ y∈Y j,f i a*f j y*E a y) := by
      simp only [mul_sum];apply sum_congr rfl;intro a _
      apply sum_congr rfl;intro y _;dsimp only [amp];ring
    rw [lhs]
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans raw
  have err : (∑ a∈X,∑ y∈X,W a*W y*E a y) ≤ A^2*C*e*(M:ℝ)^2 := by
    rw [pool_bilinear S Y amp E]
    apply (sum_le_sum (fun i hi=>sum_le_sum (fun j hj=>cross i hi j hj))).trans_eq
    simp only [←sum_mul,←mul_sum,A];ring
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    obtain ⟨_,_,hay⟩ := mem_biUnion.mp ha
    have mark := (mem_filter.mp (mem_filter.mp hay).1).2
    have lb : 0<8/(Fixed.B b:ℝ) := by positivity
    have each (U : PrescribedRows n ell) side : 0<prescribedProbability U side (smoothMarkEvent U side a) := by
      have raw := lb.trans_le (floor U bfloor hn comp target absent mark side)
      exact raw.trans_eq (probability_congr U side _ (smoothMarkEvent U side a) rfl)
    exact mul_pos (each R false) (each T true)
  have splitMoment : twoFieldSecond R T X (fun a=>W a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true) =
      (∑ a∈X,∑ y∈X,W a*W y*E a y)+(∑ a∈X,∑ y∈X,W a*W y*γ a y^2) := by
    dsimp only [twoFieldSecond];rw [←sum_add_distrib];apply sum_congr rfl;intro a ha
    rw [←sum_add_distrib];apply sum_congr rfl;intro y hy
    dsimp only [E,normalizedSmoothCovariance,twoFieldIndicatorCovariance]
    change W a / smoothMarkProbability R T a * (W y / smoothMarkProbability R T y) * ?joint =
      W a*W y*((?joint-smoothMarkProbability R T a*smoothMarkProbability R T y)/
        (smoothMarkProbability R T a*smoothMarkProbability R T y)-(γ a y^2-1))+W a*W y*γ a y^2
    field_simp [(pos a ha).ne',(pos y hy).ne'];ring
  rw [splitMoment]
  exact (add_le_add err model).trans_eq (by dsimp only [c];ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.pooled_residue_score_second
