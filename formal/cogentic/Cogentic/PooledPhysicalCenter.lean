import Cogentic.PooledResidueMoment

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- Center a pooled numerator by the *same* drawn pooled denominator.
The ratio of their true conditional first moments makes the signed score
exactly mean zero. Both profiles may use an arbitrary common mark weight. -/
theorem pooled_ratio_center_exact {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (S : Finset ι) (Y : ι→Finset ℕ) (q : ι→ℕ) (normalizer : ℕ→ℝ) (f g : ι→ℕ→ℝ) :
    let X := S.biUnion Y; let W := fun (h : ι→ℕ→ℝ) a=>pooledMarkWeight S Y (fun i v=>(q i:ℝ)*h i v) a
    let mean := fun h=>twoFieldMean R T X (fun a=>W h a/normalizer a) (smoothMarkEvent R false) (smoothMarkEvent T true)
    let θ := mean f/mean g
    mean g≠0 → mean (fun i a=>f i a-θ*g i a)=0 := by
  intro X W mean θ nz
  have point (a) : W (fun i v=>f i v-θ*g i v) a=W f a-θ*W g a := by
    dsimp only [W,pooledMarkWeight]
    rw [mul_sum,←sum_sub_distrib];apply sum_congr rfl
    intro i _
    by_cases inside : a∈Y i <;> simp only [inside,if_true,if_false] <;> ring
  have linear : mean (fun i a=>f i a-θ*g i a)=mean f-θ*mean g := by
    dsimp only [mean,twoFieldMean]
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl;intro a _
    rw [point];ring
  rw [linear,show θ*mean g=mean f from div_mul_cancel₀ _ nz,sub_self]

/-- The physical conditional first moment controls the drift term in the
second moment of a signed CRT profile. An exactly zero first moment removes
that contribution for the whole cell mixture, even with nonzero cell means. -/
theorem pooled_physical_center_second {ι : Type*} (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
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
    let mean := twoFieldMean R T X (fun a=>W a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true)
    let V := ∑ i∈S,meshVariation (L i) M (f i); let A := ∑ i∈S,D i
    let z := (Fixed.z b:ℝ); let e := exp (-K*z^2); let B := (Fixed.B b:ℝ)
    twoFieldSecond R T X (fun a=>W a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true) ≤
      A^2*C*e*(M:ℝ)^2 + (4*|mean|+5*V*(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ)) +
        4*A^2*(M:ℝ)^2/B*exp (48*z) := by
  classical
  obtain ⟨C,cp,n₁,pooled⟩ := pooled_residue_score_second (ι:=ι) line K hK
  obtain ⟨n₂,drift⟩ := residue_class_contrast_drift line K hK
  obtain ⟨n₃,density⟩ := mark_density_from_critical_line line
  obtain ⟨b₄,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨C,cp,max (max n₁ n₂) (max n₃ (max 2 (2^b₄))),?_⟩
  intro n large ell target comp absent R T b S cell q r f D props bounds M L Y X W mean V A z e B
  obtain ⟨both,rest⟩ := max_le_iff.mp large
  obtain ⟨old,nd⟩ := max_le_iff.mp both
  obtain ⟨nr,rest⟩ := max_le_iff.mp rest
  obtain ⟨hn,lim⟩ := max_le_iff.mp rest
  have bf : b₄≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  let P := (markModulus n ell).primeFactors; let ρ := ∏ p∈P,(1-(p:ℝ)⁻¹)
  have rh : 1/4≤ρ := (density n nr ell target comp absent).2
  have rpos : 0≤ρ := (by norm_num : (0:ℝ)≤1/4).trans rh
  let μ (i) := (q i:ℝ)*(∑ a∈Y i,f i a)
  let m (i) := ∑ j∈range M,f i (L i+j)
  let v (i) := meshVariation (L i) M (f i)
  let E := (1+2*exp 6)*(M:ℝ)*e
  have ok (p : ℕ) (hp : p∈P) : ¬p∣1 := (Nat.prime_of_mem_primeFactors hp).not_dvd_one
  have keep : P.filter (fun p=>¬p∣1)=P := filter_true_of_mem ok
  have each (i) (hi : i∈S) : |μ i-m i*ρ|≤v i*E := by
    have cap := (props i hi).2.2.1.trans (Nat.pow_le_pow_right (Nat.pow_pos (by decide)) (by decide : 3≤4))
    have law := drift n nd ell target comp absent (cell i) 1 (q i) 0 (r i) (by decide)
      (props i hi).1 (Nat.coprime_one_left _) (props i hi).2.2.2.1 (by rw [one_mul]; exact cap)
      (fun p hp ph=>(ok p hp ph).elim) (f i) (fun _=>0)
    dsimp only at law
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one,sum_const_zero,sub_zero,abs_zero,sub_self,add_zero] at law
    change |μ i-m i*(∏ p∈P with ¬p∣1,(1-(p:ℝ)⁻¹))|≤v i*(1+2*exp 6)*M*e at law
    rw [keep] at law
    exact law.trans_eq (by dsimp only [E];ring)
  have mark (a) (ha : a∈X) : a∈(construct n ell 0 0 0 0).marks := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp (mem_filter.mp hi).1).2
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    have lb : 0<8/(Fixed.B b:ℝ) := by dsimp [Fixed.B];positivity
    have p (U : PrescribedRows n ell) side : 0<prescribedProbability U side (smoothMarkEvent U side a) :=
      (lb.trans_le (floor U bf hn comp target absent (mark a ha) side)).trans_eq (probability_congr U side _ _ rfl)
    exact mul_pos (p R false) (p T true)
  have eq : mean=∑ i∈S,μ i := by
    change (∑ a∈X,W a/smoothMarkProbability R T a*smoothMarkProbability R T a)=_
    calc _ = ∑ a∈X,W a := sum_congr rfl (fun a ha=>div_mul_cancel₀ _ (pos a ha).ne')
         _ = _ := by
           dsimp only [W,pooledMarkWeight]
           rw [sum_comm];apply sum_congr rfl;intro i hi
           rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (subset_biUnion_of_mem Y hi),←mul_sum]
  have pooledError : |mean-(∑ i∈S,m i)*ρ|≤V*E := by
    rw [eq,sum_mul,←sum_sub_distrib]
    exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum each).trans_eq (sum_mul ..).symm)
  have bound : |∑ i∈S,m i|≤4*|mean|+4*V*E := by
    have absSum := abs_sub (mean) (mean-(∑ i∈S,m i)*ρ)
    rw [sub_sub_cancel,abs_mul,abs_of_nonneg rpos] at absSum
    linarith only [absSum,pooledError,mul_le_mul_of_nonneg_left rh (abs_nonneg (∑ i∈S,m i))]
  have vpos : 0≤V := sum_nonneg (fun i _=>add_nonneg (abs_nonneg _) (sum_nonneg (fun _ _=>abs_nonneg _)))
  have ep : 0≤E := by dsimp [E,e];positivity
  have term : |∑ i∈S,m i|+V*E ≤ 4*|mean|+5*V*E := by linarith only [bound]
  have sq := pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (mul_nonneg vpos ep)) term 2
  have law := pooled n old ell target comp absent R T S cell q r f D props bounds
  apply law.trans
  apply add_le_add_left
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  convert sq using 2 <;> dsimp only [E] <;> ring

end
end Cogentic.Construction

#print axioms Cogentic.Construction.pooled_physical_center_second

#print axioms Cogentic.Construction.pooled_ratio_center_exact
