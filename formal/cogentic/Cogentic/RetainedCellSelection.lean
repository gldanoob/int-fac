import Cogentic.CenteredSmoothVariance
import Cogentic.RetainedScoreLoss

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- Every selected mark is smooth and actually returned in the relation
matrix of the same boxed tuple. -/
def keptSmoothMark {n ell : ℕ} (R T : PrescribedRows n ell) (a : ℕ) (x y : ℤ×ℤ) : Prop :=
  smoothMarkEvent R false a x ∧ smoothMarkEvent T true a y ∧ ∃ rel,
    Marking.stageOne (TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel ∧ a∈rel.marks

private theorem retained_score_error {n ell : ℕ} (R T : PrescribedRows n ell) (X : Finset ℕ)
    (w : ℕ→ℝ) (x y : ℤ×ℤ) (bx : inCoefficientBox n x) (by' : inCoefficientBox n y) :
    let P := smoothMarkProbability R T
    let score := twoFieldScore X (fun a=>w a/P a) (smoothMarkEvent R false) (smoothMarkEvent T true) x y
    let kept := ∑ a∈X,if keptSmoothMark R T a x y then w a/P a else 0
    |kept-score| ≤ ∑ a∈X,if rejectedSmoothMark R T a x y then |w a|/P a else 0 := by
  intro P score kept
  have pn (a : ℕ) : 0≤P a := by
    have each (S : PrescribedRows n ell) (s : Bool) : 0≤prescribedProbability S s (smoothMarkEvent S s a) := by
      apply div_nonneg
      · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
      · exact tsum_nonneg (fun _=>mul_nonneg (exp_pos _).le (exp_pos _).le)
    exact mul_nonneg (each R false) (each T true)
  change |(∑ a∈X,_)-(∑ a∈X,_)|≤_
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro a ha
  by_cases f : smoothMarkEvent R false a x ∧ smoothMarkEvent T true a y
  · by_cases retain : ∃ rel, Marking.stageOne (TryPair.fixedInput n ell
          (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel ∧ a∈rel.marks
    · simp [keptSmoothMark,rejectedSmoothMark,f.1,f.2,retain]
    · simp [keptSmoothMark,rejectedSmoothMark,f.1,f.2,retain,bx,by',abs_div,abs_of_nonneg (pn a)]
  · have nk : ¬keptSmoothMark R T a x y := fun h=>f ⟨h.1,h.2.1⟩
    have nr : ¬rejectedSmoothMark R T a x y := fun h=>f ⟨h.1,h.2.1⟩
    simp [nk,nr,f]

/-- One tuple controls a whole family of signed retained scores. Quadratic
smooth-score costs and linear losses from actual stage-one deletion are
charged on the same coefficient draw. -/
theorem simultaneous_retained_cell_scores (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ {ι : Type*} (I : Finset ι) (cell : ι→Option (Bool×Fin (Fixed.d b))) (w : ι→ℕ→ℝ) (δ : ℝ), 0<δ →
    let X := fun i=>constructorCellMarks n ell (cell i); let L := fun i=>firstCellMark b (cell i); let M := cellMarkCount b
    (∀ i∈I, (∀ a∈X i,|w i a|≤1 ∧ (R.prefactor a false).Coprime (T.prefactor a true)) ∧
      (∑ j∈range M,w i (L i+j))=0 ∧
      |w i (L i+(M-1))|+(∑ j∈range (M-1),|w i (L i+(j+1))-w i (L i+j)|)≤1) →
    let e := exp (-K*(Fixed.z b:ℝ)^2)
    (I.card:ℝ)*(2*C*e/δ^2+e/δ)+2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 →
    ∃ x y : ℤ×ℤ, R.compatible false x.1 x.2 ∧ T.compatible true y.1 y.2 ∧ inCoefficientBox n x ∧ inCoefficientBox n y ∧
      ∀ i∈I, |∑ a∈X i, if keptSmoothMark R T a x y then w i a/smoothMarkProbability R T a else 0|/(M:ℝ) < 2*δ := by
  classical
  obtain ⟨C,cp,n₁,score⟩ := centered_smooth_score_decay line K hK
  obtain ⟨b₂,loss⟩ := rejected_score_loss line K hK
  refine ⟨C,cp,max n₁ (max 2 (2^b₂)),?_⟩
  intro n large ell target comp absent R T b ι I cell w δ dp X L M hypotheses e budget
  obtain ⟨old,other⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp other
  have big : b₂≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  let Ω := R.CoeffPoint false × T.CoeffPoint true
  let W := twoFieldWeight R T
  let P := smoothMarkProbability R T
  let f (i : ι) := fun a=>w i a/P a
  let s (i : ι) (k : Ω) := twoFieldScore (X i) (f i) (smoothMarkEvent R false) (smoothMarkEvent T true) k.1.val k.2.val
  let d (i : ι) (k : Ω) := ∑ a∈X i, if rejectedSmoothMark R T a k.1.val k.2.val then |w i a|/P a else 0
  have mp : 0<(M:ℝ) := by dsimp [M,cellMarkCount]; positivity
  have terms (i : ι) (hi : i∈I) : ∃ m : ℝ,
      HasSum (fun k : Ω => W k*((s i k)^2/(M:ℝ)^2/δ^2+d i k/M/δ)) m ∧ m≤2*C*e/δ^2+e/δ := by
    obtain ⟨localBounds,center,var⟩ := hypotheses i hi
    have smooth := score n old ell target comp absent R T (cell i) (w i) 1 1 zero_le_one zero_le_one
      (fun a ha=>(localBounds a ha).1) center var
    have hs := twoField_score_second R T target (X i) (f i) (smoothMarkEvent R false) (smoothMarkEvent T true)
    let ξ := twoFieldSecond R T (X i) (f i) (smoothMarkEvent R false) (smoothMarkEvent T true)
    change HasSum (fun k : Ω=>W k*(s i k)^2) ξ at hs
    change (∑' k : Ω,W k*(s i k)^2)/(M:ℝ)^2≤C*((1:ℝ)^2+1^2)*e at smooth
    rw [hs.tsum_eq] at smooth
    obtain ⟨μ,hd,upper⟩ := loss R T big hn comp target absent (X i) (w i) (fun a ha=>(mem_filter.mp ha).2)
      (fun a ha=>(localBounds a ha).2)
    change HasSum (fun k : Ω=>W k*d i k) μ at hd
    have card : (X i).card≤M := (card_filter_le ..).trans_eq (by simp only [Nat.card_Ico,Nat.add_sub_cancel_left]; rfl)
    have size : (∑ a∈X i, |w i a|)≤M := calc
      _ ≤ ∑ _a∈X i, (1:ℝ) := sum_le_sum (fun a ha=>(localBounds a ha).1)
      _ ≤ _ := by simpa only [sum_const,nsmul_one] using (Nat.cast_le.mpr card : ((X i).card:ℝ)≤M)
    have mu : μ/(M:ℝ)≤e := (div_le_iff₀ mp).mpr (upper.trans (mul_le_mul_of_nonneg_left size (exp_pos _).le))
    refine ⟨ξ/(M:ℝ)^2/δ^2+μ/M/δ,?_ ,?_⟩
    · apply (((hs.div_const ((M:ℝ)^2)).div_const (δ^2)).add ((hd.div_const (M:ℝ)).div_const δ)).congr_fun
      intro k; ring
    · apply add_le_add _ (div_le_div_of_nonneg_right mu dp.le)
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith only [smooth]
  choose m sums errors using terms
  let fn (i : ι) (k : Ω) := (s i k)^2/(M:ℝ)^2/δ^2+d i k/M/δ
  let cost (k : Ω) := ∑ i∈I,fn i k
  have dn (i : ι) (k : Ω) : 0≤d i k := sum_nonneg (fun a _ => by
    split
    · apply div_nonneg (abs_nonneg _)
      apply mul_nonneg <;> apply div_nonneg <;> apply tsum_nonneg <;> intro t <;>
        first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · rfl)
  have nn (i : ι) (k : Ω) : 0≤fn i k := add_nonneg
    (div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) (div_nonneg (div_nonneg (dn i k) mp.le) dp.le)
  have total := hasSum_sum (s:=I.attach) (fun i _=>sums i.val i.property)
  have hs : HasSum (fun k : Ω=>W k*cost k) (∑ i∈I.attach,m i.val i.property) := by
    apply total.congr_fun; intro k
    dsimp only [cost,fn]
    rw [mul_sum,←sum_attach I]
  have limit : (∑ i∈I.attach,m i.val i.property)≤(I.card:ℝ)*(2*C*e/δ^2+e/δ) := by
    calc _ ≤ ∑ _i∈I.attach, (2*C*e/δ^2+e/δ) := sum_le_sum (fun i _=>errors i.val i.property)
         _ = _ := by simp [mul_add]
  obtain ⟨k,bx,by',cheap⟩ := twoField_box_of_cost R T target cost _
    (fun k=>sum_nonneg (fun i _=>nn i k)) hs (lt_of_le_of_lt (add_le_add_left limit _) budget)
  refine ⟨k.1.val,k.2.val,k.1.property,k.2.property,bx,by',?_⟩
  intro i hi
  have localCost := (single_le_sum (f:=fun j=>fn j k) (fun j _=>nn j k) hi).trans_lt cheap
  have sd := (le_add_of_nonneg_right (div_nonneg (div_nonneg (dn i k) mp.le) dp.le)).trans_lt localCost
  have dd := (le_add_of_nonneg_left (div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))).trans_lt localCost
  have hs : |s i k|/(M:ℝ)<δ := by
    apply (sq_lt_sq₀ (div_nonneg (abs_nonneg _) mp.le) dp.le).mp
    rw [div_pow,sq_abs]
    exact (div_lt_one (sq_pos_of_pos dp)).mp sd
  have hd : d i k/M<δ := (div_lt_one dp).mp dd
  let kept := ∑ a∈X i,if keptSmoothMark R T a k.1.val k.2.val then f i a else 0
  have diff := retained_score_error R T (X i) (w i) k.1.val k.2.val bx by'
  change |kept-s i k|≤d i k at diff
  have total : |kept|≤|s i k|+d i k := calc
    _ = |s i k+(kept-s i k)| := by ring_nf
    _ ≤ _ := (abs_add_le ..).trans (add_le_add le_rfl diff)
  change |kept|/(M:ℝ)<2*δ
  have v := div_le_div_of_nonneg_right total mp.le
  rw [add_div] at v
  linarith only [hs,hd,v]

/-- Polynomially many prescribed tests on possibly different cells are
simultaneously small after actual stage-one deletion on one boxed tuple. -/
theorem polynomial_retained_cell_scores (line : DirichletLZerosOnLine) (k : ℕ) (K : ℝ) (hK : 1≤K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ {ι : Type*} (I : Finset ι) (cell : ι→Option (Bool×Fin (Fixed.d b))) (w : ι→ℕ→ℝ), I.card≤b^k →
    let X := fun i=>constructorCellMarks n ell (cell i); let L := fun i=>firstCellMark b (cell i); let M := cellMarkCount b
    (∀ i∈I, (∀ a∈X i,|w i a|≤1 ∧ (R.prefactor a false).Coprime (T.prefactor a true)) ∧
      (∑ j∈range M,w i (L i+j))=0 ∧
      |w i (L i+(M-1))|+(∑ j∈range (M-1),|w i (L i+(j+1))-w i (L i+j)|)≤1) →
    ∃ x y : ℤ×ℤ, R.compatible false x.1 x.2 ∧ T.compatible true y.1 y.2 ∧ inCoefficientBox n x ∧ inCoefficientBox n y ∧
      ∀ i∈I, |∑ a∈X i, if keptSmoothMark R T a x y then w i a/smoothMarkProbability R T a else 0|/(M:ℝ) < 2*exp (-K*(Fixed.z b:ℝ)^2) := by
  let V := 2*K+(k:ℝ)+1
  have high : 1≤V := by dsimp only [V]; linarith only [hK,Nat.cast_nonneg (α:=ℝ) k]
  obtain ⟨C,cp,n₁,select⟩ := simultaneous_retained_cell_scores line V high
  obtain ⟨b₂,small⟩ := fixed_class_accuracy (2*C+1)
  refine ⟨max n₁ (2^(max b₂ 1000)),?_⟩
  intro n large ell target comp absent R T b ι I cell w card X L M weights
  obtain ⟨old,large⟩ := max_le_iff.mp large
  have hn := (Nat.pow_pos (by decide) : 0<2^(max b₂ 1000)).trans_le large
  have big : max b₂ 1000≤b := ((Nat.le_log2 hn.ne').mpr large).trans (Nat.le_succ _)
  let z : ℝ := Fixed.z b; let δ := exp (-K*z^2); let e := exp (-V*z^2)
  have dp : 0<δ := exp_pos _
  apply select n old ell target comp absent R T I cell w δ dp weights
  have zp : 1≤z := by dsimp only [z,Fixed.z]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le b.log2)
  have bz : (b:ℝ)≤exp z := by
    have a : (b:ℝ)≤(2:ℝ)^(Fixed.z b) := by exact_mod_cast (Nat.lt_log2_self.le : b≤2^(Fixed.z b))
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith [exp_one_gt_d9] : (2:ℝ)≤exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at h
    exact a.trans h
  have count : (I.card:ℝ)≤exp ((k:ℝ)*z) := calc
    _ ≤ (b:ℝ)^k := by exact_mod_cast card
    _ ≤ _ := by rw [exp_nat_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) bz _
  have ratio : e/δ^2=exp (-((k:ℝ)+1)*z^2) := by
    dsimp only [e,δ,V]
    rw [←exp_nat_mul,←exp_sub]
    congr 1; push_cast; ring
  have do' : δ≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have tame : e/δ≤e/δ^2 := div_le_div_of_nonneg_left (exp_pos _).le (sq_pos_of_pos dp)
    (by nlinarith only [mul_le_mul_of_nonneg_left do' dp.le])
  have scale : (I.card:ℝ)*(e/δ^2)≤exp (-z^2) := calc
    _ ≤ exp ((k:ℝ)*z)*(e/δ^2) := mul_le_mul_of_nonneg_right count (div_nonneg (exp_pos _).le (sq_nonneg _))
    _ ≤ _ := by
      rw [ratio,←exp_add]; apply exp_le_exp.mpr
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (mul_nonneg (sub_nonneg.mpr zp) (zero_le_one.trans zp))]
  have bound : (I.card:ℝ)*(2*C*e/δ^2+e/δ)≤1/2 := calc
    _ ≤ (I.card:ℝ)*(2*C*e/δ^2+e/δ^2) := mul_le_mul_of_nonneg_left (add_le_add le_rfl tame) (Nat.cast_nonneg _)
    _ = (2*C+1)*((I.card:ℝ)*(e/δ^2)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left scale (by positivity)).trans (small b (max_le_iff.mp big).1)
  have tail := coefficient_tail_lt_half_mark (max_le_iff.mp big).2
  have bp : 2≤(Fixed.B b:ℝ) := by
    have hb : 0<Fixed.beta b := Nat.mul_pos (by decide) (Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _))
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hb : 2^1≤Fixed.B b)
  have den : 1/(2*(Fixed.B b:ℝ))≤1/4 := by
    rw [div_le_div_iff₀ (by positivity : 0<2*(Fixed.B b:ℝ)) (by norm_num : (0:ℝ)<4)]; linarith
  change (I.card:ℝ)*(2*C*e/δ^2+e/δ)+_ < 1
  linarith only [bound,tail.trans_le den]


end
end Cogentic.Construction
