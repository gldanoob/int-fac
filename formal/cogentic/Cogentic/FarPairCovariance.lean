import Cogentic.NearVarianceComplete
import Cogentic.ActualPairGamma
import Cogentic.AllFarPairs
import Cogentic.PairWeights

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

private theorem relative_pair (J c m γ C e : ℝ)
    (gp : 0<γ) (mp : 0 < c*m) (lower : γ≤c) (upper : c≤γ*(1+e)) (eo : e≤1)
    (est : |J/(c*m)-1|≤C*e) : 0 < m ∧ |J/(γ*m)-1|≤(2*C+1)*e := by
  have cp : 0 < c := gp.trans_le lower
  have mpos := pos_of_mul_pos_right mp cp.le
  let t := c/γ
  have t1 : 1≤t := (one_le_div gp).mpr lower
  have t2 : t≤1+e := (div_le_iff₀ gp).mpr (upper.trans_eq (mul_comm ..))
  have tn : 0≤t := zero_le_one.trans t1
  have fact : J/(γ*m)-1=(J/(c*m)-1)*t+(t-1) := by
    dsimp only [t]; field_simp [gp.ne',cp.ne',mpos.ne']; ring
  rw [fact]
  refine ⟨mpos,(abs_add_le ..).trans ?_⟩
  rw [abs_mul,abs_of_nonneg tn,abs_of_nonneg (sub_nonneg.mpr t1)]
  have prod := mul_le_mul est (show t≤2 by linarith) tn ((abs_nonneg _).trans est)
  linarith only [prod,t2]

private theorem multiply_relative (u v D e : ℝ) (dp : 0≤D) (en : 0≤e) (eo : e≤1)
    (left : |u-1|≤D*e) (right : |v-1|≤D*e) : |u*v-1|≤(D^2+2*D)*e := by
  have id : u*v-1=(u-1)*(v-1)+(u-1)+(v-1) := by ring
  rw [id]
  apply (abs_add_le ..).trans
  apply (add_le_add_left (abs_add_le ((u-1)*(v-1)) (u-1)) _).trans
  rw [abs_mul]
  have prod := mul_le_mul left right (abs_nonneg _) (mul_nonneg dp en)
  have esq := mul_le_mul_of_nonneg_left eo (mul_nonneg (sq_nonneg D) en)
  nlinarith only [left,right,prod,esq]

private theorem same_prob {n ell : ℕ} {R : PrescribedRows n ell} {side : Bool}
    {E F : ℤ×ℤ→Prop} (i : DecidablePred E) (j : DecidablePred F) (h : E=F) :
    @prescribedProbability n ell R side E i = @prescribedProbability n ell R side F j := by
  subst F
  rw [Subsingleton.elim i j]

/-- For separated pairs in the ordinary prime-square-clean range, the two-field covariance
of the actual normalized smooth indicators agrees with the centered prime
coincidence product up to any fixed logarithmic-square rate. -/
theorem clean_pair_normalized_covariance (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks → y≠a →
    (Fixed.A b:ℝ) ≤ |(y:ℝ)-a| *(dyadicUnit b:ℝ)^50 →
    (∀ p∈R.hit a, ¬p^2∣((y:ℤ)-a).natAbs) → (∀ p∈T.hit a, ¬p^2∣((y:ℤ)-a).natAbs) →
    let γ := pairGamma (pairCorrectionPrimes b) (Fixed.rootBase n) a y
    |normalizedSmoothCovariance R T a y-(γ^2-1)|≤C*exp (-v*(Fixed.z b:ℝ)^2)*γ^2 := by
  obtain ⟨C,cp,b₁,joint⟩ := PrescribedRows.separated_joint_relative line v hv
  obtain ⟨b₂,gamma⟩ := PrescribedRows.pair_gamma_correction v hv
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  let D := 2*C+1
  have dp : 0<D := by dsimp only [D]; positivity
  refine ⟨D^2+2*D,by positivity,max b₁ (max b₂ b₃),?_⟩
  intro n ell a y R T b huge hn comp target absent am ym diff sep squareR squareT γ
  obtain ⟨large,lg⟩ := max_le_iff.mp huge
  obtain ⟨lg,ld⟩ := max_le_iff.mp lg
  have ac := ((constructed_marks_iff ..).mp am).2.1
  have yc := ((constructed_marks_iff ..).mp ym).2.1
  have yr := mark_range hn (deg b ld) yc
  let e := exp (-v*(Fixed.z b:ℝ)^2)
  have eo : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hv]) (sq_nonneg _))
  let J (S : PrescribedRows n ell) (s : Bool) :=
    prescribedProbability S s (fun k=>smoothMarkEvent S s a k ∧ smoothMarkEvent S s y k)
  let p (S : PrescribedRows n ell) (s : Bool) (i : ℕ) := prescribedProbability S s (smoothMarkEvent S s i)
  let m (S : PrescribedRows n ell) (s : Bool) := p S s y*p S s a
  have bound (S : PrescribedRows n ell) (s : Bool)
      (ss : ∀ p∈S.hit a, ¬p^2∣((y:ℤ)-a).natAbs) :
      0 < m S s ∧ |J S s/(γ*m S s)-1|≤D*e := by
    let c := coprimeFactor (S.secondStep a y s).natAbs/coprimeFactor (firstStep n ell y s).natAbs
    have g := gamma S lg target ac yc yr diff s
    change 1≤γ ∧ γ≤c ∧ c≤γ*(1+e) at g
    have h := joint S large hn comp target absent am ym diff sep s ss
    let E i (k : ℤ×ℤ) := supportedValue (sieveBand n ell (S.prefactor i s)) (S.intercept i s k.1 k.2)
    let P i := prescribedProbability S s (E i)
    let j := prescribedProbability S s (fun k=>E a k ∧ E y k)
    change 0<(c*P y)*P a ∧ |j/((c*P y)*P a)-1|≤C*e at h
    have eq₁ : j=J S s := same_prob _ _ rfl
    have eq₂ (i : ℕ) : P i=p S s i := same_prob _ _ rfl
    rw [eq₁,eq₂,eq₂,mul_assoc] at h
    exact relative_pair _ _ _ _ _ _ (zero_lt_one.trans_le g.1) h.1 g.2.1 g.2.2 eo h.2
  obtain ⟨rpos,r⟩ := bound R false squareR
  obtain ⟨tpos,t⟩ := bound T true squareT
  have model := multiply_relative _ _ D e dp.le (exp_pos _).le eo r t
  have gp : 0<γ := zero_lt_one.trans_le (gamma R lg target ac yc yr diff false).1
  let total := (p R false a*p T true a)*(p R false y*p T true y)
  have tm : total=m R false*m T true := by dsimp only [total,m]; ring
  have pos : 0<total := tm ▸ mul_pos rpos tpos
  have ident : normalizedSmoothCovariance R T a y-(γ^2-1) =
      (J R false/(γ*m R false)*(J T true/(γ*m T true))-1)*γ^2 := by
    change (J R false*J T true-total)/total-(γ^2-1)=_
    rw [tm]
    field_simp [gp.ne',rpos.ne',tpos.ne']
    ring
  rw [ident,abs_mul,abs_of_nonneg (sq_nonneg γ)]
  exact mul_le_mul_of_nonneg_right model (sq_nonneg γ)

/-- A single bound for the arithmetic covariance model over every mark pair. -/
theorem pair_gamma_square_upper (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ m a y, (pairGamma (pairCorrectionPrimes b) m a y)^2 ≤ exp (48*(Fixed.z b:ℝ)) := by
  classical
  obtain ⟨b₀,total⟩ := fixed_pair_weight_sum line
  refine ⟨b₀,?_⟩
  intro b large m a y
  let P := pairCorrectionPrimes b
  have primes (p : ℕ) (hp : p∈P) : p.Prime ∧ Fixed.d b < p ∧ p ≤ Fixed.B b := by
    obtain ⟨pp,low,high⟩ := mem_pairCorrectionPrimes.mp hp
    exact ⟨pp,low,high.trans (Nat.pow_le_pow_right (by decide) (by change 200*Fixed.h b≤1000*Fixed.h b; omega))⟩
  rw [pair_gamma_square _ (fun p hp => (primes p hp).1)]
  refine le_trans (sum_le_sum ?_) (total b large P primes)
  intro T h
  split
  · exact le_rfl
  · apply prod_nonneg
    intro p hp
    have pm := (primes p (mem_powerset.mp h hp)).1
    have pp : 1≤(p:ℝ) := by exact_mod_cast pm.one_le
    exact div_nonneg (by linarith) (sq_nonneg _)

/-- The smooth-indicator covariance has a uniform absolute error across all
separated pairs avoiding the prescribed ordinary prime squares. -/
theorem clean_pair_covariance_absolute (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks → y≠a →
    (Fixed.A b:ℝ) ≤ |(y:ℝ)-a| *(dyadicUnit b:ℝ)^50 →
    (∀ p∈R.hit a, ¬p^2∣((y:ℤ)-a).natAbs) → (∀ p∈T.hit a, ¬p^2∣((y:ℤ)-a).natAbs) →
    let γ := pairGamma (pairCorrectionPrimes b) (Fixed.rootBase n) a y
    |normalizedSmoothCovariance R T a y-(γ^2-1)|≤C*exp (-v*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,b₁,cov⟩ := clean_pair_normalized_covariance line (v+48) (by linarith)
  obtain ⟨b₂,model⟩ := pair_gamma_square_upper line
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell a y R T b huge hn comp target absent am ym diff sep squareR squareT γ
  obtain ⟨large,lg⟩ := max_le_iff.mp huge
  have estimate := cov R T large hn comp target absent am ym diff sep squareR squareT
  have cap := model b lg (Fixed.rootBase n) a y
  have z : 1≤(Fixed.z b:ℝ) := by exact_mod_cast (Nat.le_add_left 1 b.log2)
  apply estimate.trans
  apply (mul_le_mul_of_nonneg_left cap (mul_nonneg cp.le (exp_pos _).le)).trans
  rw [mul_assoc,←exp_add]
  apply mul_le_mul_of_nonneg_left _ cp.le
  apply exp_le_exp.mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr z) (zero_le_one.trans z)]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.clean_pair_normalized_covariance

#print axioms Cogentic.Construction.clean_pair_covariance_absolute
