import Cogentic.NearSmoothUpper
import Cogentic.NearPairVariance

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- The smooth event at one eligible mark under one field's coefficient law. -/
def smoothMarkEvent {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (a : ℕ) (k : ℤ × ℤ) : Prop :=
  supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2)

/-- The actual single-mark occurrence probability for the two independent fields. -/
def smoothMarkProbability {n ell : ℕ} (R T : PrescribedRows n ell) (a : ℕ) : ℝ :=
  prescribedProbability R false (smoothMarkEvent R false a) *
    prescribedProbability T true (smoothMarkEvent T true a)

/-- Covariance of the two-field smooth indicators divided by each mark's own
occurrence probability, as in the squared normalized mark score. -/
def normalizedSmoothCovariance {n ell : ℕ} (R T : PrescribedRows n ell) (a y : ℕ) : ℝ :=
  twoFieldIndicatorCovariance R T (smoothMarkEvent R false) (smoothMarkEvent T true) a y /
    (smoothMarkProbability R T a * smoothMarkProbability R T y)

private theorem prob_eq {n ell : ℕ} {R : PrescribedRows n ell} {side : Bool}
    {E F : ℤ×ℤ→Prop} (d : DecidablePred E) (e : DecidablePred F) (h : E=F) :
    @prescribedProbability n ell R side E d = @prescribedProbability n ell R side F e := by
  subst F
  rw [Subsingleton.elim d e]

theorem normalized_smooth_covariance_off_diagonal (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks → y≠a →
    |normalizedSmoothCovariance R T a y| ≤ (dyadicUnit b:ℝ)^32 := by
  obtain ⟨b₀,joints⟩ := PrescribedRows.joint_smooth_upper line
  refine ⟨b₀,?_⟩
  intro n ell a y R T b large hn comp target absent first second diff
  let X : ℝ := dyadicUnit b
  let E := smoothMarkEvent R false
  let F := smoothMarkEvent T true
  let l := fun i => prescribedProbability R false (E i)
  let r := fun i => prescribedProbability T true (F i)
  let j := prescribedProbability R false (fun k => E a k ∧ E y k)
  let k := prescribedProbability T true (fun k => F a k ∧ F y k)
  let m := (l a*r a)*(l y*r y)
  have l0 (i) : 0≤l i := (R.probability_unit target false (E i)).1
  have r0 (i) : 0≤r i := (T.probability_unit target true (F i)).1
  have jp : 0≤j := (R.probability_unit target false (fun k=>E a k ∧ E y k)).1
  have kp : 0≤k := (T.probability_unit target true (fun k=>F a k ∧ F y k)).1
  have estimate (S : PrescribedRows n ell) (side : Bool) :
      let A := smoothMarkEvent S side
      prescribedProbability S side (fun k=>A a k ∧ A y k) ≤
        X^16*(prescribedProbability S side (A a)*prescribedProbability S side (A y)) := by
    have est := joints S large hn comp target absent first second diff side
    dsimp only at est ⊢
    exact (congrArg₂ (·≤·) (prob_eq _ _ rfl)
      (congrArg (X^16 * ·) (congrArg₂ (·*·) (prob_eq _ _ rfl) (prob_eq _ _ rfl)))).mpr est
  have lb : j ≤ X^16*(l a*l y) := estimate R false
  have rb : k ≤ X^16*(r a*r y) := estimate T true
  have m0 : 0 ≤ m := mul_nonneg (mul_nonneg (l0 a) (r0 a)) (mul_nonneg (l0 y) (r0 y))
  have big : 1≤X^32 := one_le_pow₀ (by dsimp only [X,dyadicUnit]; exact_mod_cast (Nat.one_le_two_pow : 1≤2^Fixed.h b))
  have bounds : j*k ≤ X^32*m := by
    apply (mul_le_mul lb rb kp (mul_nonneg (by positivity) (mul_nonneg (l0 a) (l0 y)))).trans_eq
    dsimp only [m]; ring
  change |(j*k-m)/m|≤X^32
  by_cases zero : m=0
  · simp [zero,le_trans zero_le_one big]
  rw [abs_div,abs_of_nonneg m0]
  apply (div_le_iff₀ (lt_of_le_of_ne m0 (Ne.symm zero))).mpr
  apply abs_le.mpr
  constructor
  · linarith only [le_mul_of_one_le_left m0 big,mul_nonneg jp kp]
  · linarith only [bounds,m0]

/-- Full distinct near-pair contribution to a product of normalized cell scores.
The covariance is divided by the product of the two marks' actual smooth occurrence
probabilities. Both residue densities are removed, and the two weight functions
can have either sign. The radius is the one used by the distant-mark estimate. -/
theorem cell_near_normalized_smooth_covariance (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell cell' : Option (Bool × Fin (Fixed.d b))) (q s u v : ℕ),
    0<q → 0<s → q≤(Fixed.B b)^3 → s≤(Fixed.B b)^3 →
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ u [MOD q])
    let Y := (constructorCellMarks n ell cell').filter (fun y=>y ≡ v [MOD s])
    ∀ (w w' : ℕ→ℝ) (D D' : ℝ), 0≤D → 0≤D' →
    (∀ a∈X,|w a|≤D) → (∀ y∈Y,|w' y|≤D') →
    ((q:ℝ)*s)*|∑ a∈X, ∑ y∈Y.filter (fun y=>y≠a ∧ a.dist y≤nearRadius b),
      w a*w' y*normalizedSmoothCovariance R T a y| / (cellMarkCount b:ℝ)^2 ≤
        8*(D*D')/(dyadicUnit b:ℝ)^15 := by
  obtain ⟨b₀,pointwise⟩ := normalized_smooth_covariance_off_diagonal line
  refine ⟨b₀,?_⟩
  intro n ell R T b large hn comp target absent cell cell' q s u v qp sp qr sr X Y w w' D D' dp dp' wx wy
  let z : ℝ := dyadicUnit b
  have zp : 0<z := by dsimp [z,dyadicUnit]; positivity
  let f := fun a y => w a*w' y*normalizedSmoothCovariance R T a y
  let mask := fun a y => if y≠a then f a y else 0
  have bound (a : ℕ) (ha : a∈X) (y : ℕ) (hy : y∈Y) (_ : a.dist y≤nearRadius b) :
      |mask a y|≤(D*D')*z^32 := by
    have first := (mem_filter.mp (mem_filter.mp ha).1).2
    have second := (mem_filter.mp (mem_filter.mp hy).1).2
    by_cases diff : y≠a
    · dsimp only [mask,f]; rw [if_pos diff,abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (wx a ha) (wy y hy) (abs_nonneg _) dp)
        (pointwise R T large hn comp target absent first second diff) (abs_nonneg _) (mul_nonneg dp dp')
    · dsimp only [mask]; rw [if_neg diff,abs_zero]; positivity
  have est := near_pair_cell_sum b cell X Y q s u v qp sp qr sr
    (fun a ha => ⟨(mem_filter.mp (mem_filter.mp ha).1).1,(mem_filter.mp ha).2⟩)
    (fun _ hy => (mem_filter.mp hy).2) mask ((D*D')*z^32) (by positivity) bound
  have row (a : ℕ) : ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b),mask a y =
      ∑ y∈Y.filter (fun y=>y≠a ∧ a.dist y≤nearRadius b),f a y := by
    simp only [mask,Finset.sum_filter]
    apply sum_congr rfl
    intro y _
    by_cases hd : y=a <;> by_cases hc : a.dist y≤nearRadius b <;> simp [hd,hc]
  simp_rw [row] at est
  apply est.trans_eq
  change 8*((D*D')*z^32)/z^47=8*(D*D')/z^15
  field_simp


private theorem normalized_diagonal (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks →
    |normalizedSmoothCovariance R T a a| ≤ (Fixed.B b:ℝ)^2 := by
  obtain ⟨b₀,floor⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨b₀,?_⟩
  intro n ell a R T b large hn comp target absent mark
  let B : ℝ := Fixed.B b
  let p := smoothMarkProbability R T a
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have floor' (S : PrescribedRows n ell) (side : Bool) :
      1/B ≤ prescribedProbability S side (smoothMarkEvent S side a) := by
    apply (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤8) bp.le).trans
    exact (floor S large hn comp target absent mark side).trans_eq (prob_eq _ _ rfl)
  have fp : (1/B)*(1/B)≤p := mul_le_mul (floor' R false) (floor' T true)
    (by positivity) (R.probability_unit target false _).1
  have pp : 0<p := (show 0<(1/B)*(1/B) by positivity).trans_le fp
  have pu : p≤1 := (mul_le_mul (R.probability_unit target false _).2 (T.probability_unit target true _).2
    (T.probability_unit target true _).1 zero_le_one).trans_eq (one_mul _)
  have id (S : PrescribedRows n ell) (side : Bool) (E : ℤ×ℤ→Prop) :
      prescribedProbability S side (fun k=>E k ∧ E k)=prescribedProbability S side E :=
    prob_eq _ _ (by funext k; simp)
  have eq : normalizedSmoothCovariance R T a a = (p-p*p)/(p*p) := by
    dsimp only [normalizedSmoothCovariance,twoFieldIndicatorCovariance,p,smoothMarkProbability]
    rw [id,id]
  have pm : 1≤B^2*p := by
    have eqB : B^2*(1/B*(1/B))=1 := by field_simp
    exact eqB ▸ (mul_le_mul_of_nonneg_left fp (sq_nonneg B))
  rw [eq,abs_of_nonneg (div_nonneg (sub_nonneg.mpr ((mul_le_mul_of_nonneg_left pu pp.le).trans_eq (mul_one _)))
    (mul_nonneg pp.le pp.le))]
  apply (div_le_iff₀ (mul_pos pp pp)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right pm pp.le,mul_nonneg pp.le pp.le]

/-- The diagonal contribution after both reciprocal class densities and the two
actual single-mark occurrence probabilities have been divided out. -/
theorem cell_diagonal_normalized_smooth_covariance (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (X Y : Finset ℕ) (q s : ℕ), q≤(Fixed.B b)^3 → s≤(Fixed.B b)^3 →
    X.card≤cellMarkCount b → (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    ∀ (w w' : ℕ→ℝ) (D D' : ℝ), 0≤D → 0≤D' →
    (∀ a∈X,|w a|≤D) → (∀ y∈Y,|w' y|≤D') →
    ((q:ℝ)*s)*|∑ a∈X, if a∈Y then w a*w' a*normalizedSmoothCovariance R T a a else 0| /
      (cellMarkCount b:ℝ)^2 ≤ (D*D')/(dyadicUnit b:ℝ)^1997 := by
  obtain ⟨b₀,diag⟩ := normalized_diagonal line
  refine ⟨b₀,?_⟩
  intro n ell R T b large hn comp target absent X Y q s qr sr count marks w w' D D' dp dp' wx wy
  let M : ℝ := cellMarkCount b
  let B : ℝ := Fixed.B b
  let z : ℝ := dyadicUnit b
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  have zp : 0<z := by dsimp [z,dyadicUnit]; positivity
  have schedule : B^8*z^1997=M := by
    dsimp only [B,z,M,Fixed.B,Fixed.beta,cellMarkCount,dyadicUnit]
    push_cast
    rw [←pow_mul,←pow_mul,←pow_add]; congr 1; omega
  have qs : (q:ℝ)*s≤B^6 :=
    (mul_le_mul (show (q:ℝ)≤B^3 by dsimp only [B]; exact_mod_cast qr)
      (show (s:ℝ)≤B^3 by dsimp only [B]; exact_mod_cast sr) (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have mcount : (X.card:ℝ)≤M := by dsimp only [M]; exact_mod_cast count
  let f := fun a => if a∈Y then w a*w' a*normalizedSmoothCovariance R T a a else 0
  have point (a : ℕ) (ha : a∈X) : |f a|≤(D*D')*B^2 := by
    dsimp only [f]; split_ifs with hy
    · rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (wx a ha) (wy a hy) (abs_nonneg _) dp)
        (diag R T large hn comp target absent (marks a ha)) (abs_nonneg _) (mul_nonneg dp dp')
    · rw [abs_zero]; positivity
  have h := (abs_sum_le_sum_abs ..).trans (sum_le_sum point)
  rw [sum_const,nsmul_eq_mul] at h
  have agg := h.trans (mul_le_mul_of_nonneg_right mcount (show 0≤(D*D')*B^2 by positivity))
  have bound := mul_le_mul qs agg (abs_nonneg _) (show 0≤B^6 by positivity)
  change ((q:ℝ)*s)*|∑ a∈X,f a|/M^2≤(D*D')/z^1997
  apply (div_le_div_iff₀ (sq_pos_of_pos mp) (pow_pos zp _)).mpr
  apply (mul_le_mul_of_nonneg_right bound (pow_nonneg zp.le _)).trans_eq
  rw [show B^6*(M*((D*D')*B^2))*z^1997 = (D*D')*M*(B^8*z^1997) by ring,schedule]; ring

/-- All near pairs, including the diagonal, in the product of the two normalized
smooth scores. The cells, residue classes and bounded signed weights may differ. -/
theorem cell_all_near_normalized_smooth_covariance (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell cell' : Option (Bool × Fin (Fixed.d b))) (q s u v : ℕ),
    0<q → 0<s → q≤(Fixed.B b)^3 → s≤(Fixed.B b)^3 →
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ u [MOD q])
    let Y := (constructorCellMarks n ell cell').filter (fun y=>y ≡ v [MOD s])
    ∀ (w w' : ℕ→ℝ) (D D' : ℝ), 0≤D → 0≤D' →
    (∀ a∈X,|w a|≤D) → (∀ y∈Y,|w' y|≤D') →
    ((q:ℝ)*s)*|∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b),
      w a*w' y*normalizedSmoothCovariance R T a y| / (cellMarkCount b:ℝ)^2 ≤
        9*(D*D')/(dyadicUnit b:ℝ)^15 := by
  obtain ⟨b₁,off⟩ := cell_near_normalized_smooth_covariance line
  obtain ⟨b₂,diag⟩ := cell_diagonal_normalized_smooth_covariance line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell R T b large hn comp target absent cell cell' q s u v qp sp qr sr X Y w w' D D' dp dp' wx wy
  let f := fun a y => w a*w' y*normalizedSmoothCovariance R T a y
  have count : X.card≤cellMarkCount b := by
    apply (card_le_card (filter_subset ..)).trans
    apply (card_le_card (filter_subset ..)).trans
    simp [Nat.card_Ico,b]
  have first := off R T (max_le_iff.mp large).1 hn comp target absent cell cell' q s u v qp sp qr sr w w' D D' dp dp' wx wy
  have second := diag R T (max_le_iff.mp large).2 hn comp target absent X Y q s qr sr count
    (fun a ha => (mem_filter.mp (mem_filter.mp ha).1).2) w w' D D' dp dp' wx wy
  have row (a : ℕ) : ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b), f a y =
      (∑ y∈Y.filter (fun y=>y≠a ∧ a.dist y≤nearRadius b), f a y) +
        (if a∈Y then f a a else 0) := by
    conv_lhs => rw [Finset.sum_filter]
    conv_rhs => lhs; rw [Finset.sum_filter]
    rw [←Finset.sum_ite_eq' Y a (f a),←sum_add_distrib]
    apply sum_congr rfl
    intro y _
    by_cases h : y=a
    · subst y; simp
    · by_cases near : a.dist y≤nearRadius b <;> simp [near,h]
  change ((q:ℝ)*s)*|∑ a∈X, ∑ y∈Y.filter (fun y=>a.dist y≤nearRadius b), f a y|/_≤_
  simp_rw [row,sum_add_distrib]
  let z : ℝ := dyadicUnit b
  have zp : 1≤z := by dsimp only [z,dyadicUnit]; exact_mod_cast (Nat.one_le_two_pow : 1≤2^Fixed.h b)
  have small : (D*D')/z^1997≤(D*D')/z^15 :=
    div_le_div_of_nonneg_left (mul_nonneg dp dp') (pow_pos (lt_of_lt_of_le zero_lt_one zp) _)
      (pow_le_pow_right₀ zp (by decide))
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_add_le ..) (by positivity)) (sq_nonneg _)).trans
  rw [mul_add,add_div]
  exact ((add_le_add first (second.trans small)).trans_eq (by ring))

end
end Cogentic.Construction

#print axioms Cogentic.Construction.cell_all_near_normalized_smooth_covariance
