import Cogentic.FarPairCovariance
import Cogentic.SquareDivisorPairs

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

private theorem class_count {b q r lo : ℕ} (X : Finset ℕ) (qp : 0<q) (qr : q≤(Fixed.B b)^3)
    (here : ∀ a∈X, a∈Ico lo (lo+cellMarkCount b) ∧ a ≡ r [MOD q]) :
    (X.card:ℝ) ≤ 2*(cellMarkCount b:ℝ)/q := by
  let M := cellMarkCount b
  have sub : X⊆(Ico lo (lo+M)).filter (fun a => a ≡ r [MOD q]) := fun a ha=>mem_filter.mpr (here a ha)
  have cap := (abs_le.mp (interval_residue_error (Nat.le_add_right lo M) qp r)).2
  simp only [Nat.cast_add,add_sub_cancel_left] at cap
  have small : q≤M := qr.trans (by
    change (2^(1000*Fixed.h b))^3≤2^(9997*Fixed.h b)
    rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
  have qR : (0:ℝ)<q := by exact_mod_cast qp
  have unit : 1≤(M:ℝ)/q := (one_le_div qR).mpr (by exact_mod_cast small)
  have cnt : (X.card:ℝ)≤((Ico lo (lo+M)).filter (fun a => a ≡ r [MOD q])).card := by exact_mod_cast card_le_card sub
  change (X.card:ℝ) ≤ 2*(M:ℝ)/q
  rw [mul_div_assoc]
  linarith only [cnt,cap,unit]

/-- Union bound for all prescribed prime-square coincidences on a single
row of a residue-class pair sum. The prime set may depend on the row. -/
theorem cell_square_exception_count {b s v lo : ℕ} (Y P : Finset ℕ) (sq : Squarefree s)
    (sr : s≤(Fixed.B b)^3)
    (here : ∀ y∈Y, y∈Ico lo (lo+cellMarkCount b) ∧ y ≡ v [MOD s])
    (band : P ⊆ primeBand b) (a : ℕ) :
    ((Y.filter (fun y=>∃ p∈P, y ≡ a [MOD p^2])).card:ℝ) ≤
      (P.card:ℝ)*((cellMarkCount b:ℝ)/s)*(2/(dyadicUnit b:ℝ)^500) := by
  let A (p : ℕ) := (Ico lo (lo+cellMarkCount b)).filter (fun y=>y ≡ v [MOD s] ∧ y ≡ a [MOD p^2])
  have sub : Y.filter (fun y=>∃ p∈P, y ≡ a [MOD p^2]) ⊆ P.biUnion A := by
    intro y hy
    obtain ⟨hy,p,hp,hit⟩ := mem_filter.mp hy
    exact mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨(here y hy).1,(here y hy).2,hit⟩⟩
  have count := (card_le_card sub).trans card_biUnion_le
  have card : (((Y.filter (fun y=>∃ p∈P, y ≡ a [MOD p^2])).card):ℝ)≤∑ p∈P,((A p).card:ℝ) := by exact_mod_cast count
  apply card.trans
  have eq : (dyadicUnit b:ℝ)^500=(2:ℝ)^(500*Fixed.h b) := by
    simp only [dyadicUnit,Nat.cast_pow,Nat.cast_ofNat,←pow_mul,Nat.mul_comm]
  rw [eq]
  have le := sum_le_sum (fun p hp=>fixed_square_prime_loss (band hp) sq sr lo a v)
  simp only [sum_const,nsmul_eq_mul] at le
  exact le.trans_eq (by ring)

private theorem cell_model_size (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ m a y,
      |(pairGamma (pairCorrectionPrimes b) m a y)^2-1|≤(dyadicUnit b:ℝ) := by
  obtain ⟨b₁,cap⟩ := pair_gamma_square_upper line
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 96
  refine ⟨max b₁ b₂,?_⟩
  intro b huge m a y
  obtain ⟨c,d⟩ := max_le_iff.mp huge
  have lower : 1≤(dyadicUnit b:ℝ) := by exact_mod_cast (Nat.one_le_two_pow : 1≤2^Fixed.h b)
  have logX : log (dyadicUnit b:ℝ) = (Fixed.h b:ℝ)*log 2 := by simp only [dyadicUnit,Nat.cast_pow,Nat.cast_ofNat,log_pow]
  have big : (96:ℝ)≤Fixed.d b := by exact_mod_cast deg b d
  have mag : 48≤(Fixed.d b:ℝ)*log 2 := by
    have lowerLog : (1/2:ℝ)≤log 2 := by linarith [log_two_gt_d9]
    nlinarith only [mul_le_mul big lowerLog (by norm_num : (0:ℝ)≤1/2) (Nat.cast_nonneg (α:=ℝ) (Fixed.d b))]
  have expBound : exp (48*(Fixed.z b:ℝ))≤dyadicUnit b := by
    rw [←exp_log (zero_lt_one.trans_le lower),exp_le_exp,logX]
    simpa only [Fixed.h,Nat.cast_mul,mul_right_comm] using mul_le_mul_of_nonneg_right mag (Nat.cast_nonneg (α:=ℝ) (Fixed.z b))
  have high := (cap b c m a y).trans expBound
  exact abs_le.mpr ⟨by linarith only [sq_nonneg (pairGamma (pairCorrectionPrimes b) m a y),lower],by linarith only [high]⟩

/-- Weighted covariance and the centered arithmetic model over the full two
cells. The only analytic premise concerns separated square-clean pairs. -/
theorem cell_pair_variance_transfer (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell cell' : Option (Bool × Fin (Fixed.d b))) (q s u v : ℕ),
    Squarefree q → Squarefree s → q≤(Fixed.B b)^3 → s≤(Fixed.B b)^3 →
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ u [MOD q])
    let Y := (constructorCellMarks n ell cell').filter (fun y=>y ≡ v [MOD s])
    let model := fun a y=> (pairGamma (pairCorrectionPrimes b) (Fixed.rootBase n) a y)^2-1
    ∀ (P : ℕ→Finset ℕ) (L : ℕ) (ε : ℝ), 0≤ε →
    (∀ a∈X, P a⊆primeBand b ∧ (P a).card≤L) →
    (∀ a∈X, ∀ y∈Y, nearRadius b < a.dist y → (∀ p∈P a, ¬y ≡ a [MOD p^2]) →
      |normalizedSmoothCovariance R T a y-model a y|≤ε) →
    ∀ (w w' : ℕ→ℝ) (D D' : ℝ), 0≤D → 0≤D' → (∀ a∈X,|w a|≤D) → (∀ y∈Y,|w' y|≤D') →
    ((q:ℝ)*s)*|∑ a∈X,∑ y∈Y,w a*w' y*(normalizedSmoothCovariance R T a y-model a y)|/(cellMarkCount b:ℝ)^2 ≤
      D*D'*((17+8*(L:ℝ))/(dyadicUnit b:ℝ)^15 + 4*ε) := by
  obtain ⟨b₁,near⟩ := cell_all_near_normalized_smooth_covariance line
  obtain ⟨b₂,rough⟩ := normalized_smooth_covariance_off_diagonal line
  obtain ⟨b₃,modelBound⟩ := cell_model_size line
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell R T b huge hn comp target absent cell cell' q s u v qsf ssf qr sr X Y model P L ε ep prime far w w' D D' dp dp' wx wy
  obtain ⟨lg,hg⟩ := max_le_iff.mp huge
  obtain ⟨lg2,lg3⟩ := max_le_iff.mp hg
  let M : ℝ := cellMarkCount b
  let Z : ℝ := dyadicUnit b
  let H := D*D'
  let W (a y : ℕ) := w a*w' y
  let C (a y : ℕ) := normalizedSmoothCovariance R T a y
  let F (a y : ℕ) := W a y*(C a y-model a y)
  let N (a y : ℕ) := a.dist y≤nearRadius b
  let B (a y : ℕ) := ∃ p∈P a, y ≡ a [MOD p^2]
  let S := (q:ℝ)*s/M^2
  have sn : 0≤S := by dsimp [S]; positivity
  have zp : 1≤Z := by dsimp only [Z,dyadicUnit]; exact_mod_cast (Nat.one_le_two_pow : 1≤2^Fixed.h b)
  have zn : 0<Z := zero_lt_one.trans_le zp
  have qspos := Nat.pos_of_ne_zero qsf.ne_zero
  have sspos := Nat.pos_of_ne_zero ssf.ne_zero
  have qp : (0:ℝ)<q := by exact_mod_cast qspos
  have sp : (0:ℝ)<s := by exact_mod_cast sspos
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have hp : 0≤H := mul_nonneg dp dp'
  have weight (a) (ha:a∈X) (y) (hy:y∈Y) : |W a y|≤H := by
    dsimp only [W,H]; rw [abs_mul]; exact mul_le_mul (wx a ha) (wy y hy) (abs_nonneg _) dp
  have insideX (a) (ha:a∈X) := And.intro (mem_filter.mp (mem_filter.mp ha).1).1 (mem_filter.mp ha).2
  have insideY (y) (hy:y∈Y) := And.intro (mem_filter.mp (mem_filter.mp hy).1).1 (mem_filter.mp hy).2
  have countX := class_count X qspos qr insideX
  have countY := class_count Y sspos sr insideY
  have mdl (a y) : |model a y|≤Z := modelBound b lg3 _ _ _
  have modelNear := near_pair_cell_sum b cell X Y q s u v qspos sspos qr sr insideX (fun y hy=>(insideY y hy).2)
    (fun a y=>W a y*model a y) (H*Z) (mul_nonneg hp zn.le) (fun a ha y hy _=> by
      rw [abs_mul]; exact mul_le_mul (weight a ha y hy) (mdl a y) (abs_nonneg _) hp)
  have actualNear := near R T lg hn comp target absent cell cell' q s u v qspos sspos qr sr w w' D D' dp dp' wx wy
  let nearA := ∑ a∈X,∑ y∈Y.filter (N a),W a y*C a y
  let nearM := ∑ a∈X,∑ y∈Y.filter (N a),W a y*model a y
  have norm (x : ℝ) : ((q:ℝ)*s)*|x|/M^2=S*|x| := by dsimp [S]; ring
  change ((q:ℝ)*s)*|nearA|/M^2≤9*H/Z^15 at actualNear
  change ((q:ℝ)*s)*|nearM|/M^2≤8*(H*Z)/Z^47 at modelNear
  rw [norm] at actualNear modelNear
  have nearSmall : S*|nearA-nearM|≤17*H/Z^15 := by
    have rr : 8*(H*Z)/Z^47=8*H/Z^46 := by field_simp
    have cmp : 8*H/Z^46≤8*H/Z^15 := div_le_div_of_nonneg_left (by positivity) (pow_pos zn _) (pow_le_pow_right₀ zp (by decide))
    have tri := mul_le_mul_of_nonneg_left (abs_sub nearA nearM) sn
    rw [mul_add] at tri
    exact tri.trans ((add_le_add actualNear (modelNear.trans (rr.le.trans cmp))).trans_eq (by ring))
  let farSum := ∑ a∈X,∑ y∈Y.filter (fun y=>¬N a y), F a y
  let loss := H*(2*Z^32)
  let per := (2*M/s)*(H*ε)+((L:ℝ)*(M/s)*(2/Z^500))*loss
  have lp : 0≤loss := by dsimp only [loss]; positivity
  have row (a : ℕ) (ha : a∈X) : |∑ y∈Y.filter (fun y=>¬N a y), F a y|≤per := by
    let V := Y.filter (fun y=>¬N a y)
    have point (y) (hy : y∈V) : |F a y|≤H*ε+(if B a y then loss else 0) := by
      obtain ⟨hy,nd⟩ := mem_filter.mp hy
      have dist : nearRadius b < a.dist y := lt_of_not_ge nd
      have wt := weight a ha y hy
      dsimp only [F]; rw [abs_mul]
      by_cases bad : B a y
      · rw [if_pos bad]
        have diff : y≠a := by intro eq; subst y; simp at dist
        have big := rough R T lg2 hn comp target absent (mem_filter.mp (mem_filter.mp ha).1).2 (mem_filter.mp (mem_filter.mp hy).1).2 diff
        change |C a y|≤Z^32 at big
        have un : Z≤Z^32 := le_self_pow₀ zp (by decide)
        have val := (abs_sub (C a y) (model a y)).trans (add_le_add big ((mdl a y).trans un))
        have final := mul_le_mul wt val (abs_nonneg _) hp
        dsimp only [loss]
        linarith only [final,mul_nonneg hp ep]
      · rw [if_neg bad,add_zero]
        exact mul_le_mul wt (far a ha y hy dist (fun p hp eq=>bad ⟨p,hp,eq⟩)) (abs_nonneg _) hp
    have sum := (abs_sum_le_sum_abs ..).trans (sum_le_sum point)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at sum
    rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul] at sum
    have vb : V.filter (B a) ⊆ Y.filter (B a) := filter_subset_filter _ (filter_subset ..)
    have cc := cell_square_exception_count Y (P a) ssf sr insideY (prime a ha).1 a
    have ps : ((P a).card:ℝ)≤L := by exact_mod_cast (prime a ha).2
    have ccb := (Nat.cast_le.mpr (card_le_card vb) : (((V.filter (B a)).card):ℝ)≤(Y.filter (B a)).card).trans cc
    change _ ≤ ((P a).card:ℝ)*(M/s)*(2/Z^500) at ccb
    have cb := ccb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ps (by positivity)) (by positivity))
    have cv : (V.card:ℝ) ≤ 2*M/s := (Nat.cast_le.mpr (card_le_card (filter_subset ..))).trans countY
    exact sum.trans (add_le_add (mul_le_mul_of_nonneg_right cv (mul_nonneg hp ep)) (mul_le_mul_of_nonneg_right cb lp))
  have allRows := (abs_sum_le_sum_abs ..).trans (sum_le_sum row)
  simp only [sum_const,nsmul_eq_mul] at allRows
  have perpos : 0≤per := by dsimp only [per]; positivity
  have farSmall : S*|farSum|≤4*H*ε+8*(L:ℝ)*H/Z^15 := by
    have fx := mul_le_mul_of_nonneg_left (allRows.trans (mul_le_mul_of_nonneg_right countX perpos)) sn
    change S*|farSum|≤S*(2*M/q*per) at fx
    have id : S*(2*M/q*per)=4*H*ε+8*(L:ℝ)*H/Z^468 := by
      dsimp only [S,per,loss]; field_simp; ring
    have cmp : 8*(L:ℝ)*H/Z^468≤8*(L:ℝ)*H/Z^15 := div_le_div_of_nonneg_left (by positivity)
      (pow_pos zn _) (pow_le_pow_right₀ zp (by decide))
    exact fx.trans (id.le.trans (add_le_add_right cmp _))
  have halves : (∑ a∈X,∑ y∈Y,F a y) = nearA-nearM+farSum := by
    dsimp only [nearA,nearM,farSum]
    rw [←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [←Finset.sum_filter_add_sum_filter_not Y (N a) (F a),←sum_sub_distrib]
    congr 1
    exact sum_congr rfl (fun y _=>by dsimp only [F]; ring)
  change ((q:ℝ)*s)*|∑ a∈X,∑ y∈Y,F a y|/M^2 ≤ _
  rw [norm,halves]
  apply (mul_le_mul_of_nonneg_left (abs_add_le ..) sn).trans
  rw [mul_add]
  exact (add_le_add nearSmall farSmall).trans_eq (by dsimp only [H,Z]; ring)

private theorem unit_error_saving (K : ℝ) (hK : 1≤K) :
    ∃ b₀ : ℕ, ∀ b≥b₀, 1/(dyadicUnit b:ℝ)^15 ≤ exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨b₀,save⟩ := fixed_band_power_savings (85*K) (by linarith only [hK])
  refine ⟨b₀,?_⟩
  intro b large
  let h : ℝ := Fixed.h b; let z : ℝ := Fixed.z b
  have bp : (0:ℝ)<Fixed.B b := by dsimp [Fixed.B]; positivity
  have hp : 0≤h := Nat.cast_nonneg _
  have logB : log (Fixed.B b:ℝ)=1000*h*log 2 := by simp [Fixed.B,Fixed.beta,h]
  have Xp : 0<(dyadicUnit b:ℝ) := by dsimp [dyadicUnit]; positivity
  have logX : log (dyadicUnit b:ℝ)=h*log 2 := by simp [dyadicUnit,h]
  have raw := save b large
  rw [Real.rpow_def_of_pos bp,exp_le_exp,logB] at raw
  change 1000*h*log 2*(-17/200)≤-(85*K)*z^2 at raw
  rw [one_div,←exp_log Xp,←exp_nat_mul,←exp_neg,logX,exp_le_exp]
  change -((15:ℝ)*(h*log 2)) ≤ -K*z^2
  linarith only [raw,mul_nonneg hp (log_nonneg (by norm_num : (1:ℝ)≤2))]

/-- Under the two independent prescribed coefficient laws, the full weighted
covariance on arbitrary residue classes of two cells has the same centered
prime-product model to any prescribed logarithmic-square accuracy. -/
theorem cell_pair_covariance_approximation (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell cell' : Option (Bool × Fin (Fixed.d b))) (q s u v : ℕ),
    Squarefree q → Squarefree s → q≤(Fixed.B b)^3 → s≤(Fixed.B b)^3 →
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ u [MOD q])
    let Y := (constructorCellMarks n ell cell').filter (fun y=>y ≡ v [MOD s])
    let model := fun a y=> (pairGamma (pairCorrectionPrimes b) (Fixed.rootBase n) a y)^2-1
    ∀ (w w' : ℕ→ℝ) (D D' : ℝ), 0≤D → 0≤D' → (∀ a∈X,|w a|≤D) → (∀ y∈Y,|w' y|≤D') →
    ((q:ℝ)*s)*|∑ a∈X,∑ y∈Y,w a*w' y*(normalizedSmoothCovariance R T a y-model a y)|/(cellMarkCount b:ℝ)^2 ≤
      (D*D')*(C*exp (-K*(Fixed.z b:ℝ)^2)) := by
  obtain ⟨C,cp,b₁,pair⟩ := clean_pair_covariance_absolute line K hK
  obtain ⟨b₂,cells⟩ := cell_pair_variance_transfer line
  obtain ⟨b₃,save⟩ := unit_error_saving K hK
  refine ⟨49+4*C,by positivity,max b₁ (max b₂ b₃),?_⟩
  intro n ell R T b large hn comp target absent cell cell' q s u v qsf ssf qr sr X Y model w w' D D' dp dp' wx wy
  obtain ⟨lp,other⟩ := max_le_iff.mp large
  obtain ⟨lc,ls⟩ := max_le_iff.mp other
  let P (a : ℕ) := R.hit a ∪ T.hit a
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  have primes (a : ℕ) (_ : a∈X) : P a ⊆ primeBand b ∧ (P a).card≤4 := by
    have sub (S : PrescribedRows n ell) : S.hit a⊆S.primes := filter_subset ..
    have band (S : PrescribedRows n ell) : S.hit a⊆primeBand b :=
      fun _ hp=>(mem_filter.mp (S.member (sub S hp))).1
    have size (S : PrescribedRows n ell) : (S.hit a).card≤2 := (card_le_card (sub S)).trans S.limit
    exact ⟨union_subset (band R) (band T),(card_union_le ..).trans (by linarith only [size R,size T])⟩
  have good (a : ℕ) (ha : a∈X) (y : ℕ) (hy : y∈Y) (far : nearRadius b < a.dist y)
      (clean : ∀ p∈P a, ¬ y ≡ a [MOD p^2]) : |normalizedSmoothCovariance R T a y-model a y|≤C*e := by
    have sq (p : ℕ) (hp : p∈P a) : ¬p^2∣((y:ℤ)-a).natAbs := by
      intro div
      apply clean p hp
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd,Int.natCast_dvd]
      exact div
    have d : y≠a := by intro eq; subst y; simp at far
    have sep := (lt_of_not_ge (fun h=>far.not_ge (nearRadius_iff.mpr h))).le
    exact pair R T lp hn comp target absent (mem_filter.mp (mem_filter.mp ha).1).2
      (mem_filter.mp (mem_filter.mp hy).1).2 d sep
      (fun p hp=>sq p (mem_union_left _ hp)) (fun p hp=>sq p (mem_union_right _ hp))
  have bound := cells R T lc hn comp target absent cell cell' q s u v qsf ssf qr sr P 4 (C*e)
    (mul_nonneg cp.le (exp_pos _).le) primes good w w' D D' dp dp' wx wy
  apply bound.trans (mul_le_mul_of_nonneg_left _ (mul_nonneg dp dp'))
  have rr := mul_le_mul_of_nonneg_left (save b ls) (by norm_num : (0:ℝ)≤49)
  change (17+8*(4:ℕ))/(dyadicUnit b:ℝ)^15 + 4*(C*e)≤(49+4*C)*e
  change 49*(1/(dyadicUnit b:ℝ)^15)≤49*e at rr
  rw [←mul_div_assoc,mul_one] at rr
  norm_num
  linarith only [rr]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.cell_pair_variance_transfer

#print axioms Cogentic.Construction.cell_pair_covariance_approximation
