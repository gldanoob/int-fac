import Cogentic.JointSmoothBulk
import Cogentic.FixedOmissions
import Cogentic.ProgressionCorrection
import Cogentic.ClassBalance

namespace Cogentic.Construction
open Real Finset Cogentic.Window
noncomputable section

private theorem product_loss {ι : Type*} [DecidableEq ι] (D : Finset ι) (r : ι→ℝ)
    (rp : ∀ p, 0 ≤ r p) (ro : ∀ p, r p ≤ 1) :
    (∏ p∈D, (1-r p)) ≤ 1 ∧ 1-(∏ p∈D, (1-r p)) ≤ ∑ p∈D, r p := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert p D no ih =>
    rw [prod_insert no,sum_insert no]
    have nn : 0 ≤ ∏ p∈D, (1-r p) := prod_nonneg (fun p _ => sub_nonneg.mpr (ro p))
    refine ⟨(mul_le_mul (show 1-r p ≤ 1 by linarith only [rp p]) ih.1 nn zero_le_one).trans_eq (one_mul _),?_⟩
    nlinarith only [ih.2,mul_le_mul_of_nonneg_left ih.1 (rp p)]

theorem euler_ratio_loss (L K : Finset ℕ) (sub : K⊆L) (α : ℝ) :
    let t := eulerMass K α/eulerMass L α
    0 ≤ t ∧ t ≤ 1 ∧ 1-t ≤ ∑ p∈L\K, primeProbability α p := by
  intro t
  let f (p : ℕ) := 1+(p:ℝ)^(-α)
  have pos (p : ℕ) : 0 < f p := add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg (Nat.cast_nonneg _) _)
  have f0 (p : ℕ) : 0 ≤ (p:ℝ)^(-α) := rpow_nonneg (Nat.cast_nonneg _) _
  have rp (p : ℕ) : 0 ≤ primeProbability α p := div_nonneg (f0 p) (pos p).le
  have ro (p : ℕ) : primeProbability α p ≤ 1 := (div_le_one (pos p)).mpr (le_add_of_nonneg_left zero_le_one)
  have id (p : ℕ) : 1-primeProbability α p = (f p)⁻¹ := by
    dsimp only [primeProbability,f]; field_simp; ring
  have ratio : t=∏ p∈L\K, (1-primeProbability α p) := by
    change (∏ p∈K,f p)/(∏ p∈L,f p)=_
    rw [←Finset.prod_sdiff (f:=f) sub]
    simp_rw [id]
    rw [prod_inv_distrib]
    field_simp [(prod_pos (fun p (_ : p∈K) => pos p)).ne']
  rw [ratio]
  exact ⟨prod_nonneg (fun p _ => sub_nonneg.mpr (ro p)),product_loss _ _ rp ro⟩

/-- On the binary schedule a polynomial number of deletions, even after
the saddle normalizer cost, fits any fixed logarithmic-square error budget. -/
theorem nominal_deletion_saving (k : ℕ) (v : ℝ) (hv : 1 ≤ v) :
    ∃ b₀ : ℕ, ∀ b≥b₀, 17*(b:ℝ)^(k+1)*(Fixed.B b:ℝ)^(-199/400:ℝ) ≤ exp (-v*(Fixed.z b:ℝ)^2) := by
  obtain ⟨b₁,save⟩ := fixed_band_power_savings v hv
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows (k+7)
  refine ⟨max b₁ b₂,?_⟩
  intro b huge
  let x := dyadicUnit b
  let B : ℝ := Fixed.B b
  have h := deg b (max_le_iff.mp huge).2
  have z : 1 ≤ Fixed.z b := Nat.le_add_left 1 b.log2
  have exponent : 5+(k+1)*Fixed.z b ≤ Fixed.h b := by
    have hz := Nat.mul_le_mul_right (Fixed.z b) h
    dsimp only [Fixed.h]
    simp only [Nat.add_mul,Nat.one_mul] at hz ⊢
    omega
  have poly : 17*b^(k+1) ≤ x := calc
    _ ≤ 2^5*(2^(Fixed.z b))^(k+1) := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left Nat.lt_log2_self.le _)
    _ = 2^(5+(k+1)*Fixed.z b) := by rw [←Nat.pow_mul,←Nat.pow_add,Nat.mul_comm (Fixed.z b)]
    _ ≤ x := Nat.pow_le_pow_right (by decide) exponent
  have xx : 1 ≤ (x:ℝ) := by exact_mod_cast (Nat.one_le_two_pow (n:=Fixed.h b))
  have bb : (x:ℝ)^1000=B := by
    dsimp [B,x,dyadicUnit,Fixed.B,Fixed.beta]
    push_cast
    rw [←pow_mul,Nat.mul_comm]
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have b1 : 1 ≤ B := by rw [←bb]; exact one_le_pow₀ xx
  have rt : (x:ℝ) ≤ B^(1/4:ℝ) := by
    rw [←bb,←rpow_natCast_mul (zero_le_one.trans xx)]
    norm_num
    exact le_self_pow₀ xx (by decide)
  have pR : 17*(b:ℝ)^(k+1) ≤ x := by exact_mod_cast poly
  apply le_trans (mul_le_mul_of_nonneg_right (pR.trans rt) (Real.rpow_nonneg bp.le _))
  rw [←rpow_add bp]
  exact (rpow_le_rpow_of_exponent_le b1 (by norm_num : (1/4:ℝ)+(-199/400) ≤ -17/200)).trans (save b (max_le_iff.mp huge).1)

/-- Removing any polynomial number of primes from the retained saddle
band changes the nominal Euler times central integral by at most the
specified relative error. Both bands use the same full-band saddle. -/
theorem nested_nominal_density_ratio (k : ℕ) (v : ℝ) (hv : 1 ≤ v) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ (u α : ℝ) (L K : Finset ℕ),
    let J := primeBand b; let H := log (Fixed.B b)
    let mass := fun S : Finset ℕ =>
      eulerMass S α * omittedMass J (J\S) (primeProbability α) (fun p=>log p) H 0
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α → saddleMean J α=H*u →
    K⊆L → L⊆J → (J\K).card ≤ b^k →
    0 < mass L ∧ 0 < mass K ∧ |mass K/mass L-1| ≤ exp (-v*(Fixed.z b:ℝ)^2) := by
  classical
  obtain ⟨b₁,dele⟩ := fixed_prime_deletions k
  obtain ⟨b₂,floor⟩ := fixed_central_mass_lower k
  obtain ⟨b₃,save⟩ := nominal_deletion_saving k v hv
  refine ⟨max 110 (max b₁ (max b₂ b₃)),?_⟩
  intro b huge u α L K J H mass lo hi ha mean sub lj card
  obtain ⟨bb,b1,b2,b3⟩ := (max_le_iff.trans (and_congr_right (fun _ =>
    max_le_iff.trans (and_congr_right (fun _ => max_le_iff))))).mp huge
  have band : (Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime=J := by simp [J,primeBand]
  have cardL : (J\L).card ≤ b^k := (card_le_card (show J\L⊆J\K from fun _ hp => mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun h => (mem_sdiff.mp hp).2 (sub h)⟩)).trans card
  let m := (Fixed.B b:ℝ)^(-199/400:ℝ)
  let δ := (b:ℝ)^k*m
  let r := primeProbability α
  let g := fun S : Finset ℕ => omittedMass J (J\S) r (fun p=>log p) H 0
  let base := shiftedMass J r (fun p=>log p) H 0
  have d := dele b b1 u α lo hi ha
  rw [band] at d
  obtain ⟨hp,up,pm,_,_,caps,deletions⟩ := d
  have hh : 0 < H := hp
  have root : 0 < sqrt u := sqrt_pos.mpr (by linarith only [up])
  have center (S : Finset ℕ) (size : (J\S).card ≤ b^k) :
      1/(2*H*sqrt u) ≤ g S := by
    have h := floor b b2 u α 0 (J\S)
    dsimp only at h
    rw [band] at h
    exact h lo hi ha mean (by rw [abs_zero]; positivity) size sdiff_subset
  have pos (S : Finset ℕ) (size : (J\S).card ≤ b^k) : 0 < g S := (by positivity : 0 < 1/(2*H*sqrt u)).trans_le (center S size)
  have rp (p : ℕ) : 0 ≤ r p := by dsimp [r,primeProbability]; positivity
  have ro (p : ℕ) : r p ≤ 1 := by
    unfold r primeProbability
    apply (div_le_one (add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg (Nat.cast_nonneg _) _))).mpr
    linarith
  have diff (S : Finset ℕ) (size : (J\S).card ≤ b^k) : |g S-base| ≤ 4/H*δ :=
    (omitted_mass_error J (J\S) r (fun p=>log p) H 0 hh (fun _ _=>rp _) (fun _ _=>ro _)).trans
      (mul_le_mul_of_nonneg_left (deletions _ size) (by positivity))
  have diff2 : |g K-g L| ≤ 8/H*δ := by
    have step := abs_sub_le (g K) base (g L)
    rw [abs_sub_comm base (g L)] at step
    exact step.trans ((add_le_add (diff K card) (diff L cardL)).trans_eq (by ring))
  have gr : |g K/g L-1| ≤ 16*sqrt u*δ := by
    rw [←div_self (pos L cardL).ne',←sub_div,abs_div,abs_of_pos (pos L cardL),div_le_iff₀ (pos L cardL)]
    have mul := mul_le_mul_of_nonneg_left (center L cardL) (show 0 ≤ 16*sqrt u*δ by dsimp [δ]; positivity)
    apply diff2.trans (le_trans (le_of_eq ?_) mul)
    field_simp
    ring
  have euler := euler_ratio_loss L K sub α
  let e := eulerMass K α/eulerMass L α
  have ee : |e-1| ≤ δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr euler.2.1),neg_sub]
    apply euler.2.2.trans
    have point (p : ℕ) (hp : p∈L\K) : r p ≤ m := (caps p (lj (mem_sdiff.mp hp).1)).1
    have sum := sum_le_sum point
    rw [sum_const,nsmul_eq_mul] at sum
    have size : (L\K).card ≤ b^k := (card_le_card (show L\K⊆J\K from fun _ hp => mem_sdiff.mpr ⟨lj (mem_sdiff.mp hp).1,(mem_sdiff.mp hp).2⟩)).trans card
    exact sum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast size) pm)
  have ml : 0 < mass L := mul_pos (eulerMass_pos _ _) (pos L cardL)
  have mk : 0 < mass K := mul_pos (eulerMass_pos _ _) (pos K card)
  refine ⟨ml,mk,?_⟩
  have eq : mass K/mass L-1 = e*(g K/g L-1)+(e-1) := by
    change (eulerMass K α*g K)/(eulerMass L α*g L)-1=_
    dsimp only [e]; ring
  rw [eq]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_nonneg euler.1]
  have mult := mul_le_mul euler.2.1 gr (abs_nonneg _) zero_le_one
  rw [one_mul] at mult
  have bv : 110 ≤ (b:ℝ) := by exact_mod_cast bb
  have db : (Fixed.d b:ℝ) ≤ b := by exact_mod_cast Fixed.degree_le_bits b
  have sr : sqrt u ≤ b := (sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,by nlinarith only [hi,db,mul_nonneg (sub_nonneg.mpr bv) (Nat.cast_nonneg (α:=ℝ) b)]⟩)
  apply (add_le_add mult ee).trans (le_trans _ (save b b3))
  change 16*sqrt u*δ+δ ≤ 17*(b:ℝ)^(k+1)*m
  rw [pow_succ]
  have gain := mul_le_mul_of_nonneg_right sr (show 0 ≤ δ by dsimp [δ]; positivity)
  have extra := mul_le_mul_of_nonneg_right (show 1 ≤ (b:ℝ) by linarith only [bv]) (show 0 ≤ δ by dsimp [δ]; positivity)
  dsimp only [δ] at *
  linarith only [gain,extra]

/-- For the reduced gcd-one branch, the second-mark nominal model equals
the ordinary one-mark nominal model times the ratio of the two conductor
corrections, up to an arbitrarily prescribed log-square relative error. -/
theorem PrescribedRows.nominal_conductor_comparison (v : ℝ) (hv : 1 ≤ v) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀ ≤ b → 2 ≤ n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a ≤ Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    ∀ (side : Bool) (α β : ℝ),
    let pre := R.prefactor a' side
    let Y := (exactMean n ell a' side:ℝ)/pre
    α∈Set.Icc (199/200:ℝ) 1 → β∈Set.Icc (199/200:ℝ) 1 →
    saddleMean (primeBand b) α=log Y → saddleMean (primeBand b) β=log Y →
    let s₁ := firstStep n ell a' side; let s₂ := R.secondStep a a' side
    let ordinary := secondNominalDensity n ell a' pre side s₁ 1 β
    let second := secondNominalDensity n ell a' pre side s₂ 1 α
    let correction := coprimeFactor s₂.natAbs/coprimeFactor s₁.natAbs
    α=β ∧ 0 < ordinary ∧ 0 < correction ∧
      |second/(correction*ordinary)-1| ≤ exp (-v*(Fixed.z b:ℝ)^2) := by
  obtain ⟨b₁,compare⟩ := nested_nominal_density_ratio 3 v hv
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a a' R b huge hn comp target absent cap mark diff side α β pre Y ha hb ma mb s₁ s₂ ordinary second correction
  have big := degree b (max_le_iff.mp huge).2
  obtain ⟨_,cap',grid,_⟩ := (constructed_marks_iff ..).mp mark
  have am := mark_range hn big cap'
  have ep := (mem_dyadicTargets.mp target).1.pos
  have ⟨_,nz₁⟩ := firstStep_size am ep side (n:=n) (ell:=ell)
  obtain ⟨size₂,nz₂⟩ := R.secondStep_size (a:=a) am ep diff side
  have pp := R.pre_bounds target a' side
  let B : ℝ := Fixed.B b
  let H := log B
  let u := log Y/H
  let J := primeBand b
  let base := sieveBand n ell pre
  let band (s : ℤ) := base.filter (fun p=>¬p∣s.natAbs)
  let mass (S : Finset ℕ) := eulerMass S α*omittedMass J (J\S) (primeProbability α) (fun p=>log p) H 0
  have Bp : 0 < Fixed.B b := Nat.pow_pos (by decide)
  have Ap : 0 < Fixed.A b := Nat.pow_pos (by decide)
  have Hlb := (fixed_band_log_bounds b (Nat.succ_pos _) ((by decide : 16 ≤ 10004).trans big)).1
  have Hp : 0 < H := by
    have dr : (10004:ℝ) ≤ Fixed.d b := by exact_mod_cast big
    change 1000*(Fixed.d b:ℝ) ≤ H at Hlb
    linarith only [Hlb,dr]
  have bGT : 1 < B := (Real.log_pos_iff (Nat.cast_nonneg _)).mp Hp
  have divisor := total_prefactor R side target (g:=1) (a:=a') (by decide)
    (show 1 ≤ Fixed.A b*(Fixed.B b)^2 from Nat.mul_pos Ap (Nat.pow_pos Bp))
  rw [Nat.cast_one,mul_one] at divisor
  have win := one_point_window hn big target cap' grid side _ divisor
  have ulo : 90*(Fixed.d b:ℝ) ≤ u := win.2.2.1
  have uhi : u ≤ 110*(Fixed.d b:ℝ) := win.2.2.2.1
  have up : 0 < u := by
    have dr : (10004:ℝ) ≤ Fixed.d b := by exact_mod_cast big
    linarith only [ulo,dr]
  have mag : H*u=log Y := by dsimp [u]; field_simp
  have bp : (Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime=J := by simp [B,J,primeBand]
  have unique := band_saddle_unique (B:=B) bGT (by linarith only [ha.1] : 0 ≤ α) (by linarith only [hb.1] : 0 ≤ β)
  dsimp only at unique
  rw [bp] at unique
  have same := unique (ma.symm ▸ (mag ▸ mul_pos Hp up)) (ma.trans mb.symm)
  subst β
  have f := R.second_factors a a'
  have cc := (actual_conductor_caps (both:=prodPrimes (R.hit a ∩ R.hit a')) (aux:=1) target cap cap'
    f.2.2.2.2.2.2 (show 1 ≤ (Fixed.B b)^7 from Nat.pow_pos Bp) (hitsTarget n ell a' side)).2
  have qcap : s₂.natAbs ≤ conductorCap n := size₂ ▸ (by simpa only [mul_one] using cc)
  have dc := omitted_card hn big comp target absent pp.1 pp.2 (Int.natAbs_pos.mpr nz₂) qcap
  have divides : s₁.natAbs∣s₂.natAbs := by
    dsimp only [s₂,PrescribedRows.secondStep]
    rw [Int.natAbs_mul,Int.natAbs_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right ..) _
  have sub : band s₂⊆band s₁ := fun p h => mem_filter.mpr ⟨(mem_filter.mp h).1,fun h₁ => (mem_filter.mp h).2 (h₁.trans divides)⟩
  have lj : band s₁⊆J := fun p h => (mem_filter.mp (mem_filter.mp h).1).1
  obtain ⟨mpos,_,est⟩ := compare b (max_le_iff.mp huge).1 u α (band s₁) (band s₂) ulo uhi ha.1
    (ma.trans mag.symm) sub lj dc
  change 0 < mass (band s₁) at mpos
  change |mass (band s₂)/mass (band s₁)-1| ≤ _ at est
  let scale := Y^(α-1)/(2*π)
  have yp : 0 < Y := zero_lt_one.trans_le win.2.1
  have scalePos : 0 < scale := div_pos (rpow_pos_of_pos yp _) (by positivity)
  have op (s : ℤ) : secondNominalDensity n ell a' pre side s 1 α =
      coprimeFactor s.natAbs*scale*mass (band s) := by
    have one : 1∈squarefreeSupport base := mem_image.mpr ⟨∅,mem_powerset.mpr (empty_subset _),by simp⟩
    dsimp only [secondNominalDensity]
    rw [if_pos one,Nat.div_one,Nat.cast_one,mul_one]
    dsimp only [coprimeFactor,scale,Y,mass,band,J,B,base,H,b]
    ring
  have cf (s : ℤ) (nz : s≠0) : 0 < coprimeFactor s.natAbs := div_pos
    (by exact_mod_cast Int.natAbs_pos.mpr nz) (by exact_mod_cast Nat.totient_pos.mpr (Int.natAbs_pos.mpr nz))
  have c₁ : 0 < coprimeFactor s₁.natAbs := cf s₁ nz₁
  have c₂ : 0 < coprimeFactor s₂.natAbs := cf s₂ nz₂
  refine ⟨rfl,?_,div_pos c₂ c₁,?_⟩
  · change 0 < secondNominalDensity n ell a' pre side s₁ 1 α
    rw [op]
    exact mul_pos (mul_pos c₁ scalePos) mpos
  · change |secondNominalDensity n ell a' pre side s₂ 1 α/
        (correction*secondNominalDensity n ell a' pre side s₁ 1 α)-1| ≤ _
    rw [op,op]
    change |(coprimeFactor s₂.natAbs*scale*mass (band s₂))/
      ((coprimeFactor s₂.natAbs/coprimeFactor s₁.natAbs)*(coprimeFactor s₁.natAbs*scale*mass (band s₁)))-1| ≤ _
    rwa [show (coprimeFactor s₂.natAbs*scale*mass (band s₂))/
      ((coprimeFactor s₂.natAbs/coprimeFactor s₁.natAbs)*(coprimeFactor s₁.natAbs*scale*mass (band s₁)))=
      mass (band s₂)/mass (band s₁) by field_simp]

theorem normalization_band_saving {b : ℕ} (bp : 0 < b) :
    exp (-(Fixed.U b:ℝ)) ≤ (Fixed.B b:ℝ)^(-17/200:ℝ) := by
  have ⟨x,_,_,bb,_,uu,_⟩ := dyadic_data bp
  have dp := Fixed.degree_pos bp
  have bu : Fixed.B b ≤ Fixed.U b := by
    rw [bb,uu]
    exact Nat.pow_le_pow_right (by omega : 0 < dyadicUnit b) (by omega : 1000 ≤ 100000*Fixed.d b)
  have hB : 0 < (Fixed.B b:ℝ) := by dsimp [Fixed.B]; positivity
  have base : 1 ≤ (Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_le_two_pow (n:=Fixed.beta b))
  rw [rpow_def_of_pos hB,exp_le_exp]
  have lg : 0 ≤ log (Fixed.B b) := log_nonneg base
  have logB := log_le_self hB.le
  have cast : (Fixed.B b:ℝ) ≤ Fixed.U b := by exact_mod_cast bu
  linarith only [lg,logB,cast]

/-- The actual one-mark marginal has a positive nominal density at its
exact saddle, with a fixed multiple of the requested relative error. -/
theorem PrescribedRows.first_nominal_marginal (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1 ≤ v) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side; let J := sieveBand n ell pre
    let Y := (exactMean n ell a side:ℝ)/pre
    let p := prescribedProbability R side (fun k=>supportedValue J (R.intercept a side k.1 k.2))
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log Y ∧
      let m := secondNominalDensity n ell a pre side (firstStep n ell a side) 1 α
      0 < m ∧ |p-m|≤C*exp (-v*(Fixed.z b:ℝ)^2)*m := by
  obtain ⟨C,cp,b₁,progression⟩ := first_polynomial_progression line v hv
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  obtain ⟨b₃,save⟩ := fixed_band_power_savings v hv
  refine ⟨90*(1+C)+C,by positivity,max b₁ (max b₂ b₃),?_⟩
  intro n ell a R b huge hn comp target absent mark side pre J Y p
  obtain ⟨one,two,three⟩ := (max_le_iff.trans (and_congr_right (fun _=>max_le_iff))).mp huge
  have big := degree b two
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  obtain ⟨u,w,ok,prob⟩ := R.first_probability ((by decide : 3≤10004).trans big) target cap (mark_range hn big cap) side
  obtain ⟨gcd,_,α,h⟩ := progression R one hn comp target absent mark side u w ok
  unfold PositiveScalarModel at h
  dsimp only at h
  rw [gcd] at h
  simp only [Nat.div_one,Nat.cast_one,mul_one] at h
  obtain ⟨ha,mean,mp,est⟩ := h
  let s := firstStep n ell a side
  let z := scalarMass J (R.intercept a side u w) s Y (oneWidth n ell a/pre)
  let e := exp (-v*(Fixed.z b:ℝ)^2)
  let m := secondNominalDensity n ell a pre side s 1 α
  let band := J.filter (fun p=>¬p∣s.natAbs)
  let raw := ((s.natAbs:ℝ)/s.natAbs.totient)*(Y^(α-1)*eulerMass band α)*
    omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p=>log p) (log (Fixed.B b)) 0
  change 0 < raw at mp
  change ‖(2*π:ℝ) • z - (raw:ℂ)‖ ≤ C*raw*e at est
  change |p-z.re| ≤ 90*exp (-(Fixed.U b:ℝ))*z.re at prob
  have piPos : 0 < 2*π := by positivity
  have eq : m=raw/(2*π) := by
    have one : 1∈squarefreeSupport J := mem_image.mpr ⟨∅,mem_powerset.mpr (empty_subset _),by simp⟩
    dsimp only [m,secondNominalDensity]
    rw [if_pos one,Nat.div_one,Nat.cast_one,mul_one]
    dsimp only [raw,band,Y,J,b]
    ring
  have mn : 0 < m := eq ▸ div_pos mp piPos
  have realEst := (Complex.abs_re_le_norm _).trans est
  simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re] at realEst
  have ze : |z.re-m| ≤ C*e*m := by
    rw [eq,show z.re-raw/(2*π)=((2*π)*z.re-raw)/(2*π) by field_simp,
      abs_div,abs_of_pos piPos,←mul_div_assoc,div_le_div_iff_of_pos_right piPos]
    exact realEst.trans_eq (mul_right_comm ..)
  have en : 0≤e := (exp_pos _).le
  have small : e≤1 := exp_le_one_iff.mpr (by nlinarith only [sq_nonneg (Fixed.z b:ℝ),mul_nonneg (show 0≤v by linarith) (sq_nonneg (Fixed.z b:ℝ))])
  have nerr : exp (-(Fixed.U b:ℝ))≤e := (normalization_band_saving (b:=b) (Nat.succ_pos _)).trans (save b three)
  have zpos : 0≤z.re := by by_contra! bad; nlinarith only [prob,abs_nonneg (p-z.re),mul_neg_of_pos_of_neg (by positivity : 0<90*exp (-(Fixed.U b:ℝ))) bad]
  have capz : z.re ≤ (1+C)*m := by
    have eb := mul_le_mul_of_nonneg_left small cp.le
    linarith only [(abs_le.mp ze).2,mul_le_mul_of_nonneg_right eb mn.le]
  have a := mul_le_mul (mul_le_mul_of_nonneg_left nerr (by norm_num : (0:ℝ)≤90)) capz zpos (by positivity)
  refine ⟨α,ha,mean,mn,?_⟩
  apply (abs_sub_le p z.re m).trans
  change |p-z.re|+|z.re-m| ≤ (90*(1+C)+C)*e*m
  linarith only [prob,ze,a]

/-- The second nominal density on a gcd-one fiber is the true second-mark
marginal times its conductor correction, to any fixed log-square precision. -/
theorem PrescribedRows.nominal_to_actual_marginal (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a → ∀ (side : Bool) (α : ℝ),
    let pre := R.prefactor a' side; let J := sieveBand n ell pre
    let Y := (exactMean n ell a' side:ℝ)/pre
    α∈Set.Icc (199/200:ℝ) 1 → saddleMean (primeBand b) α=log Y →
    let s₁ := firstStep n ell a' side; let s₂ := R.secondStep a a' side
    let p := prescribedProbability R side (fun z=>supportedValue J (R.intercept a' side z.1 z.2))
    let second := secondNominalDensity n ell a' pre side s₂ 1 α
    let correction := coprimeFactor s₂.natAbs/coprimeFactor s₁.natAbs
    0 < correction*p ∧ |second/(correction*p)-1| ≤ exp (-K*(Fixed.z b:ℝ)^2) := by
  have large : 1 ≤ K+1 := by linarith
  obtain ⟨C,cp,b₁,first⟩ := PrescribedRows.first_nominal_marginal line (K+1) large
  obtain ⟨b₂,cmp⟩ := PrescribedRows.nominal_conductor_comparison (K+1) large
  obtain ⟨b₃,decay⟩ := fixed_class_accuracy (2*(1+C))
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell a a' R b huge hn comp target absent cap mark diff side α pre J Y ha ma s₁ s₂ p second correction
  obtain ⟨one,two,three⟩ := (max_le_iff.trans (and_congr_right (fun _=>max_le_iff))).mp huge
  obtain ⟨β,hb,mb,_,err⟩ := first R one hn comp target absent mark side
  obtain ⟨_,mp,hc,close⟩ := cmp R two hn comp target absent cap mark diff side α β ha hb ma mb
  let m := secondNominalDensity n ell a' pre side s₁ 1 β
  let z : ℝ := Fixed.z b
  let e := exp (-(K+1)*z^2)
  change 0 < m at mp
  change 0 < correction at hc
  change |p-m| ≤ C*e*m at err
  change |second/(correction*m)-1| ≤ e at close
  have W := decay b three
  change 2*(1+C)*exp (-z^2) ≤ 1/2 at W
  have eSmall : e ≤ exp (-z^2) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (by linarith : 0 ≤ K) (sq_nonneg z)]
  have small : C*e ≤ 1/2 := (mul_le_mul (by linarith only [cp]) eSmall (exp_pos _).le (by positivity)).trans W
  have top : m ≤ 2*p := by linarith only [(abs_le.mp err).1,mul_le_mul_of_nonneg_right small mp.le]
  have pp : 0 < p := by linarith only [mp,top]
  have den := mul_pos hc mp
  rw [←div_self den.ne',←sub_div,abs_div,abs_of_pos den,div_le_iff₀ den] at close
  have left : |correction*m-correction*p| ≤ correction*(C*e*m) := by
    rw [←mul_sub,abs_mul,abs_of_pos hc,abs_sub_comm]
    exact mul_le_mul_of_nonneg_left err hc.le
  have h := abs_sub_le second (correction*m) (correction*p)
  have gain : 2*(1+C)*e ≤ exp (-K*z^2) := by
    rw [show e = exp (-z^2)*exp (-K*z^2) by dsimp only [e]; rw [←exp_add]; congr 1; ring,←mul_assoc]
    exact (mul_le_mul_of_nonneg_right (W.trans (by norm_num : (1:ℝ)/2 ≤ 1)) (exp_pos _).le).trans_eq (one_mul _)
  have t := mul_le_mul_of_nonneg_left top (show 0 ≤ (1+C)*e*correction by dsimp [e]; positivity)
  have capE := mul_le_mul_of_nonneg_right gain (mul_nonneg hc.le pp.le)
  refine ⟨mul_pos hc pp,?_⟩
  rw [←div_self (mul_pos hc pp).ne',←sub_div,abs_div,abs_of_pos (mul_pos hc pp),div_le_iff₀ (mul_pos hc pp)]
  change |second-correction*p| ≤ exp (-K*z^2)*(correction*p)
  linarith only [h,close,left,t,capE]

/-- The actual conditional coefficient probability for a separated second
mark and a bulk first observation on the gcd-one branch. The predictor is
the true one-mark probability times the conductor correction. -/
theorem PrescribedRows.gcd_one_conditional_smooth (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks → a'≠a →
    (Fixed.A b:ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit b:ℝ)^50 →
    ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let x := u+(a:ℤ)*v
    |(x:ℝ)-lineCenter n a|≤(b:ℝ)^3*projectionScale n a →
    let c := R.intercept a' side u v; let s := R.secondStep a a' side
    commonDivisor c s=1 →
    let J := sieveBand n ell (R.prefactor a' side)
    let y := fun j : ℤ => v+(prodPrimes (R.miss a):ℤ)*j
    let key := fun j : ℤ => (x-a*y j,y j)
    let W := fun j : ℤ => coefficientWeight n (key j)
    let E := fun j : ℤ => supportedValue J (R.intercept a' side (key j).1 (key j).2)
    let Z := ∑' j,W j
    let θ := (∑' j, if E j then W j else 0)/Z
    let p := prescribedProbability R side (fun z=>supportedValue J (R.intercept a' side z.1 z.2))
    let correction := coprimeFactor s.natAbs/coprimeFactor (firstStep n ell a' side).natAbs
    0 < Z ∧ 0 < correction*p ∧ |θ/(correction*p)-1| ≤ C*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,b₁,observed⟩ := observed_second_scalar line K hK
  obtain ⟨b₂,nominal⟩ := PrescribedRows.nominal_to_actual_marginal line K hK
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 10004
  obtain ⟨b₄,save⟩ := fixed_band_power_savings K hK
  let D := 6*(1+C)+C
  have dp : 0<D := by dsimp [D]; positivity
  refine ⟨2*D+1,by positivity,max b₁ (max b₂ (max b₃ b₄)),?_⟩
  intro n ell a a' R b huge hn comp target absent cap mark diff sep side u v ok x bulk c s gcd J y key W E Z θ p correction
  obtain ⟨one,two,three,four⟩ := (max_le_iff.trans (and_congr_right (fun _=>
    max_le_iff.trans (and_congr_right (fun _=>max_le_iff))))).mp huge
  have big := degree b three
  have bx : (x:ℝ)=(u:ℝ)+(a:ℝ)*(v:ℝ) := by simp only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have am := mark_range hn big ((constructed_marks_iff ..).mp mark).2.1
  have row := R.second_probability ((by decide : 3≤10004).trans big) target cap am diff side u v ok
  let pre := R.prefactor a' side
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  let z := scalarMass J c s (conditionalMean n ell a a' side (x:ℝ)/pre) (twoWidth n ell a a'/pre)
  change 0<Z ∧ |θ-z.re|≤6*exp (-(Fixed.U b:ℝ))*z.re at row
  have branch := (observed R one hn comp target absent cap mark sep side u v ok (bx ▸ bulk)).2
  have eligible : 1∈squarefreeSupport J := mem_image.mpr ⟨∅,mem_powerset.mpr (empty_subset _),by simp⟩
  obtain ⟨α,ha,mean,rawp,model⟩ := branch (gcd ▸ eligible)
  change saddleMean (primeBand b) α=log ((exactMean n ell a' side:ℝ)/((pre:ℝ)*commonDivisor c s)) at mean
  rw [gcd,Nat.cast_one,mul_one] at mean
  let m := secondNominalDensity n ell a' pre side s 1 α
  let band := J.filter (fun p=>¬p∣s.natAbs)
  let Y := (exactMean n ell a' side:ℝ)/pre
  let raw := ((s.natAbs:ℝ)/s.natAbs.totient)*Y^(α-1)*eulerMass band α*
    omittedMass (primeBand b) (primeBand b\band) (primeProbability α) (fun p=>log p) (log (Fixed.B b)) 0
  change commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)=1 at gcd
  simp only [gcd,Nat.div_one,Nat.cast_one,mul_one,←bx] at model rawp
  change ‖(2*π:ℝ) • z-(raw:ℂ)‖ ≤ C*raw*e at model
  change 0 < raw at rawp
  have mEq : m=raw/(2*π) := by
    dsimp only [m,secondNominalDensity]
    rw [if_pos eligible,Nat.div_one,Nat.cast_one,mul_one]
  have piP : 0 < 2*π := by positivity
  have mp : 0 < m := mEq ▸ div_pos rawp piP
  have re := (Complex.abs_re_le_norm _).trans model
  simp only [Complex.sub_re,Complex.smul_re,smul_eq_mul,Complex.ofReal_re] at re
  have sz : |z.re-m|≤C*e*m := by
    rw [mEq,show z.re-raw/(2*π)=((2*π)*z.re-raw)/(2*π) by field_simp,
      abs_div,abs_of_pos piP,←mul_div_assoc,div_le_div_iff_of_pos_right piP]
    exact re.trans_eq (mul_right_comm ..)
  have ⟨pred,rel⟩ := nominal R two hn comp target absent cap mark diff side α ha mean
  let ref := correction*p
  change 0 < ref at pred
  change |m/ref-1|≤e at rel
  rw [←div_self pred.ne',←sub_div,abs_div,abs_of_pos pred,div_le_iff₀ pred] at rel
  have epos : 0≤e := (exp_pos _).le
  have small : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have gain := (normalization_band_saving (b:=b) (Nat.succ_pos _)).trans (save b four)
  change exp (-(Fixed.U b:ℝ))≤e at gain
  have zp : 0≤z.re := by
    by_contra! no
    exact (not_lt_of_ge ((abs_nonneg _).trans row.2)) (mul_neg_of_pos_of_neg (by positivity) no)
  have zcap : z.re≤(1+C)*m := by
    have ec := mul_le_mul_of_nonneg_left small cp.le
    linarith only [(abs_le.mp sz).2,mul_le_mul_of_nonneg_right ec mp.le]
  have capm : m≤2*ref := by linarith only [(abs_le.mp rel).2,mul_le_mul_of_nonneg_right small pred.le]
  have fcap := mul_le_mul (mul_le_mul_of_nonneg_left gain (by norm_num : (0:ℝ)≤6)) zcap zp (by positivity)
  have sm : |θ-m|≤D*e*m := by
    apply (abs_sub_le θ z.re m).trans
    dsimp only [D]
    linarith only [sz,row.2,fcap]
  refine ⟨row.1,pred,?_⟩
  change |θ/ref-1|≤(2*D+1)*e
  rw [←div_self pred.ne',←sub_div,abs_div,abs_of_pos pred,div_le_iff₀ pred]
  rw [div_self pred.ne']
  have bound := mul_le_mul_of_nonneg_left capm (mul_nonneg dp.le epos)
  apply (abs_sub_le θ m ref).trans
  linarith only [sm,rel,bound]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.nested_nominal_density_ratio

#print axioms Cogentic.Construction.PrescribedRows.nominal_conductor_comparison

#print axioms Cogentic.Construction.PrescribedRows.first_nominal_marginal

#print axioms Cogentic.Construction.PrescribedRows.nominal_to_actual_marginal

#print axioms Cogentic.Construction.PrescribedRows.gcd_one_conditional_smooth
