import Cogentic.CellCountConcentration
import Cogentic.RankCoverage

namespace Cogentic.Construction
open Finset Real Filter Cogentic.Window
open scoped Classical

theorem target_class_card {n ell : ℕ} (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (cell : Option (Bool×Fin (Fixed.d (n.log2+1)))) (r : ℕ) :
    let b := n.log2+1; let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ r [MOD ell]); let M := 2*(cellMarkCount b:ℝ)/ell
    (X.card:ℝ)≤M := by
  intro b X M
  have ep := (mem_dyadicTargets.mp target).1
  have ep' : 0<(ell:ℝ) := by exact_mod_cast ep.pos
  have eB : ell≤Fixed.B b := (mem_dyadicTargets.mp target).2.2
  have block (a : ℕ) (h : a∈X) := And.intro (mem_filter.mp (mem_filter.mp h).1).1 (mem_filter.mp h).2
  have sub : X ⊆ (Ico (firstCellMark b cell) (firstCellMark b cell+cellMarkCount b)).filter (fun a=>a ≡ r [MOD ell]) :=
    fun a h=>mem_filter.mpr (block a h)
  have cnt := (abs_le.mp (interval_residue_error (Nat.le_add_right (firstCellMark b cell) (cellMarkCount b)) ep.pos r)).2
  simp only [Nat.cast_add,add_sub_cancel_left] at cnt
  have em : ell≤cellMarkCount b := eB.trans (Nat.pow_le_pow_right (by decide : 0<2)
    (by change 1000*Fixed.h b≤9997*Fixed.h b; omega))
  have unit := (one_le_div ep').mpr (Nat.cast_le.mpr em)
  refine (Nat.cast_le.mpr (card_le_card sub)).trans ?_
  dsimp only [M]; rw [mul_div_assoc]; linarith only [cnt,unit]

theorem pair_gamma_class_excess (P Y : Finset ℕ) (pr : ∀ p∈P,p.Prime)
    (m x lo M ell r : ℕ) (ep : 0<ell) (cop : ∀ p∈P,ell.Coprime p)
    (interval : ∀ a∈Y, a∈Ico lo (lo+M) ∧ a ≡ r [MOD ell]) :
    (∑ y∈Y,((pairGamma P m x y)^2-1)) ≤
      ((M:ℝ)/ell)*((∑ T∈P.powerset,pairDivisorWeight T/(sieveProduct T:ℝ))-1)+
        ∑ T∈P.powerset,pairDivisorWeight T := by
  classical
  let S := P.powerset.erase ∅
  let hit (T : Finset ℕ) (y : ℕ) := x ≡ y [MOD sieveProduct T] ∧ ∀ p∈T, ¬x ≡ m [MOD p]
  have empty : (∅ : Finset ℕ)∈P.powerset := mem_powerset.mpr (empty_subset _)
  have positive (T) (hT : T⊆P) : 0≤pairDivisorWeight T := by
    apply prod_nonneg; intro p hp
    have lb : (2:ℝ)≤p := by exact_mod_cast (pr p (hT hp)).two_le
    exact div_nonneg (by linarith) (sq_nonneg _)
  have point (y) : (pairGamma P m x y)^2-1 =
      ∑ T∈S, if hit T y then pairDivisorWeight T else 0 := by
    rw [pair_gamma_square P pr m x y,←sum_erase_add _ _ empty]
    simp [S,hit,pairDivisorWeight,sieveProduct,Nat.modEq_one]
  simp_rw [point]
  rw [sum_comm]
  have each (T : Finset ℕ) (member : T∈S) :
      (∑ y∈Y, if hit T y then pairDivisorWeight T else 0) ≤
        ((M:ℝ)/ell)*(pairDivisorWeight T/(sieveProduct T:ℝ))+pairDivisorWeight T := by
    let q := sieveProduct T
    have sub := mem_powerset.mp (mem_of_mem_erase member)
    have qp : 0<q := prod_pos (fun p hp => (pr p (sub hp)).pos)
    have ec : ell.Coprime q := Nat.coprime_prod_right_iff.mpr (fun p hp=>cop p (sub hp))
    let v := Nat.chineseRemainder ec r x
    let ys := (Ico lo (lo+M)).filter (fun y => y ≡ v.val [MOD ell*q])
    have ysub : (Y.filter (hit T))⊆ys := by
      intro y h
      obtain ⟨hy,eq,_⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨(interval y hy).1,Nat.chineseRemainder_modEq_unique ec (interval y hy).2 eq.symm⟩
    have size := (abs_le.mp (interval_residue_error (Nat.le_add_right lo M) (Nat.mul_pos ep qp) v.val)).2
    change (ys.card:ℝ)-(((lo+M:ℕ):ℝ)-lo)/((ell*q:ℕ):ℝ) ≤ 1 at size
    simp only [Nat.cast_add,add_sub_cancel_left,Nat.cast_mul,←div_div] at size
    have card : ((Y.filter (hit T)).card:ℝ)≤(M:ℝ)/ell/q+1 :=
      (Nat.cast_le.mpr (card_le_card ysub)).trans (by linarith only [size])
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right card (positive T sub)).trans_eq (by dsimp only [q]; ring)
  have both := sum_le_sum each
  rw [sum_add_distrib,←mul_sum] at both
  have first := sum_erase_add P.powerset (fun T=>pairDivisorWeight T/(sieveProduct T:ℝ)) empty
  change (∑ T∈S,_) + _ = _ at first
  simp only [sieveProduct,prod_empty,pairDivisorWeight,Nat.cast_one,div_one] at first
  have one : (∑ T∈S,pairDivisorWeight T/(sieveProduct T:ℝ))=
      (∑ T∈P.powerset,pairDivisorWeight T/(sieveProduct T:ℝ))-1 := eq_sub_of_add_eq first
  rw [one] at both
  exact both.trans (add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
    (fun T h _ => positive T (mem_powerset.mp h))))


set_option maxHeartbeats 500000 in
/-- For any fixed loss budget, the true normalized score variance on
one target residue in a cell is eventually smaller than that budget divided by d.
The bound holds uniformly for the same coefficient law in every cell. -/
theorem target_class_covariance (line : DirichletLZerosOnLine) (k : ℕ) (kp : 0<k) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (r : ℕ),
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ r [MOD ell]); let M := 2*(cellMarkCount b:ℝ)/ell
    (∑ a∈X,∑ y∈X, normalizedSmoothCovariance R T a y)/(M:ℝ)^2 ≤ 1/((k:ℝ)*Fixed.d b) := by
  obtain ⟨C,cp,b₁,compare⟩ := cell_pair_covariance_approximation line 3 (by norm_num)
  obtain ⟨d₀,inverse⟩ := pair_weight_inverse_prime_bound
  obtain ⟨b₂,mass⟩ := fixed_pair_weight_sum line
  obtain ⟨b₃,band⟩ := fixed_band_power_savings 50 (by norm_num)
  obtain ⟨b₄,budget⟩ := fixed_class_accuracy ((k:ℝ)*(C+1))
  obtain ⟨t,cap⟩ := exists_nat_ge (exp (384*(k:ℝ)))
  obtain ⟨b₅,grow⟩ := Fixed.degree_grows (max d₀ (max 2 t))
  refine ⟨max (max b₁ b₂) (max b₃ (max b₄ b₅)),?_⟩
  intro n ell R T b huge hn comp target absent cell r X M
  obtain ⟨one,two⟩ := max_le_iff.mp (max_le_iff.mp huge).1
  obtain ⟨three,tmp⟩ := max_le_iff.mp (max_le_iff.mp huge).2
  obtain ⟨four,five⟩ := max_le_iff.mp tmp
  let d := Fixed.d b; let z : ℝ := Fixed.z b; let B : ℝ := Fixed.B b; let P := pairCorrectionPrimes b
  obtain ⟨dmin,dd⟩ := max_le_iff.mp (grow b five)
  obtain ⟨dg,lower⟩ := max_le_iff.mp dd
  have dr : 0<(d:ℝ) := by exact_mod_cast (by change 2≤d at dg; omega : 0<d)
  have kr : 0<(k:ℝ) := by exact_mod_cast kp
  have k1 : (1:ℝ)≤k := by exact_mod_cast kp
  have zl : 1≤z := by dsimp [z,Fixed.z]; exact_mod_cast Nat.le_add_left 1 b.log2
  have lp : 0<log (d:ℝ) := log_pos (by change 1<(Fixed.d b:ℝ); exact_mod_cast (by omega : 1<Fixed.d b))
  have logbig : 384*(k:ℝ)≤log d := (le_log_iff_exp_le dr).mpr (cap.trans (by exact_mod_cast lower))
  have primes (p) (hp : p∈P) : p.Prime ∧ d<p ∧ p≤Fixed.B b := by
    obtain ⟨pr,small,hi⟩ := mem_pairCorrectionPrimes.mp hp
    exact ⟨pr,small,hi.trans (Nat.pow_le_pow_right (by decide : 0<2) (by change 200*Fixed.h b≤1000*Fixed.h b; omega))⟩
  let w := 96/((d:ℝ)*log d)
  have wp : 0≤w := by dsimp [w]; positivity
  have wo : w≤1 := (div_le_iff₀ (mul_pos dr lp)).mpr (by
    have d1 : 1≤(d:ℝ) := by exact_mod_cast (by change 2≤d at dg; omega : 1≤d)
    nlinarith only [mul_nonneg (sub_nonneg.mpr d1) lp.le,logbig,k1])
  have inverseBound := inverse d dmin P (fun p h => ⟨(primes p h).1,(primes p h).2.1⟩)
  have small := (le_abs_self (exp w-1)).trans (Real.abs_exp_sub_one_le (by simpa only [abs_of_nonneg wp] using wo))
  rw [abs_of_nonneg wp] at small
  have absw : exp w-1≤1/(2*k*d) := small.trans (by
    rw [le_div_iff₀ (by positivity : (0:ℝ)<2*k*d)]
    dsimp only [w]; field_simp [dr.ne',lp.ne']
    linarith only [logbig])
  have ep := (mem_dyadicTargets.mp target).1
  have ep' : 0<(ell:ℝ) := by exact_mod_cast ep.pos
  have eB : ell≤Fixed.B b := (mem_dyadicTargets.mp target).2.2
  have hh : 0<Fixed.h b := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos n.log2)) (Nat.succ_pos _)
  have cop (p : ℕ) (hp : p∈P) : ell.Coprime p := by
    apply (ep.coprime_iff_not_dvd).mpr
    have less : p<ell := ((mem_pairCorrectionPrimes.mp hp).2.2.trans
      (Nat.pow_le_pow_right (by decide : 0<2) (by change 200*Fixed.h b≤1000*Fixed.h b-1; omega))).trans_lt
      (mem_dyadicTargets.mp target).2.1
    exact fun h=>less.not_ge (Nat.le_of_dvd (primes p hp).1.pos h)
  have block (a : ℕ) (h : a∈X) := And.intro (mem_filter.mp (mem_filter.mp h).1).1 (mem_filter.mp h).2
  have xs := target_class_card target cell r
  change (X.card:ℝ)≤M at xs
  have mpos : 0<M := by dsimp only [M,cellMarkCount]; positivity
  have model (a : ℕ) :
      (∑ y∈X,((pairGamma P (Fixed.rootBase n) a y)^2-1)) ≤ M/(2*k*d)+exp (48*z) := by
    have est := pair_gamma_class_excess P X (fun p h=>(primes p h).1) (Fixed.rootBase n) a
      (firstCellMark b cell) (cellMarkCount b) ell r ep.pos cop block
    have mm : (cellMarkCount b:ℝ)/ell ≤ M := by dsimp only [M]; rw [mul_div_assoc]; linarith only [div_nonneg (Nat.cast_nonneg (α:=ℝ) (cellMarkCount b)) ep'.le]
    exact est.trans (add_le_add ((mul_le_mul_of_nonneg_left ((sub_le_sub_right inverseBound 1).trans absw)
      (by positivity)).trans ((mul_le_mul_of_nonneg_right mm (by positivity : 0≤1/(2*(k:ℝ)*d))).trans_eq (by ring))) (mass b two P primes))
  have bound := sum_le_sum (s:=X) (fun a _=>model a)
  rw [sum_const,nsmul_eq_mul] at bound
  have modelTotal := bound.trans (mul_le_mul_of_nonneg_right xs (by positivity))
  let cov := normalizedSmoothCovariance R T
  let g := fun a y=> (pairGamma P (Fixed.rootBase n) a y)^2-1
  have ecap : ell≤(Fixed.B b)^3 := eB.trans (Nat.le_self_pow (by decide) _)
  have err := compare R T one hn comp target absent cell cell ell ell r r
    ep.squarefree ep.squarefree ecap ecap (fun _=>1) (fun _=>1) 1 1 zero_le_one zero_le_one (by simp) (by simp)
  simp only [one_mul] at err
  change (ell:ℝ)*ell*|(∑ a∈X,∑ y∈X,(cov a y-g a y))|/(cellMarkCount b:ℝ)^2 ≤ C*exp (-3*z^2) at err
  simp only [sum_sub_distrib] at err
  change (ell:ℝ)*ell*|((∑ a∈X,∑ y∈X,cov a y)-(∑ a∈X,∑ y∈X,g a y))|/(cellMarkCount b:ℝ)^2 ≤ C*exp (-3*z^2) at err
  have raw : (∑ a∈X,∑ y∈X,cov a y)-(∑ a∈X,∑ y∈X,g a y) ≤ C*exp (-3*z^2)*M^2 := by
    have cm : (0:ℝ)<cellMarkCount b := by dsimp [cellMarkCount]; positivity
    have cap := (div_le_iff₀ (sq_pos_of_pos cm)).mp err
    apply (le_abs_self _).trans
    apply le_of_mul_le_mul_left (a:=(ell:ℝ)*ell) _ (by positivity)
    have eq : (ell:ℝ)*ell*(C*exp (-3*z^2)*M^2)=4*(C*exp (-3*z^2)*(cellMarkCount b:ℝ)^2) := by
      dsimp only [M]; field_simp; ring
    rw [eq]; linarith only [cap,show 0≤C*exp (-3*z^2)*(cellMarkCount b:ℝ)^2 by positivity]
  have bo : 1≤B := by dsimp [B,Fixed.B]; exact_mod_cast Nat.one_le_two_pow
  have mb : B≤M := by
    have pow : (Fixed.B b)^2≤cellMarkCount b := by
      change (2^(1000*Fixed.h b))^2≤2^(9997*Fixed.h b)
      rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have sq : ell*(Fixed.B b)≤cellMarkCount b := (Nat.mul_le_mul_right _ eB).trans (by simpa [sq] using pow)
    have realSq : (ell:ℝ)*B≤cellMarkCount b := by dsimp only [B]; exact_mod_cast sq
    apply (le_div_iff₀ ep').mpr
    nlinarith only [realSq,Nat.cast_nonneg (α:=ℝ) (cellMarkCount b)]
  have neg : 1/(M:ℝ)≤exp (-50*z^2) := calc
    _ ≤ 1/B := one_div_le_one_div_of_le (zero_lt_one.trans_le bo) mb
    _ = B^(-(1:ℝ)) := by rw [rpow_neg (zero_le_one.trans bo),rpow_one,one_div]
    _ ≤ B^(-17/200:ℝ) := rpow_le_rpow_of_exponent_le bo (by norm_num)
    _ ≤ _ := band b three
  have tail : exp (48*z)/(M:ℝ)≤exp (-2*z^2) := calc
    _ = (1/(M:ℝ))*exp (48*z) := by ring
    _ ≤ exp (-50*z^2)*exp (48*z) := mul_le_mul_of_nonneg_right neg (exp_pos _).le
    _ ≤ _ := by rw [←exp_add]; apply exp_le_exp.mpr; nlinarith only [mul_nonneg (sub_nonneg.mpr zl) (zero_le_one.trans zl)]
  have dz : (d:ℝ)≤exp (z^2) := calc
    _ ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Fixed.degree_le_bits b).trans Nat.lt_log2_self.le
    _ = exp ((Fixed.z b:ℝ)*log 2) := by rw [←rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ)<2),mul_comm]
    _ ≤ _ := by apply exp_le_exp.mpr; change z*log 2≤z^2
                nlinarith only [mul_nonneg (sub_nonneg.mpr zl) (zero_le_one.trans zl),
                  mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)) (zero_le_one.trans zl)]
  have rem : (C*exp (-3*z^2)+exp (-2*z^2))≤1/(2*k*d) := by
    have cmp : exp (-3*z^2)≤exp (-2*z^2) := exp_le_exp.mpr (by nlinarith only [sq_nonneg z])
    have est := mul_le_mul_of_nonneg_right dz (show 0≤((k:ℝ)*(C+1))*exp (-2*z^2) by positivity)
    rw [show exp (z^2)*(((k:ℝ)*(C+1))*exp (-2*z^2)) = ((k:ℝ)*(C+1))*exp (-z^2) by
          rw [mul_left_comm,←exp_add]; congr 2; ring] at est
    have half := est.trans (budget b four)
    rw [le_div_iff₀ (by positivity : (0:ℝ)<2*k*d)]
    linarith only [half,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cmp cp.le)
      (by positivity : 0≤(k:ℝ)*d)]
  change (∑ a∈X,∑ y∈X,cov a y)/(M:ℝ)^2 ≤ _
  have total : (∑ a∈X,∑ y∈X,cov a y) ≤ C*exp (-3*z^2)*(M:ℝ)^2+
      (M:ℝ)*((M:ℝ)/(2*k*d)+exp (48*z)) := by
    change (∑ a∈X,∑ y∈X,g a y) ≤ _ at modelTotal
    linarith only [raw,modelTotal]
  have error := mul_le_mul_of_nonneg_right rem (sq_nonneg (M:ℝ))
  have endpoint := mul_le_mul_of_nonneg_right ((div_le_iff₀ mpos).mp tail) mpos.le
  apply (div_le_iff₀ (sq_pos_of_pos mpos)).mpr
  apply total.trans
  have equal : (1/(2*(k:ℝ)*d))*M^2+(M:ℝ)*((M:ℝ)/(2*k*d))=(1/((k:ℝ)*d))*M^2 := by ring
  linarith only [error,endpoint,equal]



/-- The true first and second moments for constant cell weights give
concentration around the actual number of constructor marks. -/
theorem target_class_score_error (line : DirichletLZerosOnLine) (k : ℕ) (kp : 0<k) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (r : ℕ), let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ r [MOD ell])
    let M := 2*(cellMarkCount b:ℝ)/ell; let f := fun a=>(smoothMarkProbability R T a)⁻¹
    let E := smoothMarkEvent R false; let F := smoothMarkEvent T true
    let μ := twoFieldMean R T X f E F
    μ=X.card ∧ (twoFieldSecond R T X f E F-2*(X.card:ℝ)*μ+(X.card:ℝ)^2)/(M:ℝ)^2 ≤ 1/((k:ℝ)*Fixed.d b) := by
  obtain ⟨b₁,cov⟩ := target_class_covariance line k kp
  obtain ⟨b₂,margin⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell R T b huge hn comp target absent cell r X M f E F μ
  obtain ⟨large,big⟩ := max_le_iff.mp huge
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    have mark := (mem_filter.mp (mem_filter.mp ha).1).2
    have floor : 0<8/(Fixed.B b:ℝ) := by dsimp [Fixed.B]; positivity
    have each (S : PrescribedRows n ell) (s : Bool) :
        0<prescribedProbability S s (smoothMarkEvent S s a) :=
      (floor.trans_le (margin S big hn comp target absent mark s)).trans_eq
        (probability_congr S s _ (smoothMarkEvent S s a) rfl)
    exact mul_pos (each R false) (each T true)
  have mean : μ=X.card := by
    change (∑ a∈X, f a*smoothMarkProbability R T a)=(X.card:ℝ)
    calc _ = ∑ _a∈X,(1:ℝ) := sum_congr rfl (fun a ha => inv_mul_cancel₀ (pos a ha).ne')
         _ = _ := by simp
  refine ⟨mean,?_⟩
  have decomp := twoField_covariance_identity R T X f E F (X.card:ℝ)
  change twoFieldSecond R T X f E F-2*(X.card:ℝ)*μ+(X.card:ℝ)^2 =
    (μ-(X.card:ℝ))^2+∑ i∈X,∑ j∈X, (f i*f j)*twoFieldIndicatorCovariance R T E F i j at decomp
  rw [mean,sub_self,zero_pow (by decide : 2≠0),zero_add] at decomp
  rw [mean,decomp]
  have norm (i j : ℕ) : f i*f j*twoFieldIndicatorCovariance R T E F i j=normalizedSmoothCovariance R T i j := by
    unfold normalizedSmoothCovariance
    dsimp only [f,E,F]
    rw [div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [norm]
  exact cov R T large hn comp target absent cell r


/-- For a family of at most four times the degree plus four prescribed
classes, a single nonnegative test of arbitrarily small expected cost
certifies all the retained count bounds on any boxed draw passing it. -/
theorem target_class_count_test (line : DirichletLZerosOnLine) (k : ℕ) (hk : 0<k) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (I : Type*) [Fintype I] [Nonempty I], Fintype.card I≤4*Fixed.d b+4 →
    ∀ (cell : I → Option (Bool×Fin (Fixed.d b))) (residue : I → ℕ),
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ (test : Ω→ℝ) (μ : ℝ), (∀ t,0≤test t) ∧ HasSum (fun t=>twoFieldWeight O O t*test t) μ ∧ μ≤1/(k:ℝ) ∧
      ∀ t : Ω, let u := t.1.val; let v := t.2.val
        inCoefficientBox n u → inCoefficientBox n v → test t<1 →
        ∃ rel : Marking.Relations,
          Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
          ∀ i, let Y := (constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ residue i [MOD ell] ∧ a∈rel.marks)
            4*(cellMarkCount b:ℝ) ≤ (ell:ℝ)*(Fixed.B b:ℝ)^2*Y.card := by
  classical
  obtain ⟨b₁,count⟩ := target_class_score_error line (262144*k) (Nat.mul_pos (by decide) hk)
  obtain ⟨n₂,marks⟩ := grid_cells_have_marks line
  obtain ⟨b₃,grows⟩ := Fixed.degree_grows 10004
  obtain ⟨b₄,deleted⟩ := rejected_score_loss line 2 (by norm_num)
  obtain ⟨b₅,tiny⟩ := fixed_class_accuracy (2048*(k:ℝ))
  obtain ⟨b₆,floor⟩ := PrescribedRows.smooth_probability_margin line
  let threshold := max (max b₁ b₆) (max b₃ (max 1000 (max b₄ b₅)))
  refine ⟨max n₂ (max 2 (2^threshold)),?_⟩
  intro n large ell target comp absent b I _ _ num cell residue
  obtain ⟨old,h₀⟩ := max_le_iff.mp large
  obtain ⟨hn,hb⟩ := max_le_iff.mp h₀
  have huge : threshold≤b := ((Nat.le_log2 (by omega : n≠0)).mpr hb).trans (Nat.le_succ _)
  obtain ⟨both,rest⟩ := max_le_iff.mp huge
  obtain ⟨one,six⟩ := max_le_iff.mp both
  obtain ⟨three,rest⟩ := max_le_iff.mp rest
  obtain ⟨big,rest⟩ := max_le_iff.mp rest
  obtain ⟨four,five⟩ := max_le_iff.mp rest
  let d := Fixed.d b
  let R := PrescribedRows.unrestricted n ell
  let T := R
  have cop (a : ℕ) : (R.prefactor a false).Coprime (T.prefactor a true) :=
    (R.prefactors_coprime_iff T ((by decide : 3≤10004).trans (grows b three)) target a).mpr
      (by simp [R,T,PrescribedRows.unrestricted,PrescribedRows.hit])
  have ep := (mem_dyadicTargets.mp target).1
  have ep' : 0<(ell:ℝ) := by exact_mod_cast ep.pos
  let X (c : I) := (constructorCellMarks n ell (cell c)).filter (fun a=>a ≡ residue c [MOD ell])
  let M : ℝ := 2*(cellMarkCount b:ℝ)/ell; let B : ℝ := Fixed.B b
  let p := smoothMarkProbability R T; let w := fun a=>(p a)⁻¹
  let E := smoothMarkEvent R false; let F := smoothMarkEvent T true
  let m (c : I) := ((X c).card:ℝ)
  let cost (c : I) := twoFieldSecond R T (X c) w E F-2*m c*twoFieldMean R T (X c) w E F+(m c)^2
  have dp : 0<(d:ℝ) := by exact_mod_cast Fixed.degree_pos (Nat.succ_pos n.log2)
  have dn : 1≤(d:ℝ) := by dsimp only [d]; exact_mod_cast Fixed.degree_pos (Nat.succ_pos n.log2)
  have mp : 0<M := by dsimp [M,cellMarkCount]; positivity
  have bp : 2≤B := by
    dsimp only [B]; exact_mod_cast (show 2^1≤Fixed.B b from Nat.pow_le_pow_right (by decide)
      (show 1≤1000*Fixed.h b by
        have := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos n.log2)) (Nat.succ_pos b.log2)
        change 0<Fixed.h b at this; omega))
  let Ω := R.CoeffPoint false×T.CoeffPoint true
  let W := twoFieldWeight R T
  let s (c : I) (t : Ω) := twoFieldScore (X c) w E F t.1.val t.2.val
  let loss (c : I) (t : Ω) := ∑ a∈X c, if rejectedSmoothMark R T a t.1.val t.2.val then w a else 0
  let fc (c : I) (t : Ω) := (s c t-m c)^2/(M/64)^2+loss c t/(M/64)
  let z : ℝ := Fixed.z b
  let e := exp (-2*z^2)
  have entry (c : I) : cost c/(M/64)^2≤4096/(262144*(k:ℝ)*d) := by
    have bound := (count R T one hn comp target absent (cell c) (residue c)).2
    push_cast at bound
    change cost c/M^2≤1/(262144*(k:ℝ)*d) at bound
    exact (show cost c/(M/64)^2=4096*(cost c/M^2) by ring).le.trans
      ((mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ)≤4096)).trans_eq (by ring))
  have terms (c : I) : ∃ ξ, HasSum (fun t:Ω => W t*fc c t) ξ ∧ ξ≤4096/(262144*(k:ℝ)*d)+64*e := by
    obtain ⟨μ,h,ub⟩ := deleted R T four hn comp target absent (X c) (fun _=>1)
      (fun a ha=>(mem_filter.mp (mem_filter.mp ha).1).2) (fun a _=>cop a)
    simp only [abs_one,one_div,sum_const,nsmul_one] at h ub
    have xs : ((X c).card:ℝ)≤M := target_class_card target (cell c) (residue c)
    have du : μ/(M/64)≤64*e := (div_le_iff₀ (by positivity : 0<M/64)).mpr
      ((ub.trans (mul_le_mul_of_nonneg_left xs (exp_pos _).le)).trans_eq (by ring))
    refine ⟨cost c/(M/64)^2+μ/(M/64),?_,add_le_add (entry c) du⟩
    have h₁ := (twoField_score_error R T target (X c) w E F (m c)).div_const ((M/64)^2)
    apply (h₁.add (h.div_const (M/64))).congr_fun
    intro t
    change W t*((s c t-m c)^2/(M/64)^2+loss c t/(M/64))=W t*(s c t-m c)^2/(M/64)^2+W t*loss c t/(M/64)
    ring
  choose ξ ex up using terms
  have sum := sum_le_sum (s:=(univ : Finset I)) (fun c _=>up c)
  rw [sum_const,card_univ,nsmul_eq_mul] at sum
  have fcard : (Fintype.card I:ℝ) ≤ 4*d+4 := by exact_mod_cast num
  have z1 : 1≤z := by dsimp [z,Fixed.z]; exact_mod_cast Nat.le_add_left 1 b.log2
  have dz : (d:ℝ)≤exp (z^2) := calc
    _ ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Fixed.degree_le_bits b).trans Nat.lt_log2_self.le
    _ = exp ((Fixed.z b:ℝ)*log 2) := by rw [←rpow_natCast,rpow_def_of_pos (by norm_num : (0:ℝ)<2),mul_comm]
    _ ≤ _ := by apply exp_le_exp.mpr; change z*log 2≤z^2
                nlinarith only [mul_nonneg (sub_nonneg.mpr z1) (zero_le_one.trans z1),
                  mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)) (zero_le_one.trans z1)]
  have kp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have smallD : (4*(d:ℝ)+4)*(64*e)≤1/(2*(k:ℝ)) := by
    have le := mul_le_mul_of_nonneg_right dz (exp_pos (-2*z^2)).le
    rw [←exp_add,show z^2+ -2*z^2= -z^2 by ring] at le
    have ad := mul_le_mul_of_nonneg_right dn (exp_pos (-2*z^2)).le
    have h : (4*(d:ℝ)+4)*(64*e)≤512*exp (-z^2) := by
      dsimp only [e];linarith only [le,ad]
    apply h.trans
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [tiny b five]
  have smallC : (4*(d:ℝ)+4)*(4096/(262144*(k:ℝ)*d))≤1/(2*(k:ℝ)) := by
    rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left dn kp.le,kp]
  have unionBound := sum.trans (mul_le_mul_of_nonneg_right fcard (by positivity))
  have total : (∑ c:I, ξ c)≤1/(k:ℝ) := unionBound.trans (by
    rw [mul_add,show 1/(k:ℝ)=1/(2*(k:ℝ))+1/(2*(k:ℝ)) by ring];exact add_le_add smallC smallD)
  have pw0 (a) : 0≤w a := inv_nonneg.mpr (mul_nonneg (R.probability_unit target false _).1 (T.probability_unit target true _).1)
  have l0 (c t) : 0≤loss c t := sum_nonneg (fun a _=>by split <;> first | exact pw0 a | rfl)
  have f0 (c t) : 0≤fc c t := add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg (l0 c t) (by positivity))
  refine ⟨fun t=>∑ c:I,fc c t,∑ c:I,ξ c,fun t=>sum_nonneg (fun c _=>f0 c t),?_,total,?_⟩
  · exact (hasSum_sum (s:=(univ:Finset I)) (fun c _=>ex c)).congr_fun (fun t=>mul_sum ..)
  intro t u v bu bv cheap
  let stage := Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))
  let retained (a : ℕ) := ∃ rel,stage=some rel ∧ a∈rel.marks
  let yes (a : ℕ) := E a u ∧ F a v ∧ retained a
  have lower (c : I) : 2*M ≤ B^2*((X c).filter yes).card := by
    let hits := (X c).filter yes
    have result := (single_le_sum (s:=(univ:Finset I)) (f:=fun i=>fc i t) (fun i _=>f0 i t) (mem_univ c)).trans_lt cheap
    have scoreSmall : (s c t-m c)^2/(M/64)^2<1 :=
      (le_add_of_nonneg_right (div_nonneg (l0 c t) (by positivity))).trans_lt result
    have lossSmall : loss c t/(M/64)<1 := (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))).trans_lt result
    have near := (abs_lt.mp ((sq_lt_sq₀ (abs_nonneg _) (by positivity : 0≤M/64)).mp
      (by rw [sq_abs]; exact (div_lt_one (sq_pos_of_pos (by positivity))).mp scoreSmall))).1
    have lossCap := (div_lt_one (by positivity)).mp lossSmall
    have eB : ell≤Fixed.B b := (mem_dyadicTargets.mp target).2.2
    have e4 : ell≤(Fixed.B b)^4 := eB.trans (Nat.le_self_pow (by decide) _)
    have gc := marks n old ell target comp absent ell (residue c) 0 0 0 0 (cell c) ep.pos e4 (by
      intro p hp dvd
      have ne := (markModulus_spec hn (grows b three) comp target absent).2.2.2 p hp
      exact (ne.2 (((Nat.dvd_prime ep).mp dvd).resolve_left (Nat.prime_of_mem_primeFactors hp).ne_one)).elim)
    have classes : ((Ico (firstCellMark b (cell c)) (firstCellMark b (cell c)+cellMarkCount b)).filter
      (fun a=>a ≡ residue c [MOD ell])).filter (fun a=>a∈(construct n ell 0 0 0 0).marks)=X c := by
      ext a; simp [X,constructorCellMarks,and_comm,and_left_comm,b]
    dsimp only at gc
    rw [classes] at gc
    have lowerMean : M/16 ≤ m c := by
      change (cellMarkCount b:ℝ)/ell/8 ≤ m c at gc
      exact (by dsimp only [M]; ring : M/16=(cellMarkCount b:ℝ)/ell/8).le.trans gc
    have floorAt (a) (ha : a∈X c) (S : PrescribedRows n ell) (s : Bool) :
        8/B ≤ prescribedProbability S s (smoothMarkEvent S s a) :=
      (floor S six hn comp target absent (mem_filter.mp (mem_filter.mp ha).1).2 s).trans_eq
        (probability_congr S s _ (smoothMarkEvent S s a) rfl)
    have pw (a) (ha : a∈X c) : w a≤B^2/64 := by
      have bpos : 0<B := by linarith
      have lb : (0:ℝ)<8/B := by positivity
      have main : (8/B)*(8/B)≤p a := mul_le_mul (floorAt a ha R false) (floorAt a ha T true) lb.le
        (lb.trans_le (floorAt a ha R false)).le
      exact (inv_anti₀ (mul_pos lb lb) main).trans_eq (by field_simp; ring)
    have eq : s c t = (∑ a∈hits,w a)+loss c t := by
      change (∑ a∈X c,w a*(if E a u ∧ F a v then 1 else 0))=_
      dsimp only [hits,loss]
      rw [sum_filter (p:=yes),←sum_add_distrib]
      apply sum_congr rfl; intro a _
      change _ = (if yes a then w a else 0)+(if rejectedSmoothMark R T a u v then w a else 0)
      have rej : rejectedSmoothMark R T a u v ↔ E a u ∧ F a v ∧ ¬retained a := by
        simp only [rejectedSmoothMark,E,F,retained,stage,bu,bv,true_and,u,v]
      by_cases h : E a u ∧ F a v <;> by_cases r : retained a <;> simp_all only [yes,
        and_true,and_false,not_true_eq_false,not_false_eq_true,if_true,if_false,mul_one,mul_zero,zero_add,add_zero]
    have upper := sum_le_sum (s:=hits) (fun a h=>pw a (mem_filter.mp h).1)
    rw [sum_const,nsmul_eq_mul] at upper
    change 2*M≤B^2*(hits.card:ℝ)
    linarith only [near,lowerMean,upper,lossCap,eq]
  cases hs : stage with
  | none =>
    have no (a : ℕ) : ¬yes a := fun h=>by obtain ⟨_,hh,_⟩ := h.2.2; simp [hs] at hh
    have contradiction := lower (Classical.arbitrary I)
    simp [no] at contradiction; linarith
  | some rel =>
    refine ⟨rel,hs,?_⟩
    intro c Y
    have sub : (X c).filter yes ⊆ Y := by
      intro a mem
      obtain ⟨am,_,_,rr,hh,hr⟩ := mem_filter.mp mem
      cases Option.some.inj (hh.symm.trans hs)
      exact mem_filter.mpr ⟨(mem_filter.mp am).1,(mem_filter.mp am).2,hr⟩
    have q := (lower c).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card sub)) (sq_nonneg _))
    have eq : 2*M*(ell:ℝ)=4*(cellMarkCount b:ℝ) := by dsimp only [M]; field_simp; ring
    change 4*(cellMarkCount b:ℝ)≤(ell:ℝ)*B^2*Y.card
    linarith only [mul_le_mul_of_nonneg_right q ep'.le,eq]

/-- A single positive coefficient tuple realizes every prescribed cell and target
residue in any family of at most four times the degree plus four constraints. -/
theorem simultaneous_target_class_counts (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (I : Type*) [Fintype I] [Nonempty I], Fintype.card I≤4*Fixed.d b+4 →
    ∀ (cell : I → Option (Bool×Fin (Fixed.d b))) (residue : I → ℕ),
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), inCoefficientBox n u ∧ inCoefficientBox n v ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
      ∀ i, let Y := (constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ residue i [MOD ell] ∧ a∈rel.marks)
      4*(cellMarkCount b:ℝ) ≤ (ell:ℝ)*(Fixed.B b:ℝ)^2*Y.card := by
  obtain ⟨n₀,test⟩ := target_class_count_test line 2 (by decide)
  refine ⟨max n₀ (2^1000),?_⟩
  intro n large ell target comp absent b I _ _ count cell residue
  obtain ⟨old,lim⟩ := max_le_iff.mp large
  have powpos : 0<(2:ℕ)^1000 := pow_pos (by decide : 0<(2:ℕ)) _
  have big : 1000≤b := ((Nat.le_log2 ((powpos.trans_le lim).ne')).mpr lim).trans (Nat.le_succ _)
  let O := PrescribedRows.unrestricted n ell
  obtain ⟨f,μ,nonneg,law,rate,passes⟩ := test n old ell target comp absent I count cell residue
  have tail := coefficient_tail_lt_half_mark (b:=b) big
  have hp := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos n.log2)) (Nat.succ_pos b.log2)
  have bpos : 0<1000*Fixed.h b := Nat.mul_pos (by decide) hp
  have B2 : (2:ℝ)≤Fixed.B b := Nat.cast_le.mpr (Nat.succ_le_of_lt (Nat.one_lt_pow bpos.ne' (by decide : 1<2)))
  have half : 1/(2*(Fixed.B b:ℝ))≤1/4 := by
    rw [div_le_div_iff₀ (by linarith only [B2]) (by norm_num)];linarith only [B2]
  have enough : μ+2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 := by
    norm_num at rate;linarith only [rate,tail,half]
  obtain ⟨t,bu,bv,cheap⟩ := twoField_box_of_cost O O target f μ nonneg law enough
  obtain ⟨rel,stage,supply⟩ := passes t bu bv cheap
  exact ⟨t.1.val,t.2.val,rel,bu,bv,stage,supply⟩

/-- A single positive coefficient tuple realizes every prescribed cell and target
residue in any family of at most four times the degree plus four constraints. -/
theorem simultaneous_target_cells (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (I : Type*) [Fintype I] [Nonempty I], Fintype.card I≤4*Fixed.d b+4 →
    ∀ (cell : I → Option (Bool×Fin (Fixed.d b))) (residue : I → ℕ),
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), inCoefficientBox n u ∧ inCoefficientBox n v ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
      ∀ i, ∃ a∈constructorCellMarks n ell (cell i), a ≡ residue i [MOD ell] ∧ a∈rel.marks := by
  obtain ⟨n₀,supply⟩ := simultaneous_target_class_counts line
  refine ⟨n₀,?_⟩
  intro n big ell target comp absent b I _ _ size cell residue
  obtain ⟨u,v,rel,bu,bv,stage,counts⟩ := supply n big ell target comp absent I size cell residue
  refine ⟨u,v,rel,bu,bv,stage,?_⟩
  intro i
  let Y := (constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ residue i [MOD ell] ∧ a∈rel.marks)
  have pos : Y.Nonempty := by
    by_contra! he
    have count := counts i
    change 4*(cellMarkCount b:ℝ) ≤ _*Y.card at count
    rw [he,card_empty,Nat.cast_zero,mul_zero] at count
    have mp : (0:ℝ)<cellMarkCount b := by dsimp [cellMarkCount]; positivity
    linarith
  obtain ⟨a,mem⟩ := pos
  exact ⟨a,(mem_filter.mp mem).1,(mem_filter.mp mem).2⟩

/-- The ordinary valuation rows restricted to a specified set of natural marks. -/
def ordinaryMarkMatrix (rel : Marking.Relations) (Y : Finset ℕ) :
    Matrix {i : Fin rel.rows.length // (rel.rows.get i).q ≠ rel.target} Y ℚ :=
  fun i a => if a.val%(rel.rows.get i.val).q=(rel.rows.get i.val).r then 1 else 0

/-- On one residue of the target prime, the ordinary rows alone distinguish
the actual columns: the intercept and every target row are constant there. -/
theorem ordinary_rank_on_target_class (rel : Marking.Relations) (Y : Finset ℕ) (r : ℕ)
    (retained : ∀ a∈Y, a∈rel.marks ∧ a%rel.target=r)
    (inj : Function.Injective (rel.matrix.map (Int.castRingHom ℚ)).col) :
    Y.card≤2^(ordinaryMarkMatrix rel Y).rank := by
  classical
  choose ix hix using fun a : Y => List.mem_iff_get.mp (retained a a.property).1
  let A := ordinaryMarkMatrix rel Y
  obtain ⟨code,complete⟩ := binary_row_signatures A (by intro i j; unfold A ordinaryMarkMatrix; split <;> simp)
  have unique : Function.Injective code := by
    intro a b he
    have full : (rel.matrix.map (Int.castRingHom ℚ)).col (ix a) = (rel.matrix.map (Int.castRingHom ℚ)).col (ix b) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ j =>
        change (↑(if rel.marks.get (ix a)%(rel.rows.get j).q=(rel.rows.get j).r then (1:ℤ) else 0):ℚ)=
          (↑(if rel.marks.get (ix b)%(rel.rows.get j).q=(rel.rows.get j).r then (1:ℤ) else 0):ℚ)
        rw [hix,hix]
        by_cases target : (rel.rows.get j).q=rel.target
        · rw [target,(retained a a.property).2,(retained b b.property).2]
        · simpa [A,ordinaryMarkMatrix,apply_ite] using complete a b he ⟨j,target⟩
    have same := congrArg rel.marks.get (inj full)
    exact Subtype.ext (by simpa only [hix] using same)
  simpa only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,A] using Fintype.card_le_of_injective code unique

/-- Every constructor cell has a retained mark on the common off-target
residue, and the baseline cell also represents every prescribed target root.
All these marks are in the same executable relation matrix. -/
theorem protected_target_cells (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let m := Fixed.rootBase n
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), inCoefficientBox n u ∧ inCoefficientBox n v ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
      (∀ c : Option (Bool×Fin (Fixed.d b)), ∃ a∈constructorCellMarks n ell c, a∈rel.marks ∧ a%ell=m%ell) ∧
      (∀ r∈wanted (Fixed.d b) ell m, ∃ a∈constructorCellMarks n ell none, a∈rel.marks ∧ a%ell=r) := by
  obtain ⟨n₀,supply⟩ := simultaneous_target_cells line
  refine ⟨n₀,?_⟩
  intro n large ell target comp absent b m
  let d := Fixed.d b
  let C := Option (Bool×Fin d)
  let I := C ⊕ Fin d
  let roots := wanted d ell m
  have spec := wanted_spec (target_gt_degree target) m
  have len : roots.length=d := spec.1
  let row (i : Fin d) := roots.get ⟨i.val,len.symm ▸ i.isLt⟩
  let c : I→C := Sum.elim id (fun _=>none)
  let r : I→ℕ := Sum.elim (fun _=>m) row
  have bound : Fintype.card I≤4*Fixed.d b+4 := by simp [I,C,d]; omega
  obtain ⟨u,v,rel,bu,bv,stage,hit⟩ := supply n large ell target comp absent I bound c r
  refine ⟨u,v,rel,bu,bv,stage,fun i=>?_,fun z hz=>?_⟩
  · obtain ⟨a,am,ar,arr⟩ := hit (.inl i)
    exact ⟨a,am,arr,ar⟩
  · obtain ⟨i,eq⟩ := List.mem_iff_get.mp hz
    let j : Fin d := ⟨i.val,len ▸ i.isLt⟩
    obtain ⟨a,am,ar,arr⟩ := hit (.inr j)
    have eq' : row j=z := eq
    change a%ell = row j%ell at ar
    exact ⟨a,am,arr,ar.trans (by rw [eq',Nat.mod_eq_of_lt ((spec.2.2 z hz).1)])⟩

/-- Every constructor cell has a retained mark on the common off-target
residue, and the baseline cell also represents every prescribed target root.
All these marks are in the same executable relation matrix. -/
theorem protected_target_cells_rank (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let m := Fixed.rootBase n
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), inCoefficientBox n u ∧ inCoefficientBox n v ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
      (∀ c : Option (Bool×Fin (Fixed.d b)), ∃ a∈constructorCellMarks n ell c, a∈rel.marks ∧ a%ell=m%ell) ∧
      (∀ r∈wanted (Fixed.d b) ell m, ∃ a∈constructorCellMarks n ell none, a∈rel.marks ∧ a%ell=r) ∧
      (4*(cellMarkCount b:ℝ) ≤ (ell:ℝ)*(Fixed.B b:ℝ)^2*
        ((constructorCellMarks n ell none).filter (fun a=>a%ell=m%ell ∧ a∈rel.marks)).card) ∧
      6997*Fixed.h b+2 ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank ∧
      6997*Fixed.h b+2 ≤ (ordinaryMarkMatrix rel ((constructorCellMarks n ell none).filter
        (fun a=>a%ell=m%ell ∧ a∈rel.marks))).rank := by
  obtain ⟨n₀,supply⟩ := simultaneous_target_class_counts line
  obtain ⟨b₀,grows⟩ := Fixed.degree_grows 10004
  refine ⟨max n₀ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b m
  obtain ⟨old,h₀⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp h₀
  have big : b₀≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  let d := Fixed.d b
  let C := Option (Bool×Fin d)
  let I := C ⊕ Fin d
  let roots := wanted d ell m
  have spec := wanted_spec (target_gt_degree target) m
  have len : roots.length=d := spec.1
  let row (i : Fin d) := roots.get ⟨i.val,len.symm ▸ i.isLt⟩
  let c : I→C := Sum.elim id (fun _=>none)
  let r : I→ℕ := Sum.elim (fun _=>m) row
  have bound : Fintype.card I≤4*Fixed.d b+4 := by simp [I,C,d]; omega
  obtain ⟨u,v,rel,bu,bv,stage,counts⟩ := supply n old ell target comp absent I bound c r
  have hit (i : I) : ∃ a∈constructorCellMarks n ell (c i), a ≡ r i [MOD ell] ∧ a∈rel.marks := by
    let Y := (constructorCellMarks n ell (c i)).filter (fun a=>a ≡ r i [MOD ell] ∧ a∈rel.marks)
    have nonempty : Y.Nonempty := by
      by_contra! he
      have count := counts i
      change 4*(cellMarkCount b:ℝ)≤_*Y.card at count
      rw [he,card_empty,Nat.cast_zero,mul_zero] at count
      have mp : (0:ℝ)<cellMarkCount b := by dsimp [cellMarkCount]; positivity
      linarith
    obtain ⟨a,am⟩ := nonempty
    exact ⟨a,(mem_filter.mp am).1,(mem_filter.mp am).2⟩
  let Y := (constructorCellMarks n ell none).filter (fun a=>a%ell=m%ell ∧ a∈rel.marks)
  have cnt : 4*cellMarkCount b ≤ ell*(Fixed.B b)^2*Y.card := by
    have h := counts (.inl none)
    change 4*(cellMarkCount b:ℝ) ≤ (ell:ℝ)*(Fixed.B b:ℝ)^2*Y.card at h
    exact_mod_cast h
  have mem : Y ⊆ rel.marks.toFinset := fun a ha=>List.mem_toFinset.mpr (mem_filter.mp ha).2.2
  have lenN := (card_le_card mem).trans (List.toFinset_card_le rel.marks)
  have ub : u.1.toNat≤2*b^2*Fixed.U b*Fixed.A b := Int.toNat_le.mpr (by exact_mod_cast bu.2.1)
  have vb : u.2.toNat≤2*b^2*Fixed.U b := Int.toNat_le.mpr (by exact_mod_cast bu.2.2.2)
  have inj := constructed_columns_injective hn (grows b big) target ⟨ub,vb⟩ stage
  have full := lenN.trans (retained_rank_of_column_separation rel inj)
  have targetEq : rel.target=ell := (Marking.rows_and_guards stage).2.2.1
  have ordinary := ordinary_rank_on_target_class rel Y (m%ell) (fun a am=>
    ⟨(mem_filter.mp am).2.2, by rw [targetEq]; exact (mem_filter.mp am).2.1⟩) inj
  have eB : ell≤Fixed.B b := (mem_dyadicTargets.mp target).2.2
  have rankLower (rk : ℕ) (card : Y.card≤2^rk) : 6997*Fixed.h b+2≤rk := by
    have power : 2^(2+9997*Fixed.h b) ≤ 2^(3000*Fixed.h b+rk) := calc
      _ = 4*cellMarkCount b := by rw [pow_add]; rfl
      _ ≤ ell*(Fixed.B b)^2*Y.card := cnt
      _ ≤ Fixed.B b*(Fixed.B b)^2*2^rk := Nat.mul_le_mul (Nat.mul_le_mul_right _ eB) card
      _ = _ := by change 2^(1000*Fixed.h b)*(2^(1000*Fixed.h b))^2 * 2^rk = _; rw [←pow_mul,←pow_add,←pow_add]; congr 1; omega
    have exponent := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp power
    omega
  refine ⟨u,v,rel,bu,bv,stage,fun i=>?_,fun z hz=>?_,counts (.inl none),rankLower _ full,rankLower _ ordinary⟩
  · obtain ⟨a,am,ar,arr⟩ := hit (.inl i)
    exact ⟨a,am,arr,ar⟩
  · obtain ⟨i,eq⟩ := List.mem_iff_get.mp hz
    let j : Fin d := ⟨i.val,len ▸ i.isLt⟩
    obtain ⟨a,am,ar,arr⟩ := hit (.inr j)
    have eq' : row j=z := eq
    change a%ell = row j%ell at ar
    exact ⟨a,am,arr,ar.trans (by rw [eq',Nat.mod_eq_of_lt ((spec.2.2 z hz).1)])⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.simultaneous_target_cells

#print axioms Cogentic.Construction.protected_target_cells

#print axioms Cogentic.Construction.protected_target_cells_rank
