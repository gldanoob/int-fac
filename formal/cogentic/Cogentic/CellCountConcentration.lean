import Cogentic.PairVarianceTransfer
import Cogentic.RetainedScoreLoss
import Cogentic.RetainedNullity
import Mathlib.NumberTheory.Chebyshev

namespace Cogentic.Construction
open Finset Real Filter Cogentic.Window
open scoped Classical

/-- The inverse-square mass of arbitrary primes above a degree cutoff.
Chebyshev's count is applied on successive doubling intervals. -/
theorem prime_inverse_squares_tail :
    ∃ d₀ : ℕ, ∀ d≥d₀, ∀ P : Finset ℕ, (∀ p∈P, p.Prime ∧ d<p) →
      (∑ p∈P, ((p:ℝ)⁻¹)^2) ≤ 12/((d:ℝ)*log d) := by
  obtain ⟨x₀,h⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (ε:=1) zero_lt_one)
  obtain ⟨n₀,large⟩ := exists_nat_ge x₀
  refine ⟨max 2 n₀,?_⟩
  intro d hd P prime
  have log4 : log 4+1≤3 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have dyad (k : ℕ) : ∀ a≥d, ∀ Q : Finset ℕ,
      (∀ p∈Q, p.Prime ∧ a<p ∧ p≤2^k*a) →
      (∑ p∈Q, ((p:ℝ)⁻¹)^2) ≤ 12/((a:ℝ)*log d) := by
    have d2 := (le_max_left ..).trans hd
    have ld : 0<log d := log_pos (by exact_mod_cast (by omega : 1<d))
    induction k with
    | zero =>
      intro a da Q small
      have empty : Q=∅ := eq_empty_iff_forall_notMem.mpr (fun p pm => by
        obtain ⟨_,l,r⟩ := small p pm
        simp only [pow_zero,one_mul] at r; omega)
      simp [empty]
      positivity
    | succ k ih =>
      intro a ad Q small
      let F := Q.filter (·≤2*a)
      let G := Q.filter (fun p=>¬p≤2*a)
      have partition : F∪G=Q := by ext p; by_cases hp : p≤2*a <;> simp [F,G,hp,lt_of_not_ge]
      have disj : Disjoint F G := disjoint_left.mpr (fun _ h h' => (mem_filter.mp h').2 (mem_filter.mp h).2)
      have ap : 0<(a:ℝ) := by exact_mod_cast (by omega : 0<a)
      have two : (d:ℝ)≤2*a := by exact_mod_cast (by omega : d≤2*a)
      have log2a : log (d:ℝ)≤log (2*(a:ℝ)) := log_le_log (by positivity) two
      have ceil := h (2*(a:ℝ)) (large.trans (by exact_mod_cast (by omega : n₀≤2*a)))
      rw [show 2*(a:ℝ)=((2*a:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast] at ceil
      have card : F.card≤(2*a).primeCounting := by
        rw [←Nat.primesLE_card_eq_primeCounting]
        exact card_le_card (fun p hp=>Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2,(small p (mem_filter.mp hp).1).1⟩)
      have upper : (F.card:ℝ)≤6*a/log d := calc
        _ ≤ ((2*a).primeCounting:ℝ) := by exact_mod_cast card
        _ ≤ _ := ceil
        _ ≤ _ := by
          push_cast
          apply div_le_div₀ _ _ ld log2a
          · positivity
          · linarith only [mul_le_mul_of_nonneg_right log4 (by positivity : (0:ℝ)≤2*a)]
      have first : (∑ p∈F, ((p:ℝ)⁻¹)^2)≤6/((a:ℝ)*log d) := calc
        _ ≤ ∑ _p∈F, ((a:ℝ)⁻¹)^2 := sum_le_sum (fun p hp => by
          have pa : (a:ℝ)≤p := by exact_mod_cast (small p (mem_filter.mp hp).1).2.1.le
          exact pow_le_pow_left₀ (by positivity) (inv_anti₀ ap pa) 2)
        _ = (F.card:ℝ)*(a:ℝ)⁻¹^2 := by simp
        _ ≤ (6*a/log d)*(a:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right upper (sq_nonneg _)
        _ = _ := by field_simp
      have last := ih (2*a) (by omega) G (fun p hp=>by
        obtain ⟨mem,lt⟩ := mem_filter.mp hp
        obtain ⟨pr,_,up⟩ := small p mem
        exact ⟨pr,by omega,by simpa only [pow_succ,Nat.mul_assoc] using up⟩)
      rw [←partition,sum_union disj]
      refine (add_le_add first last).trans_eq ?_
      push_cast
      ring
  let k := P.sup id
  exact dyad k d le_rfl P (fun p hp => ⟨(prime p hp).1,(prime p hp).2,
    (le_sup (f:=id) hp).trans (Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (by omega)))⟩)

/-- The nonempty divisors in the pair correction have mass o(1/d);
this sharper bound allows summation over all 2d+1 grid cells. -/
theorem pair_weight_inverse_prime_bound :
    ∃ d₀ : ℕ, ∀ d≥d₀, ∀ P : Finset ℕ, (∀ p∈P, p.Prime ∧ d<p) →
      (∑ T∈P.powerset, pairDivisorWeight T/(sieveProduct T:ℝ)) ≤ exp (96/((d:ℝ)*log d)) := by
  obtain ⟨d₀,tail⟩ := prime_inverse_squares_tail
  refine ⟨d₀,?_⟩
  intro d hd P pr
  let e := fun p : ℕ => (2*(p:ℝ)-1)/((p:ℝ)-1)^2
  have eq (T : Finset ℕ) : pairDivisorWeight T/(sieveProduct T:ℝ)=∏ p∈T,e p/(p:ℝ) := by
    simp [pairDivisorWeight,sieveProduct,e,prod_div_distrib]
  have eta (p) (hp : p∈P) : 0≤e p/(p:ℝ) ∧ e p/(p:ℝ)≤8*((p:ℝ)⁻¹)^2 := by
    have p2 : (2:ℝ)≤p := by exact_mod_cast (pr p hp).1.two_le
    have pp : (0:ℝ)<p := by linarith
    have bound : e p≤8/(p:ℝ) := (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) pp).mpr
      (by nlinarith only [sq_nonneg ((p:ℝ)-2),p2])
    exact ⟨div_nonneg (div_nonneg (by linarith) (sq_nonneg _)) pp.le,
      (div_le_div_of_nonneg_right bound pp.le).trans_eq (by ring)⟩
  simp_rw [eq]; rw [←prod_one_add]
  refine (prod_le_prod (fun p h => by linarith [(eta p h).1]) (fun p h => show 1+e p/(p:ℝ) ≤ exp (8*((p:ℝ)⁻¹)^2) by
    linarith only [(eta p h).2,add_one_le_exp (8*((p:ℝ)⁻¹)^2)])).trans ?_
  rw [←exp_sum,←mul_sum,exp_le_exp]
  exact (mul_le_mul_of_nonneg_left (tail d hd P pr) (by norm_num : (0:ℝ)≤8)).trans_eq (by ring)

/-- The empty divisor contributes exactly one. Every remaining divisor
costs one interval congruence, regardless of any sieve imposed on Y. -/
theorem pair_gamma_row_excess (P Y : Finset ℕ) (pr : ∀ p∈P,p.Prime)
    (m x lo M : ℕ) (interval : Y⊆Ico lo (lo+M)) :
    (∑ y∈Y,((pairGamma P m x y)^2-1)) ≤
      (M:ℝ)*((∑ T∈P.powerset,pairDivisorWeight T/(sieveProduct T:ℝ))-1)+
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
        (M:ℝ)*(pairDivisorWeight T/(sieveProduct T:ℝ))+pairDivisorWeight T := by
    let q := sieveProduct T
    have sub := mem_powerset.mp (mem_of_mem_erase member)
    have qp : 0<q := prod_pos (fun p hp => (pr p (sub hp)).pos)
    let ys := (Ico lo (lo+M)).filter (fun y => y ≡ x [MOD q])
    have ysub : (Y.filter (hit T))⊆ys :=
      fun y h => mem_filter.mpr ⟨interval (mem_filter.mp h).1,(mem_filter.mp h).2.1.symm⟩
    have size := (abs_le.mp (interval_residue_error (Nat.le_add_right lo M) qp x)).2
    change (ys.card:ℝ)-(((lo+M:ℕ):ℝ)-lo)/q ≤ 1 at size
    simp only [Nat.cast_add,add_sub_cancel_left] at size
    have card : ((Y.filter (hit T)).card:ℝ)≤(M:ℝ)/q+1 :=
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
one entire cell is eventually smaller than that budget divided by d.
The bound holds uniformly for the same coefficient law in every cell. -/
theorem cell_count_covariance (line : DirichletLZerosOnLine) (k : ℕ) (kp : 0<k) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ cell : Option (Bool×Fin (Fixed.d b)),
    let X := constructorCellMarks n ell cell; let M := cellMarkCount b
    (∑ a∈X,∑ y∈X, normalizedSmoothCovariance R T a y)/(M:ℝ)^2 ≤ 1/((k:ℝ)*Fixed.d b) := by
  obtain ⟨C,cp,b₁,compare⟩ := cell_pair_covariance_approximation line 3 (by norm_num)
  obtain ⟨d₀,inverse⟩ := pair_weight_inverse_prime_bound
  obtain ⟨b₂,mass⟩ := fixed_pair_weight_sum line
  obtain ⟨b₃,band⟩ := fixed_band_power_savings 50 (by norm_num)
  obtain ⟨b₄,budget⟩ := fixed_class_accuracy ((k:ℝ)*(C+1))
  obtain ⟨t,cap⟩ := exists_nat_ge (exp (384*(k:ℝ)))
  obtain ⟨b₅,grow⟩ := Fixed.degree_grows (max d₀ (max 2 t))
  refine ⟨max (max b₁ b₂) (max b₃ (max b₄ b₅)),?_⟩
  intro n ell R T b huge hn comp target absent cell X M
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
  have model (a : ℕ) :
      (∑ y∈X,((pairGamma P (Fixed.rootBase n) a y)^2-1)) ≤ (M:ℝ)/(2*k*d)+exp (48*z) := by
    have est := pair_gamma_row_excess P X (fun p h=>(primes p h).1) (Fixed.rootBase n) a
      (firstCellMark b cell) M (filter_subset ..)
    exact est.trans (add_le_add ((mul_le_mul_of_nonneg_left ((sub_le_sub_right inverseBound 1).trans absw)
      (Nat.cast_nonneg M)).trans_eq (by ring)) (mass b two P primes))
  have xs : (X.card:ℝ)≤M := Nat.cast_le.mpr ((card_le_card (filter_subset ..)).trans_eq (by simp [M,b]))
  have mpos : 0<(M:ℝ) := by dsimp [M,cellMarkCount]; positivity
  have bound := sum_le_sum (s:=X) (fun a _=>model a)
  rw [sum_const,nsmul_eq_mul] at bound
  have modelTotal := bound.trans (mul_le_mul_of_nonneg_right xs (by positivity))
  let cov := normalizedSmoothCovariance R T
  let g := fun a y=> (pairGamma P (Fixed.rootBase n) a y)^2-1
  have B1 : 1≤(Fixed.B b)^3 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
  have err := compare R T one hn comp target absent cell cell 1 1 0 0
    squarefree_one squarefree_one B1 B1 (fun _=>1) (fun _=>1) 1 1 zero_le_one zero_le_one (by simp) (by simp)
  simp only [Nat.modEq_one,filter_true,Nat.cast_one,one_mul] at err
  change |∑ a∈X,∑ y∈X,(cov a y-g a y)|/(M:ℝ)^2 ≤ C*exp (-3*z^2) at err
  simp only [sum_sub_distrib] at err
  have raw := (le_abs_self _).trans ((div_le_iff₀ (sq_pos_of_pos mpos)).mp err)
  have bo : 1≤B := by dsimp [B,Fixed.B]; exact_mod_cast Nat.one_le_two_pow
  have mb : B≤M := by
    dsimp only [B,M,cellMarkCount,Fixed.B]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) (by change 1000*Fixed.h b≤9997*Fixed.h b; omega)
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
theorem cell_count_score_error (line : DirichletLZerosOnLine) (k : ℕ) (kp : 0<k) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ cell : Option (Bool×Fin (Fixed.d b)), let X := constructorCellMarks n ell cell
    let M := cellMarkCount b; let f := fun a=>(smoothMarkProbability R T a)⁻¹
    let E := smoothMarkEvent R false; let F := smoothMarkEvent T true
    let μ := twoFieldMean R T X f E F
    μ=X.card ∧ (twoFieldSecond R T X f E F-2*(X.card:ℝ)*μ+(X.card:ℝ)^2)/(M:ℝ)^2 ≤ 1/((k:ℝ)*Fixed.d b) := by
  obtain ⟨b₁,cov⟩ := cell_count_covariance line k kp
  obtain ⟨b₂,margin⟩ := PrescribedRows.smooth_probability_margin line
  refine ⟨max b₁ b₂,?_⟩
  intro n ell R T b huge hn comp target absent cell X M f E F μ
  obtain ⟨large,big⟩ := max_le_iff.mp huge
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    have mark := (mem_filter.mp ha).2
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
  exact cov R T large hn comp target absent cell


/-- One positive boxed coefficient tuple has at least 4M/B² smooth
marks retained by the executable first stage in each of its 2d+1 cells. -/
theorem all_cells_retained_together (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    (∀ a∈(construct n ell 0 0 0 0).marks,(R.prefactor a false).Coprime (T.prefactor a true)) →
    ∃ (u v : ℤ×ℤ) (rel : Marking.Relations), R.compatible false u.1 u.2 ∧ T.compatible true v.1 v.2 ∧
      inCoefficientBox n u ∧ inCoefficientBox n v ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))=some rel ∧
      ∀ cell : Option (Bool×Fin (Fixed.d b)), let X := (constructorCellMarks n ell cell).filter (fun a=>smoothMarkEvent R false a u ∧ smoothMarkEvent T true a v ∧ a∈rel.marks)
      4*(cellMarkCount b:ℝ) ≤ (Fixed.B b:ℝ)^2*X.card := by
  classical
  obtain ⟨b₁,count⟩ := cell_count_score_error line 16384 (by decide)
  obtain ⟨n₂,marks⟩ := grid_cells_have_marks line
  obtain ⟨b₃,floor⟩ := PrescribedRows.smooth_probability_margin line
  obtain ⟨b₄,deleted⟩ := rejected_score_loss line 2 (by norm_num)
  obtain ⟨b₅,tiny⟩ := fixed_class_accuracy 192
  let threshold := max b₁ (max b₃ (max 1000 (max b₄ b₅)))
  refine ⟨max n₂ (max 2 (2^threshold)),?_⟩
  intro n large ell target comp absent R T b cop
  obtain ⟨old,h₀⟩ := max_le_iff.mp large
  obtain ⟨hn,hb⟩ := max_le_iff.mp h₀
  have huge : threshold≤b := ((Nat.le_log2 (by omega : n≠0)).mpr hb).trans (Nat.le_succ _)
  obtain ⟨one,rest⟩ := max_le_iff.mp huge
  obtain ⟨three,rest⟩ := max_le_iff.mp rest
  obtain ⟨big,rest⟩ := max_le_iff.mp rest
  obtain ⟨four,five⟩ := max_le_iff.mp rest
  let d := Fixed.d b; let I := Option (Bool×Fin d)
  let X (c : I) := constructorCellMarks n ell c
  let M : ℝ := cellMarkCount b; let B : ℝ := Fixed.B b
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
  let fc (c : I) (t : Ω) := (s c t-m c)^2/(M/32)^2+loss c t/(M/32)
  let z : ℝ := Fixed.z b
  let e := exp (-2*z^2)
  have entry (c : I) : cost c/(M/32)^2≤1024/(16384*(d:ℝ)) := by
    have bound := (count R T one hn comp target absent c).2
    change cost c/M^2≤1/(16384*(d:ℝ)) at bound
    exact (show cost c/(M/32)^2=1024*(cost c/M^2) by ring).le.trans
      ((mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ)≤1024)).trans_eq (by ring))
  have terms (c : I) : ∃ ξ, HasSum (fun t:Ω => W t*fc c t) ξ ∧ ξ≤1024/(16384*(d:ℝ))+32*e := by
    obtain ⟨μ,h,ub⟩ := deleted R T four hn comp target absent (X c) (fun _=>1)
      (fun a ha=>(mem_filter.mp ha).2) (fun a ha=>cop a (mem_filter.mp ha).2)
    simp only [abs_one,one_div,sum_const,nsmul_one] at h ub
    have xs : ((X c).card:ℝ)≤M := Nat.cast_le.mpr ((card_le_card (filter_subset ..)).trans_eq (by simp [b]))
    have du : μ/(M/32)≤32*e := (div_le_iff₀ (by positivity : 0<M/32)).mpr
      ((ub.trans (mul_le_mul_of_nonneg_left xs (exp_pos _).le)).trans_eq (by ring))
    refine ⟨cost c/(M/32)^2+μ/(M/32),?_,add_le_add (entry c) du⟩
    have h₁ := (twoField_score_error R T target (X c) w E F (m c)).div_const ((M/32)^2)
    apply (h₁.add (h.div_const (M/32))).congr_fun
    intro t
    change W t*((s c t-m c)^2/(M/32)^2+loss c t/(M/32))=W t*(s c t-m c)^2/(M/32)^2+W t*loss c t/(M/32)
    ring
  choose ξ ex up using terms
  have sum := sum_le_sum (s:=(univ : Finset I)) (fun c _=>up c)
  have card : Fintype.card I=2*d+1 := by simp [I]
  rw [sum_const,card_univ,nsmul_eq_mul,card] at sum
  have z1 : 1≤z := by dsimp [z,Fixed.z]; exact_mod_cast Nat.le_add_left 1 b.log2
  have dz : (d:ℝ)≤exp (z^2) := calc
    _ ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Fixed.degree_le_bits b).trans Nat.lt_log2_self.le
    _ = exp ((Fixed.z b:ℝ)*log 2) := by rw [←rpow_natCast,rpow_def_of_pos (by norm_num : (0:ℝ)<2),mul_comm]
    _ ≤ _ := by apply exp_le_exp.mpr; change z*log 2≤z^2
                nlinarith only [mul_nonneg (sub_nonneg.mpr z1) (zero_le_one.trans z1),
                  mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)) (zero_le_one.trans z1)]
  have smallD : (2*(d:ℝ)+1)*(32*e)≤1/4 := by
    have le := mul_le_mul_of_nonneg_right dz (exp_pos (-2*z^2)).le
    rw [←exp_add,show z^2+ -2*z^2= -z^2 by ring] at le
    have ad := mul_le_mul_of_nonneg_right dn (exp_pos (-2*z^2)).le
    dsimp only [e]
    linarith only [le,ad,tiny b five]
  have smallC : (2*(d:ℝ)+1)*(1024/(16384*(d:ℝ)))≤1/4 := by
    rw [←mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ)<16384*d)]; linarith
  have total : (∑ c:I, ξ c)≤1/2 := sum.trans (by push_cast; rw [mul_add]; linarith only [smallC,smallD])
  have box := coefficient_tail_lt_half_mark (b:=b) big
  change 1216*B^2*exp (-π*((b:ℝ)^2)^2/2)<1/(2*B) at box
  have small : 1/(2*B)≤1/4 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have fit : (∑ c:I, ξ c)+2432*B^2*exp (-π*((b:ℝ)^2)^2/2)<1 := by
    linarith only [total,box,small]
  have pw0 (a) : 0≤w a := inv_nonneg.mpr (mul_nonneg (R.probability_unit target false _).1 (T.probability_unit target true _).1)
  have l0 (c t) : 0≤loss c t := sum_nonneg (fun a _=>by split <;> first | exact pw0 a | rfl)
  have f0 (c t) : 0≤fc c t := add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg (l0 c t) (by positivity))
  obtain ⟨t,bu,bv,cheap⟩ := twoField_box_of_cost R T target (fun t=>∑ c:I,fc c t) _ (fun t=>sum_nonneg (fun c _=>f0 c t))
    ((hasSum_sum (s:=(univ:Finset I)) (fun c _=>ex c)).congr_fun (fun t=>mul_sum ..)) fit
  let u := t.1.val; let v := t.2.val
  let stage := Marking.stageOne (TryPair.fixedInput n ell (construct n ell u.1.toNat u.2.toNat v.1.toNat v.2.toNat))
  let retained (a : ℕ) := ∃ rel,stage=some rel ∧ a∈rel.marks
  let yes (a : ℕ) := E a u ∧ F a v ∧ retained a
  have lower (c : I) : 4*M≤B^2*((X c).filter yes).card := by
    let hits := (X c).filter yes
    have result := (single_le_sum (s:=(univ:Finset I)) (f:=fun i=>fc i t) (fun i _=>f0 i t) (mem_univ c)).trans_lt cheap
    have scoreSmall : (s c t-m c)^2/(M/32)^2<1 :=
      (le_add_of_nonneg_right (div_nonneg (l0 c t) (by positivity))).trans_lt result
    have lossSmall : loss c t/(M/32)<1 := (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))).trans_lt result
    have near := (abs_lt.mp ((sq_lt_sq₀ (abs_nonneg _) (by positivity : 0≤M/32)).mp
      (by rw [sq_abs]; exact (div_lt_one (sq_pos_of_pos (by positivity))).mp scoreSmall))).1
    have lossCap := (div_lt_one (by positivity)).mp lossSmall
    have c4 : 1≤(Fixed.B b)^4 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
    have gc := marks n old ell target comp absent 1 0 0 0 0 0 c (by decide) c4
      (fun p hp dvd=>((Nat.prime_of_mem_primeFactors hp).ne_one (Nat.eq_one_of_dvd_one dvd)).elim)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at gc
    change M/8 ≤ m c at gc
    have floorAt (a) (ha : a∈X c) (S : PrescribedRows n ell) (s : Bool) :
        8/B ≤ prescribedProbability S s (smoothMarkEvent S s a) :=
      (floor S three hn comp target absent (mem_filter.mp ha).2 s).trans_eq
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
      rw [sum_filter,←sum_add_distrib]
      apply sum_congr rfl; intro a _
      change _ = (if yes a then w a else 0)+(if rejectedSmoothMark R T a u v then w a else 0)
      have rej : rejectedSmoothMark R T a u v ↔ E a u ∧ F a v ∧ ¬retained a := by
        simp only [rejectedSmoothMark,E,F,retained,stage,bu,bv,true_and,u,v]
      by_cases h : E a u ∧ F a v <;> by_cases r : retained a <;> simp_all only [yes,
        and_true,and_false,not_true_eq_false,not_false_eq_true,if_true,if_false,mul_one,mul_zero,zero_add,add_zero]
    have upper := sum_le_sum (s:=hits) (fun a h=>pw a (mem_filter.mp h).1)
    rw [sum_const,nsmul_eq_mul] at upper
    change 4*M≤B^2*(hits.card:ℝ)
    linarith only [near,gc,upper,lossCap,eq]
  cases hs : stage with
  | none =>
    have no (a : ℕ) : ¬yes a := fun h=>by obtain ⟨_,hh,_⟩ := h.2.2; simp [hs] at hh
    have contradiction := lower none
    simp [no] at contradiction
    linarith
  | some rel =>
    refine ⟨u,v,rel,t.1.property,t.2.property,bu,bv,hs,?_⟩
    intro c hits
    have eq : ((X c).filter yes)=hits := by
      ext a
      simp [hits,yes,retained,hs,X,E,F]
    rw [←eq]
    exact lower c


/-- Without prescribed roots, one candidate in the positive enumeration retains
at least 4M/B² marks per cell and has the indicated incidence rank and nullity. -/
theorem unrestricted_all_cells_rank (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∃ (u v w z : ℕ) (rel : Marking.Relations),
      (1≤u ∧ u≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤v ∧ v≤2*b^2*Fixed.U b) ∧
      (1≤w ∧ w≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤z ∧ z≤2*b^2*Fixed.U b) ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel ∧
      (∀ cell : Option (Bool×Fin (Fixed.d b)),
        4*(cellMarkCount b:ℝ) ≤ (Fixed.B b:ℝ)^2*((constructorCellMarks n ell cell).filter (·∈rel.marks)).card) ∧
      7997*Fixed.h b+2 ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank ∧
      2*Fixed.d b ≤ Module.finrank ℚ (LinearMap.ker (rel.matrix.map (Int.castRingHom ℚ)).mulVecLin) := by
  classical
  obtain ⟨n₀,all⟩ := all_cells_retained_together line
  obtain ⟨b₀,grows⟩ := Fixed.degree_grows 10004
  refine ⟨max n₀ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b
  obtain ⟨old,h₀⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp h₀
  have big : b₀≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  let S := PrescribedRows.unrestricted n ell
  have cop (a : ℕ) : (S.prefactor a false).Coprime (S.prefactor a true) :=
    (S.prefactors_coprime_iff S ((by decide : 3≤10004).trans (grows b big)) target a).mpr
      (by simp [S,PrescribedRows.unrestricted,PrescribedRows.hit])
  obtain ⟨i,j,rel,_,_,bi,bj,stage,counts⟩ := all n old ell target comp absent S S (fun a _=>cop a)
  have bounds (k : ℤ×ℤ) (hk : inCoefficientBox n k) :
      (1≤k.1.toNat ∧ k.1.toNat≤2*b^2*Fixed.U b*Fixed.A b) ∧
      (1≤k.2.toNat ∧ k.2.toNat≤2*b^2*Fixed.U b) := by
    obtain ⟨x,y,z,t⟩ := hk
    exact ⟨⟨by omega,Int.toNat_le.mpr (by exact_mod_cast y)⟩,⟨by omega,Int.toNat_le.mpr (by exact_mod_cast t)⟩⟩
  obtain ⟨xu,yu⟩ := bounds i bi; obtain ⟨xv,yv⟩ := bounds j bj
  have actual (cell : Option (Bool×Fin (Fixed.d b))) :
      4*(cellMarkCount b:ℝ) ≤ (Fixed.B b:ℝ)^2*((constructorCellMarks n ell cell).filter (·∈rel.marks)).card := by
    apply (counts cell).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact Nat.cast_le.mpr (card_le_card (monotone_filter_right _ (fun _ _ h => h.2.2)))
  have pop : 4*cellMarkCount b ≤ (Fixed.B b)^2*rel.marks.length := by
    let X := (constructorCellMarks n ell none).filter (·∈rel.marks)
    have sub : X⊆rel.marks.toFinset := fun a ha=>List.mem_toFinset.mpr (mem_filter.mp ha).2
    have cnt : 4*cellMarkCount b ≤ (Fixed.B b)^2*X.card := by exact_mod_cast actual none
    exact cnt.trans (Nat.mul_le_mul_left _ ((card_le_card sub).trans (List.toFinset_card_le _)))
  have inj := constructed_columns_injective hn (grows b big) target ⟨xu.2,yu.2⟩ stage
  let r := (rel.matrix.map (Int.castRingHom ℚ)).rank
  have power : 2^(2+9997*Fixed.h b) ≤ 2^(2000*Fixed.h b+r) := calc
    _ = 4*cellMarkCount b := by rw [pow_add]; rfl
    _ ≤ (Fixed.B b)^2*rel.marks.length := pop
    _ ≤ (Fixed.B b)^2*2^r := Nat.mul_le_mul_left _ (retained_rank_of_column_separation rel inj)
    _ = _ := by change (2^(1000*Fixed.h b))^2 * 2^r = _; rw [←pow_mul,←pow_add]; congr 1; omega
  have exponent := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp power
  have bp : 0<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide : 0<2) : 0<Fixed.B b)
  have p : 4*(cellMarkCount b:ℝ) ≤ (Fixed.B b:ℝ)^2*rel.marks.length := by exact_mod_cast pop
  have nullity := kernel_dim_of_cell_count (q:=1) (by decide) (Nat.one_le_pow _ _ (Nat.one_le_two_pow)) stage
  refine ⟨_,_,_,_,rel,xu,yu,xv,yv,stage,actual,by change 7997*Fixed.h b+2≤r; omega,nullity ?_⟩
  apply (div_le_iff₀ (by positivity)).mpr
  rw [Nat.cast_one,mul_one]
  change (cellMarkCount b:ℝ) ≤ (rel.marks.length:ℝ)*(32*(Fixed.B b:ℝ)^2)
  nlinarith only [p,mul_nonneg (sq_nonneg (Fixed.B b:ℝ)) (Nat.cast_nonneg rel.marks.length)]

end Cogentic.Construction

#print axioms Cogentic.Construction.cell_count_score_error

#print axioms Cogentic.Construction.all_cells_retained_together

#print axioms Cogentic.Construction.unrestricted_all_cells_rank
