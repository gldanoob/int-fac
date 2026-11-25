import Cogentic.MarkDensity
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Choose.Sum

namespace Cogentic.Construction
open Finset Real

/-- Each CRT class contributes at most one endpoint error, including on
intervals that contain fewer elements than the modulus. -/
theorem interval_residue_error {a b q : ℕ} (ab : a ≤ b) (qp : 0 < q) (v : ℕ) :
    |(((Ico a b).filter (fun n => n ≡ v [MOD q])).card:ℝ) - ((b:ℝ)-a)/q| ≤ 1 := by
  let x := ((a:ℚ)-v)/q
  let y := ((b:ℚ)-v)/q
  have ord : x ≤ y := div_le_div_of_nonneg_right
    (sub_le_sub_right (by exact_mod_cast ab) _) (by positivity)
  have eq := Nat.Ico_filter_modEq_card a b qp v
  change (_:ℤ) = max (⌈y⌉-⌈x⌉) 0 at eq
  rw [max_eq_left (sub_nonneg.mpr (Int.ceil_le_ceil ord))] at eq
  have eq' : (((Ico a b).filter (fun n => n ≡ v [MOD q])).card:ℚ) = (⌈y⌉:ℚ)-(⌈x⌉:ℚ) := by exact_mod_cast eq
  have size : ((b:ℚ)-a)/q = y-x := by dsimp [x,y]; ring
  have bound : |(((Ico a b).filter (fun n => n ≡ v [MOD q])).card:ℚ) - ((b:ℚ)-a)/q| ≤ 1 := by
    rw [eq',size,abs_le]
    constructor <;> linarith [Int.le_ceil x,Int.ceil_lt_add_one x,Int.le_ceil y,Int.ceil_lt_add_one y]
  have realBound := (Rat.cast_le (K:=ℝ)).mpr bound
  simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,Rat.cast_one] using realBound

/-- The Bonferroni truncation for one integer misses by at most its
number of subsets of bad primes at the first omitted degree. -/
theorem sieve_point_error (hits t : ℕ) :
    |(if hits=0 then (1:ℝ) else 0) - ∑ j ∈ range (t+1), (-1:ℝ)^j*(hits.choose j:ℝ)| ≤
      hits.choose (t+1) := by
  cases hits with
  | zero =>
    simp [Finset.sum_range_succ',Nat.choose_zero_succ]
  | succ n =>
    have eq := Int.alternating_sum_range_choose_eq_choose (n:=n) (m:=t)
    have r : (∑ j ∈ range (t+1), (-1:ℝ)^j*((n+1).choose j:ℝ)) = (-1:ℝ)^t*(n.choose t:ℝ) := by exact_mod_cast eq
    simp only [Nat.add_one_ne_zero,ite_false,zero_sub,abs_neg,r,abs_mul,abs_pow,abs_one,one_pow,one_mul,Nat.abs_cast]
    rw [Nat.choose_succ_succ']
    exact_mod_cast Nat.le_add_right (n.choose t) (n.choose (t+1))

/-- The j-th empirical sieve moment equals the total number of points
meeting all congruences in each j-element set of sieving primes. -/
theorem sieve_intersections (X P : Finset ℕ) (bad : ℕ → Finset ℕ)
    (sub : ∀ n ∈ X, bad n ⊆ P) (j : ℕ) :
    ∑ n ∈ X, ((bad n).card.choose j:ℝ) =
      ∑ T ∈ P.powersetCard j, (((X.filter (fun n => T ⊆ bad n)).card):ℝ) := by
  classical
  have point (n) (h : n∈X) : ((bad n).card.choose j:ℝ) =
      ∑ T ∈ P.powersetCard j, if T⊆bad n then 1 else 0 := by
    have eq : (P.powersetCard j).filter (· ⊆ bad n) = (bad n).powersetCard j := by
      ext T
      simp only [mem_filter,mem_powersetCard]
      exact ⟨fun s => ⟨s.2,s.1.2⟩,fun s => ⟨⟨s.1.trans (sub n h),s.2⟩,s.1⟩⟩
    rw [←sum_filter,Finset.sum_const,eq,card_powersetCard,nsmul_eq_mul,mul_one]
  rw [sum_congr rfl point,sum_comm]
  apply sum_congr rfl
  intro T _
  rw [←sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

/-- All omission terms from degree k onward are small at once. The
bound uses the Euler product with doubled weights at every prime. -/
theorem sieve_product_tail (P : Finset ℕ) (w : ℕ → ℝ) (w0 : ∀ p ∈ P, 0 ≤ w p) (k : ℕ) :
    (2:ℝ)^k*(∑ T ∈ P.powerset with k ≤ T.card, ∏ p ∈ T, w p) ≤ exp (2*∑ p ∈ P, w p) := by
  classical
  rw [mul_sum]
  have weights (T : Finset ℕ) : ∏ p ∈ T, 2*w p = (2:ℝ)^T.card*∏ p ∈ T, w p := by
    rw [prod_mul_distrib,prod_const]
  calc
    _ ≤ ∑ T ∈ P.powerset with k ≤ T.card, ∏ p ∈ T, 2*w p := by
      apply sum_le_sum
      intro T h
      rw [weights]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (mem_filter.mp h).2)
        (prod_nonneg (fun p hp => w0 p (mem_powerset.mp (mem_filter.mp h).1 hp)))
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, 2*w p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun T h _ =>
        prod_nonneg (fun p hp => mul_nonneg (by norm_num) (w0 p (mem_powerset.mp h hp))))
    _ = ∏ p ∈ P, (1+2*w p) := (prod_one_add _).symm
    _ ≤ ∏ p ∈ P, exp (2*w p) := prod_le_prod (fun p mem => by linarith [w0 p mem])
      (fun p _ => by linarith [add_one_le_exp (2*w p)])
    _ = _ := by rw [←exp_sum,mul_sum]

private theorem sum_by_sieve_degree (P : Finset ℕ) (f : Finset ℕ → ℝ) (t : ℕ) :
    (∑ j ∈ range (t+1), ∑ T ∈ P.powersetCard j, f T) =
      ∑ T ∈ P.powerset with T.card ≤ t, f T := by
  let good := P.powerset.filter (fun T => T.card ≤ t)
  have maps : ∀ T ∈ good, T.card ∈ range (t+1) := fun _ h => mem_range.mpr (by
    have := (mem_filter.mp h).2; omega)
  change _ = ∑ T ∈ good, f T
  rw [←sum_fiberwise_of_maps_to maps f]
  apply sum_congr rfl
  intro j hj
  have eq : good.filter (fun T => T.card=j) = P.powersetCard j := by
    ext T
    simp only [good,mem_filter,mem_powerset,mem_powersetCard]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2 ▸ Nat.le_of_lt_succ (mem_range.mp hj)⟩,h.2⟩⟩
  rw [eq]

/-- Finite Brun estimate. Each simultaneous congruence contributes at
most one endpoint error to the signed sum through the truncation degree.
The remaining density is controlled by the tilted Euler product. -/
theorem finite_grid_sieve (X P : Finset ℕ) (bad : ℕ → Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℕ)
    (sub : ∀ a ∈ X, bad a ⊆ P) (w0 : ∀ p ∈ P, 0 ≤ w p) (lp : 0 ≤ L)
    (count : ∀ T ⊆ P,
      |(((X.filter (fun a => T ⊆ bad a)).card):ℝ)-L*(∏ p ∈ T, w p)| ≤ 1) :
    |(∑ a ∈ X, if (bad a).card=0 then (1:ℝ) else 0) - L*(∏ p ∈ P, (1-w p))| ≤
      ∑ j ∈ range (t+2), (P.card.choose j:ℝ) +
      2*L*exp (2*∑ p ∈ P, w p)/(2:ℝ)^(t+1) := by
  classical
  let S (T : Finset ℕ) := ∏ p ∈ T, w p
  let A (j : ℕ) := ∑ a ∈ X, ((bad a).card.choose j:ℝ)
  let B (j : ℕ) := ∑ T ∈ P.powersetCard j, S T
  let H := exp (2*∑ p ∈ P, w p)/(2:ℝ)^(t+1)
  let C (j : ℕ) := (P.card.choose j:ℝ)
  have diff (j : ℕ) : |A j-L*B j| ≤ C j := by
    dsimp only [A,B,C]
    rw [sieve_intersections X P bad sub,mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    simpa only [sum_const,nsmul_eq_mul,mul_one,card_powersetCard] using
      sum_le_sum (s:=P.powersetCard j) (fun T h => count T (mem_powersetCard.mp h).1)
  have sj0 (T : Finset ℕ) (mem : T ⊆ P) : 0 ≤ S T := prod_nonneg (fun p h => w0 p (mem h))
  have tail := (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(t+1))).mpr
    ((mul_comm ..).le.trans (sieve_product_tail P w w0 (t+1)))
  change (∑ T ∈ P.powerset with t+1 ≤ T.card, S T) ≤ H at tail
  have lastB : B (t+1) ≤ H := by
    refine le_trans ?_ tail
    exact sum_le_sum_of_subset_of_nonneg (fun T h => mem_filter.mpr
      ⟨mem_powerset.mpr (mem_powersetCard.mp h).1,(mem_powersetCard.mp h).2.ge⟩)
      (fun T h _ => sj0 T (mem_powerset.mp (mem_filter.mp h).1))
  have lastA : A (t+1) ≤ C (t+1)+L*H := by
    have h := (abs_le.mp (diff (t+1))).2
    linarith only [h,mul_le_mul_of_nonneg_left lastB lp]
  let emp := ∑ j ∈ range (t+1), (-1:ℝ)^j*A j
  let model := ∑ j ∈ range (t+1), (-1:ℝ)^j*B j
  let keep := ∑ a ∈ X, if (bad a).card=0 then (1:ℝ) else 0
  have empirical : |keep-emp| ≤ A (t+1) := by
    have eq : emp = ∑ a ∈ X, ∑ j ∈ range (t+1), (-1:ℝ)^j*((bad a).card.choose j:ℝ) := by
      dsimp only [emp,A]
      simp_rw [mul_sum]
      rw [sum_comm]
    dsimp only [keep]; rw [eq,←sum_sub_distrib]
    exact (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun a _ => sieve_point_error (bad a).card t))
  have approx : |emp-L*model| ≤ ∑ j ∈ range (t+1), C j := by
    dsimp only [emp,model]
    rw [mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun j _ => ?_))
    rw [show (-1:ℝ)^j*A j-L*((-1)^j*B j)=(-1)^j*(A j-L*B j) by ring,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact diff j
  let term (T : Finset ℕ) := (-1:ℝ)^T.card*S T
  have full : ∏ p ∈ P, (1-w p) = ∑ T ∈ P.powerset, term T := by
    simp only [prod_sub _ _ P,prod_const_one,mul_one,term,S]
  have trunc : model = ∑ T ∈ P.powerset with T.card ≤ t, term T := by
    rw [←sum_by_sieve_degree]
    apply sum_congr rfl
    intro j hj; dsimp only [B]; rw [mul_sum]
    exact sum_congr rfl (fun T h => by simp only [term,(mem_powersetCard.mp h).2])
  have moderr : |(∏ p ∈ P, (1-w p))-model| ≤ H := by
    have split := sum_filter_add_sum_filter_not P.powerset (fun T => T.card ≤ t) term
    simp only [not_le,Nat.lt_iff_add_one_le] at split
    rw [full,←split,trunc,add_sub_cancel_left]
    refine (abs_sum_le_sum_abs ..).trans ?_
    apply le_trans (sum_le_sum (fun T h => ?_)) tail
    dsimp only [term]
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (sj0 T (mem_powerset.mp (mem_filter.mp h).1))]
  have endErr : |L*model-L*(∏ p ∈ P, (1-w p))| ≤ L*H := by
    rw [←mul_sub,abs_mul,abs_of_nonneg lp,abs_sub_comm]
    exact mul_le_mul_of_nonneg_left moderr lp
  have total := (abs_sub_le keep emp _).trans (add_le_add empirical ((abs_sub_le emp (L*model) _).trans (add_le_add approx endErr)))
  change |keep-_| ≤ _
  rw [sum_range_succ]
  dsimp only [C,H] at total lastA ⊢
  simp only [div_eq_mul_inv] at total lastA ⊢
  linarith only [total,lastA]

theorem prime_product_modEq (T : Finset ℕ) (pr : ∀ p ∈ T, p.Prime) (a m : ℕ) :
    a ≡ m [MOD ∏ p ∈ T, p] ↔ ∀ p ∈ T, a ≡ m [MOD p] := by
  induction T using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p T fresh ih =>
    have pp := pr p (mem_insert_self ..)
    have old (r) (h : r ∈ T) := pr r (mem_insert_of_mem h)
    have cop : p.Coprime (∏ r ∈ T, r) := Nat.coprime_prod_right_iff.mpr
      (fun r hr => (Nat.coprime_primes pp (old r hr)).mpr (fun eq => fresh (eq ▸ hr)))
    rw [prod_insert fresh,← Nat.modEq_and_modEq_iff_modEq_mul cop,ih old]
    simp only [forall_mem_insert]

/-- The interval sieve for any residue progression coprime to the sieving
primes. Every simultaneous divisibility count uses the actual integer CRT. -/
theorem brun_interval {a b q : ℕ} (ab : a ≤ b) (qp : 0 < q) (r m t : ℕ) (P : Finset ℕ)
    (pr : ∀ p ∈ P, p.Prime) (cop : ∀ p ∈ P, q.Coprime p) :
    let L := ((b:ℝ)-a)/q
    let X := (Ico a b).filter (fun x => x ≡ r [MOD q])
    |(((X.filter (fun x => ∀ p ∈ P, ¬x ≡ m [MOD p])).card):ℝ) -
      L*(∏ p ∈ P, (1-(p:ℝ)⁻¹))| ≤
      ∑ j ∈ range (t+2), (P.card.choose j:ℝ) +
      2*L*exp (2*∑ p ∈ P, (p:ℝ)⁻¹)/(2:ℝ)^(t+1) := by
  classical
  intro L X
  let bad := fun x => P.filter (fun p => x ≡ m [MOD p])
  have count (T : Finset ℕ) (sub : T ⊆ P) :
      |(((X.filter (fun x => T ⊆ bad x)).card):ℝ)-L*(∏ p ∈ T, (p:ℝ)⁻¹)| ≤ 1 := by
    let Q := ∏ p ∈ T, p
    have qcop : q.Coprime Q := Nat.coprime_prod_right_iff.mpr (fun p h => cop p (sub h))
    have Qp : 0 < Q := Finset.prod_pos (fun p h => (pr p (sub h)).pos)
    let v := Nat.chineseRemainder qcop r m
    have eq : X.filter (fun x => T ⊆ bad x) = (Ico a b).filter (fun x => x ≡ v.val [MOD q*Q]) := by
      ext x
      simp only [X,mem_filter,←Nat.modEq_and_modEq_iff_modEq_mul qcop]
      constructor
      · intro h
        refine ⟨h.1.1,h.1.2.trans v.property.1.symm,?_⟩
        exact ((prime_product_modEq T (fun p pT => pr p (sub pT)) x m).mpr
          (fun p pT => (mem_filter.mp (h.2 pT)).2)).trans v.property.2.symm
      · rintro ⟨xI,hq,hv⟩
        refine ⟨⟨xI,hq.trans v.property.1⟩,fun p pT => mem_filter.mpr ⟨sub pT,?_⟩⟩
        exact (prime_product_modEq T (fun p pt => pr p (sub pt)) x m).mp (hv.trans v.property.2) p pT
    rw [eq]
    have est := interval_residue_error ab (Nat.mul_pos qp Qp) v.val
    have wt : (∏ p ∈ T, (p:ℝ)⁻¹) = (Q:ℝ)⁻¹ := by simp [Q]
    rw [wt]
    simpa only [L,Nat.cast_mul,div_mul_eq_div_div,div_eq_mul_inv, mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using est
  have work := finite_grid_sieve X P bad (fun p => (p:ℝ)⁻¹) L t (fun _ _ => filter_subset _ _)
    (fun _ _ => by positivity) (div_nonneg (sub_nonneg.mpr (by exact_mod_cast ab)) (by positivity)) count
  have nil (x : ℕ) : (bad x).card=0 ↔ ∀ p ∈ P, ¬x ≡ m [MOD p] := by
    rw [card_eq_zero]
    exact filter_eq_empty_iff
  simpa only [nil,←sum_filter,sum_const,nsmul_eq_mul,mul_one] using work

/-- Primes shared by the progression modulus and the cofactor impose no
extra density loss on an eligible class. The remaining product counts
the actual coprimality predicate used by the constructor. -/
theorem brun_coprime_interval {a b q k : ℕ} (ab : a ≤ b) (qp : 0 < q) (kp : 0 < k) (r m t : ℕ)
    (eligible : ∀ p ∈ k.primeFactors, p ∣ q → ¬ r ≡ m [MOD p]) :
    let L := ((b:ℝ)-a)/q
    let X := (Ico a b).filter (fun x => x ≡ r [MOD q])
    let P := k.primeFactors.filter (fun p => ¬p ∣ q)
    |(((X.filter (fun x : ℕ => ((x:ℤ)-m).natAbs.Coprime k)).card):ℝ) -
      L*(∏ p ∈ P, (1-(p:ℝ)⁻¹))| ≤
      ∑ j ∈ range (t+2), (P.card.choose j:ℝ) +
      2*L*exp (2*∑ p ∈ P, (p:ℝ)⁻¹)/(2:ℝ)^(t+1) := by
  classical
  intro L X P
  have pr (p) (h : p ∈ P) := Nat.prime_of_mem_primeFactors (mem_filter.mp h).1
  have cop (p) (h : p ∈ P) := ((pr p h).coprime_iff_not_dvd.mpr (mem_filter.mp h).2).symm
  have result := brun_interval ab qp r m t P pr cop
  have mod (x p : ℕ) : p ∣ ((x:ℤ)-m).natAbs ↔ x ≡ m [MOD p] := by
    calc _ ↔ m ≡ x [MOD p] := by
           rw [Nat.modEq_iff_dvd]
           exact Int.natCast_dvd_natCast.symm.trans Int.dvd_natAbs
         _ ↔ _ := ⟨fun h => h.symm,fun h => h.symm⟩
  have eq : X.filter (fun x : ℕ => ((x:ℤ)-m).natAbs.Coprime k) =
      X.filter (fun x => ∀ p ∈ P, ¬x ≡ m [MOD p]) := by
    apply filter_congr
    intro x hx
    constructor
    · intro c p h hit
      exact Nat.not_coprime_of_dvd_of_dvd (pr p h).one_lt ((mod x p).mpr hit)
        (Nat.dvd_of_mem_primeFactors (mem_filter.mp h).1) c
    · intro no
      apply Nat.coprime_of_dvd
      intro p prime pg pk
      have member := Nat.mem_primeFactors.mpr ⟨prime,pk,kp.ne'⟩
      have hit := (mod x p).mp pg
      by_cases pq : p ∣ q
      · exact eligible p member pq (((mem_filter.mp hx).2.of_dvd pq).symm.trans hit)
      · exact no p (mem_filter.mpr ⟨member,pq⟩) hit
  rw [eq]
  exact result

end Cogentic.Construction
