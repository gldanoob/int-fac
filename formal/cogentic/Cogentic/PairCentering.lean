import Cogentic.PairWeights

namespace Cogentic.Construction
open Finset Real

/-- The shortest crossing prefix of any large squarefree divisor has
modulus between y and y² if each of its primes is at most y. -/
theorem middle_subproduct (T : Finset ℕ) (y : ℕ) (yp : 1≤y)
    (size : ∀ p∈T, p ≤ y) (large : y < sieveProduct T) :
    ∃ U ⊆ T, y < sieveProduct U ∧ sieveProduct U ≤ y^2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sieveProduct] at large; omega
  | @insert p T hp ih =>
    by_cases crossed : y < sieveProduct T
    · obtain ⟨U,hU,low,hi⟩ := ih (fun s h => size s (mem_insert_of_mem h)) crossed
      exact ⟨U,hU.trans (subset_insert ..),low,hi⟩
    · refine ⟨insert p T,subset_rfl,large,?_⟩
      change (∏ q ∈ insert p T,q) ≤ y^2
      rw [prod_insert hp,sq]
      exact Nat.mul_le_mul (size p (mem_insert_self ..)) (Nat.le_of_not_gt crossed)

private theorem class_square_bound (X : Finset ℕ) (w : ℕ → ℝ) (T : Finset ℕ) (m : ℕ)
    (hp : 0 < sieveProduct T) (c : ℝ)
    (small : ∀ r < sieveProduct T, (∀ p∈T, ¬r ≡ m [MOD p]) →
      |∑ x ∈ X with x%(sieveProduct T)=r, w x| ≤ c/(sieveProduct T:ℝ)) :
    (∑ r ∈ range (sieveProduct T) with ∀ p∈T, ¬r ≡ m [MOD p],
          (∑ x ∈ X with x%(sieveProduct T)=r, w x)^2) ≤ c^2/(sieveProduct T:ℝ) := by
  classical
  let q := sieveProduct T
  let F := (range q).filter (fun r => ∀ p ∈ T, ¬r ≡ m [MOD p])
  have each (r) (h : r∈F) := pow_le_pow_left₀ (abs_nonneg _)
    (small r (mem_range.mp (mem_filter.mp h).1) (mem_filter.mp h).2) 2
  simp only [sq_abs] at each
  have sum := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at sum
  have fc := card_le_card (filter_subset (fun r => ∀ p∈T, ¬r ≡ m [MOD p]) (range q))
  have fit : (F.card:ℝ) ≤ q := by simpa using (show (F.card:ℝ) ≤ (range q).card by exact_mod_cast fc)
  refine sum.trans ((mul_le_mul_of_nonneg_right fit (sq_nonneg _)).trans_eq ?_)
  change (q:ℝ)*(c/q)^2=c^2/q
  field_simp

private theorem prefix_square_bound (X : Finset ℕ) (w : ℕ → ℝ) (T U : Finset ℕ) (sub : U⊆T)
    (m : ℕ) (hp : 0 < sieveProduct T) (A : ℝ)
    (cap : ∀ r, (∑ x ∈ X with x ≡ r [MOD sieveProduct U], |w x|) ≤ A) :
    (∑ r ∈ range (sieveProduct T) with ∀ p∈T, ¬r ≡ m [MOD p],
          (∑ x ∈ X with x%(sieveProduct T)=r, w x)^2) ≤ A*∑ x∈X, |w x| := by
  classical
  let q := sieveProduct T
  let v := sieveProduct U
  let f := fun r => ∑ x ∈ X with x%q=r, w x
  let mass := fun r => ∑ x ∈ X with x%q=r, |w x|
  let good := (range q).filter (fun r => ∀ p∈T, ¬r ≡ m [MOD p])
  have total : (∑ r ∈ range q, mass r) = ∑ x∈X, |w x| :=
    sum_fiberwise_of_maps_to (fun x _ => mem_range.mpr (Nat.mod_lt x hp)) _
  have dv : v ∣ q := prod_dvd_prod_of_subset _ _ id sub
  have upper (r) : mass r ≤ A := by
    refine le_trans ?_ (cap r)
    apply sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => abs_nonneg _)
    intro x h
    have mod : x ≡ r [MOD q] := by rw [← (mem_filter.mp h).2]; exact (Nat.mod_modEq ..).symm
    exact mem_filter.mpr ⟨(mem_filter.mp h).1,mod.of_dvd dv⟩
  have norm (r) : |f r| ≤ mass r := abs_sum_le_sum_abs ..
  have Ap : 0 ≤ A := (abs_nonneg (f 0)).trans ((norm 0).trans (upper 0))
  change (∑ r∈good, (f r)^2) ≤ _
  calc _ ≤ ∑ r ∈ good, A*mass r := sum_le_sum (fun r _ => by
           rw [←sq_abs,sq]
           exact mul_le_mul ((norm r).trans (upper r)) (norm r) (abs_nonneg _) Ap)
       _ ≤ ∑ r ∈ range q, A*mass r := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
         (fun r _ _ => mul_nonneg Ap ((abs_nonneg _).trans (norm r)))
       _ = _ := by rw [←mul_sum,total]

/-- Centering on short eligible classes and an unsigned count on
intermediate moduli control the full weighted two-point correction. -/
theorem centered_pair_bound (X P : Finset ℕ) (pr : ∀ p∈P, p.Prime) (m d y : ℕ)
    (dp : 0 < d) (yp : 1 ≤ y) (size : ∀ p∈P, d < p ∧ p ≤ y) (w : ℕ→ℝ) (c A : ℝ)
    (short : ∀ T ⊆ P, sieveProduct T ≤ y → ∀ r < sieveProduct T, (∀ p∈T, ¬r ≡ m [MOD p]) →
      |∑ x ∈ X with x%(sieveProduct T)=r, w x| ≤ c/(sieveProduct T:ℝ))
    (mid : ∀ U ⊆ P, y < sieveProduct U → sieveProduct U ≤ y^2 →
      ∀ r, (∑ x ∈ X with x ≡ r [MOD sieveProduct U], |w x|) ≤ A)
    (Ap : 0 ≤ A) :
    (∑ x ∈ X, ∑ y ∈ X, w x*w y*(pairGamma P m x y)^2) ≤
      c^2*exp (8/(d:ℝ))+(A*∑ x∈X, |w x|)*(∑ T∈P.powerset, pairDivisorWeight T) := by
  classical
  rw [weighted_pair_gamma X P pr m w]
  have positive (T : Finset ℕ) (h : T⊆P) : 0 ≤ pairDivisorWeight T := by
    apply prod_nonneg; intro p hp
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast (pr p (h hp)).two_le
    exact div_nonneg (by linarith) (sq_nonneg _)
  have sum := sum_le_sum (s:=P.powerset) (fun T h => show pairDivisorWeight T *
      (∑ r ∈ range (sieveProduct T) with ∀ p∈T, ¬r ≡ m [MOD p],
        (∑ x ∈ X with x%(sieveProduct T)=r, w x)^2) ≤
        c^2*(pairDivisorWeight T/(sieveProduct T:ℝ))+(A*∑ x∈X, |w x|)*pairDivisorWeight T by
    have sub := mem_powerset.mp h
    have qpos : 0 < sieveProduct T := prod_pos (fun p hp => (pr p (sub hp)).pos)
    have pos := positive T sub
    by_cases low : sieveProduct T ≤ y
    · have u := mul_le_mul_of_nonneg_left (class_square_bound X w T m qpos c (short T sub low)) pos
      have tail := mul_nonneg (mul_nonneg Ap (sum_nonneg (s:=X) (fun i _ => abs_nonneg (w i)))) pos
      simp only [div_eq_mul_inv] at u ⊢
      linarith only [u,tail]
    · obtain ⟨U,ut,qlo,qhi⟩ := middle_subproduct T y yp (fun p hp => (size p (sub hp)).2) (by omega)
      have u := mul_le_mul_of_nonneg_left (prefix_square_bound X w T U ut m qpos A (mid U (ut.trans sub) qlo qhi)) pos
      have first := mul_nonneg (sq_nonneg c) (div_nonneg pos (Nat.cast_nonneg (α:=ℝ) (sieveProduct T)))
      linarith only [u,first])
  rw [sum_add_distrib,←mul_sum,←mul_sum] at sum
  exact sum.trans (add_le_add (mul_le_mul_of_nonneg_left
    (pair_weight_inverse_sum P pr d dp (fun p h => (size p h).1)) (sq_nonneg c)) le_rfl)

end Cogentic.Construction
