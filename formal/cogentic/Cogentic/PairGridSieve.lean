import Cogentic.WeightedGridSieve
import Cogentic.ProgressionCorrection

namespace Cogentic.Construction
open Finset Real

/-- Small-prime correction shared by the two independent fields. -/
noncomputable def pairGamma (P : Finset ℕ) (m x y : ℕ) : ℝ :=
  ∏ p ∈ P with x ≡ y [MOD p] ∧ ¬x ≡ m [MOD p], (p:ℝ)/((p:ℝ)-1)

def sieveProduct (T : Finset ℕ) := ∏ p ∈ T, p

noncomputable def pairDivisorWeight (T : Finset ℕ) : ℝ :=
  ∏ p ∈ T, (2*(p:ℝ)-1)/((p:ℝ)-1)^2

theorem pair_gamma_square (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (m x y : ℕ) :
    pairGamma P m x y ^ 2 = ∑ T ∈ P.powerset,
      if x ≡ y [MOD sieveProduct T] ∧ ∀ p ∈ T, ¬x ≡ m [MOD p] then pairDivisorWeight T else 0 := by
  classical
  let hit := fun p => x ≡ y [MOD p] ∧ ¬x ≡ m [MOD p]
  let eta := fun p : ℕ => (2*(p:ℝ)-1)/((p:ℝ)-1)^2
  have point (p : ℕ) (hp : p ∈ P) : ((p:ℝ)/((p:ℝ)-1))^2 = 1+eta p := by
    have pp : 1 < (p:ℝ) := by exact_mod_cast (pr p hp).one_lt
    dsimp only [eta]; rw [div_pow]; field_simp [sub_ne_zero.mpr pp.ne']; ring
  have expand : pairGamma P m x y ^ 2 = ∏ p ∈ P, (1+if hit p then eta p else 0) := by
    rw [pairGamma,←Finset.prod_pow,Finset.prod_filter]
    apply prod_congr rfl
    intro p h; by_cases test : hit p
    · simp only [hit] at test; simp [hit,test,point p h]
    · simp only [hit] at test; simp [hit,test]
  rw [expand,prod_one_add]
  apply sum_congr rfl
  intro T h
  rw [prod_ite_zero]
  have same : (∀ p ∈ T, hit p) ↔ x ≡ y [MOD sieveProduct T] ∧ ∀ p ∈ T, ¬x ≡ m [MOD p] := by
    rw [sieveProduct,prime_product_modEq T (fun p hp => pr p (mem_powerset.mp h hp))]
    exact ⟨fun h => ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩,
      fun h p hp => ⟨h.1 p hp,h.2 p hp⟩⟩
  simp only [same,eta,pairDivisorWeight]

private theorem sum_class_squares (X : Finset ℕ) (w : ℕ → ℝ) (T : Finset ℕ) (m : ℕ)
    (pr : ∀ p ∈ T, p.Prime) :
    let q := sieveProduct T
    (∑ x ∈ X, ∑ y ∈ X, if x ≡ y [MOD q] ∧ ∀ p ∈ T, ¬x ≡ m [MOD p] then w x*w y else 0) =
      ∑ r ∈ range q with ∀ p ∈ T, ¬r ≡ m [MOD p], (∑ x ∈ X with x%q=r, w x)^2 := by
  classical
  intro q
  have qp : 0 < q := prod_pos (fun p hp => (pr p hp).pos)
  let good := fun r : ℕ => ∀ p ∈ T, ¬r ≡ m [MOD p]
  have cong (x r) (eq : x%q=r) : x ≡ r [MOD q] := by
    rw [←eq]; exact (Nat.mod_modEq ..).symm
  have transG (x r) (eq : x%q=r) : good x ↔ good r := by
    have pq (p) (h : p∈T) : x ≡ r [MOD p] := (cong x r eq).of_dvd (dvd_prod_of_mem id h)
    exact ⟨fun g p h f => g p h ((pq p h).trans f),fun g p h f => g p h ((pq p h).symm.trans f)⟩
  have maps : ∀ x ∈ X, x%q ∈ range q := fun x _ => mem_range.mpr (Nat.mod_lt x qp)
  rw [←sum_fiberwise_of_maps_to maps,Finset.sum_filter]
  apply sum_congr rfl
  intro r _
  by_cases gr : good r
  · rw [if_pos gr,sq,sum_mul]
    apply sum_congr rfl
    intro x hx
    have eq := (mem_filter.mp hx).2
    have gx := (transG x r eq).mpr gr
    rw [mul_sum,sum_filter]
    apply sum_congr rfl
    intro y _
    have iff : x ≡ y [MOD q] ∧ good x ↔ y%q=r := by change x%q=y%q ∧ good x ↔ _; rw [eq]; simp [gx,eq_comm]
    simp only [show (x ≡ y [MOD q] ∧ ∀ p ∈ T, ¬x ≡ m [MOD p]) ↔ y%q=r from iff]
  · rw [if_neg gr]
    apply sum_eq_zero
    intro x hx
    have ng := fun g => gr ((transG x r (mem_filter.mp hx).2).mp g)
    exact sum_eq_zero fun y _ => if_neg (fun h => ng h.2)

/-- The two-point singular series tested against signed centered mark
weights is exactly a sum of squares of eligible residue-class sums. -/
theorem weighted_pair_gamma (X P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (m : ℕ) (w : ℕ → ℝ) :
    (∑ x ∈ X, ∑ y ∈ X, w x*w y*(pairGamma P m x y)^2) =
      ∑ T ∈ P.powerset, pairDivisorWeight T *
        ∑ r ∈ range (sieveProduct T) with ∀ p ∈ T, ¬r ≡ m [MOD p],
          (∑ x ∈ X with x%(sieveProduct T)=r, w x)^2 := by
  classical
  let term := fun x y (T : Finset ℕ) =>
    if x ≡ y [MOD sieveProduct T] ∧ ∀ p ∈ T, ¬x ≡ m [MOD p] then w x*w y else 0
  have each (x y) : w x*w y*(pairGamma P m x y)^2 = ∑ T ∈ P.powerset, pairDivisorWeight T*term x y T := by
    rw [pair_gamma_square P pr,mul_sum]
    apply sum_congr rfl
    intro T _
    dsimp only [term]
    split <;> ring
  simp_rw [each]
  have swap (x : ℕ) := sum_comm (s:=X) (t:=P.powerset) (f:=fun y T => pairDivisorWeight T*term x y T)
  simp_rw [swap]
  rw [sum_comm]
  apply sum_congr rfl
  intro T h
  simp_rw [←mul_sum]
  exact congrArg (pairDivisorWeight T * ·) (sum_class_squares X w T m (fun p hp => pr p (mem_powerset.mp h hp)))

end Cogentic.Construction
