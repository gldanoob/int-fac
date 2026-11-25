import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Cogentic.Window

noncomputable section

/-- The local factor in the passage from the individual reduced progression
    to the reference Gaussian smooth mass. -/
def coprimeFactor (q : ℕ) : ℝ := (q:ℝ)/q.totient

theorem coprime_factor_primes (q : ℕ) (hq : 0 < q) :
    coprimeFactor q = ∏ p ∈ q.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
  have fp (p : ℕ) (h : p ∈ q.primeFactors) : 1 < (p:ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
  have pos : 0 < ∏ p ∈ q.primeFactors, ((p:ℝ)-1) :=
    Finset.prod_pos (fun p hp => sub_pos.mpr (fp p hp))
  have eq := congrArg ((↑):ℕ → ℝ) (Nat.totient_mul_prod_primeFactors q)
  push_cast at eq
  have sub (p : ℕ) (hp : p ∈ q.primeFactors) : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by
    rw [Nat.cast_sub (Nat.pos_of_mem_primeFactors hp),Nat.cast_one]
  rw [Finset.prod_congr rfl sub] at eq
  rw [coprimeFactor,Finset.prod_div_distrib,div_eq_div_iff
    (by exact_mod_cast (Nat.totient_pos.mpr hq).ne') pos.ne']
  linarith only [eq,mul_comm (q.totient:ℝ) (∏ p ∈ q.primeFactors, (p:ℝ))]

/-- Extra local factors are contributed once per newly appearing prime,
    independent of its exponent in the progression modulus. -/
theorem coprime_factor_quotient (q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    coprimeFactor (q*k)/coprimeFactor q =
      ∏ p ∈ k.primeFactors \ q.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
  rw [coprime_factor_primes (q*k) (mul_pos hq hk),coprime_factor_primes q hq,
    Nat.primeFactors_mul hq.ne' hk.ne']
  let F := fun p : ℕ => (p:ℝ)/((p:ℝ)-1)
  have nz : (∏ p ∈ q.primeFactors, F p) ≠ 0 := (Finset.prod_pos (fun p hp => div_pos
    (by exact_mod_cast Nat.pos_of_mem_primeFactors hp)
    (sub_pos.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)))).ne'
  rw [div_eq_iff nz]
  have dis : Disjoint (k.primeFactors \ q.primeFactors) q.primeFactors := Finset.sdiff_disjoint
  rw [← Finset.prod_union dis]
  congr 1
  ext p
  simp only [Finset.mem_union,Finset.mem_sdiff]
  tauto

/-- The contribution of the newly appearing primes above the smoothness
    cutoff has an explicit relative bound, with the smaller-prime product
    retained exactly. -/
theorem coprime_factor_large_remainder (q k : ℕ) (hq : 0 < q) (hk : 0 < k)
    (B : ℝ) (hB : 1 < B) :
    let P := k.primeFactors \ q.primeFactors
    let lo := P.filter (fun p : ℕ => (p:ℝ) ≤ B)
    let hi := P.filter (fun p : ℕ => B < (p:ℝ))
    let γ := ∏ p ∈ lo, (p:ℝ)/((p:ℝ)-1)
    γ ≤ coprimeFactor (q*k)/coprimeFactor q ∧
      coprimeFactor (q*k)/coprimeFactor q ≤ γ*Real.exp (hi.card/(B-1)) := by
  let P := k.primeFactors \ q.primeFactors
  let F := fun p : ℕ => (p:ℝ)/((p:ℝ)-1)
  let lo := P.filter (fun p : ℕ => (p:ℝ) ≤ B)
  let hi := P.filter (fun p : ℕ => B < (p:ℝ))
  have ge (p : ℕ) (hp : p ∈ P) : 1 ≤ F p := by
    have one : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).one_lt
    exact (le_div_iff₀ (by linarith : 0 < (p:ℝ)-1)).mpr (by linarith)
  have split : (∏ p ∈ lo, F p)*(∏ p ∈ hi, F p) = ∏ p ∈ P, F p := by
    simpa only [lo,hi,not_le] using Finset.prod_filter_mul_prod_filter_not P (fun p : ℕ => (p:ℝ) ≤ B) F
  have lower : 1 ≤ ∏ p ∈ hi, F p := Finset.one_le_prod (fun p hp => ge p (Finset.mem_filter.mp hp).1)
  have gp : 0 ≤ ∏ p ∈ lo, F p := Finset.prod_nonneg (fun p hp =>
    zero_le_one.trans (ge p (Finset.mem_filter.mp hp).1))
  have upper : (∏ p ∈ hi, F p) ≤ Real.exp (hi.card/(B-1)) := by
    have term (p : ℕ) (hp : p ∈ hi) : F p ≤ Real.exp (1/(B-1)) := by
      have small : B < p := (Finset.mem_filter.mp hp).2
      have pos : 0 < (p:ℝ)-1 := by linarith
      have identity : F p=1+1/((p:ℝ)-1) := by dsimp [F]; field_simp; ring
      rw [identity]
      have b := one_div_le_one_div_of_le (sub_pos.mpr hB) (by linarith : B-1 ≤ (p:ℝ)-1)
      linarith [Real.add_one_le_exp (1/(B-1))]
    exact (Finset.prod_le_prod (fun p hp => zero_le_one.trans (ge p (Finset.mem_filter.mp hp).1)) term).trans_eq
      (by rw [Finset.prod_const,← Real.exp_nat_mul]; congr 1; ring)
  change (∏ p ∈ lo, F p) ≤ _ ∧ _ ≤ (∏ p ∈ lo, F p)*Real.exp (hi.card/(B-1))
  rw [coprime_factor_quotient q k hq hk,← split]
  exact ⟨(mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left lower gp),mul_le_mul_of_nonneg_left upper gp⟩

/-- At primes outside the prescribed and fixed coefficients, the extra
    prime factors of the two-point modulus are exactly the diagonal
    coincidences appearing in the source's factor γ. -/
theorem new_evaluation_prime (a b m : ℤ) (G F U p : ℕ) (prime : p.Prime)
    (hab : b ≠ a) (hbm : b ≠ m) (hF : F ≠ 0) (hU : U ≠ 0)
    (hG : G ∣ (b-a).natAbs) (pG : ¬p ∣ G) (pF : ¬p ∣ F) (pU : ¬p ∣ U) :
    let extra := ((b-a).natAbs/G)*F
    let base := U*(b-m).natAbs
    p ∈ extra.primeFactors \ base.primeFactors ↔ (p:ℤ) ∣ b-a ∧ ¬(p:ℤ) ∣ a-m := by
  dsimp only
  have hD : (b-a).natAbs ≠ 0 := by simpa using sub_ne_zero.mpr hab
  have hA : (b-m).natAbs ≠ 0 := by simpa using sub_ne_zero.mpr hbm
  have eq := Nat.div_mul_cancel hG
  have hn : (b-a).natAbs/G ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at eq
    exact hD eq.symm
  have div : p ∣ (b-a).natAbs/G ↔ p ∣ (b-a).natAbs := by
    conv_rhs => rw [← eq,prime.dvd_mul]
    simp only [pG,or_false]
  have shift (hd : (p:ℤ) ∣ b-a) : (p:ℤ) ∣ b-m ↔ (p:ℤ) ∣ a-m := by
    constructor <;> intro h
    · rw [show a-m=(b-m)-(b-a) by ring]
      exact dvd_sub h hd
    · rw [show b-m=(a-m)+(b-a) by ring]
      exact dvd_add h hd
  rw [Finset.mem_sdiff,Nat.mem_primeFactors_of_ne_zero (mul_ne_zero hn hF),
    Nat.mem_primeFactors_of_ne_zero (mul_ne_zero hU hA)]
  simp only [prime,true_and,prime.dvd_mul,pU,pF,false_or,or_false,div,← Int.natCast_dvd]
  exact and_congr_right (fun h => not_congr (shift h))

/-- The small-prime part of the actual two-point progression correction is
    the γ-product over p dividing b-a but not a-m. -/
theorem two_point_coprime_correction (a b m : ℤ) (G F U d : ℕ) (B : ℝ)
    (hB : 1 < B) (hab : b ≠ a) (hbm : b ≠ m) (hF : F ≠ 0) (hU : U ≠ 0)
    (hG : G ∣ (b-a).natAbs)
    (localPrimes : ∀ p : ℕ, p.Prime → (p:ℝ) ≤ B → (p ∣ U ↔ p ≤ d) ∧ ¬p ∣ F ∧ ¬p ∣ G) :
    let D := (b-a).natAbs
    let k := D/G*F
    let q := U*(b-m).natAbs
    let S := D.primeFactors.filter (fun p : ℕ => d < p ∧ (p:ℝ) ≤ B ∧ ¬(p:ℤ) ∣ a-m)
    let γ := ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)
    let kHi := (k.primeFactors.filter (fun p : ℕ => B < (p:ℝ))).card
    γ ≤ coprimeFactor (q*k)/coprimeFactor q ∧
      coprimeFactor (q*k)/coprimeFactor q ≤ γ*Real.exp (kHi/(B-1)) := by
  classical
  let D := (b-a).natAbs
  let k := D/G*F
  let q := U*(b-m).natAbs
  let S := D.primeFactors.filter (fun p : ℕ => d < p ∧ (p:ℝ) ≤ B ∧ ¬(p:ℤ) ∣ a-m)
  let P := k.primeFactors \ q.primeFactors
  have hD : D ≠ 0 := by simpa [D] using sub_ne_zero.mpr hab
  have hA : (b-m).natAbs ≠ 0 := by simpa using sub_ne_zero.mpr hbm
  have hn : D/G ≠ 0 := by
    intro hz
    have eq : D/G*G=D := Nat.div_mul_cancel hG
    rw [hz, zero_mul] at eq
    exact hD eq.symm
  have kp : 0 < k := Nat.pos_of_ne_zero (mul_ne_zero hn hF)
  have qp : 0 < q := Nat.pos_of_ne_zero (mul_ne_zero hU hA)
  have loeq : P.filter (fun p : ℕ => (p:ℝ) ≤ B) = S := by
    ext p
    rw [Finset.mem_filter,Finset.mem_filter]
    constructor
    · rintro ⟨hp,pB⟩
      have pp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
      have loc := localPrimes p pp pB
      have pu : ¬p ∣ U := by
        intro dvd
        exact (Finset.mem_sdiff.mp hp).2 (pp.mem_primeFactors (dvd_mul_of_dvd_left dvd _) qp.ne')
      have info := (new_evaluation_prime a b m G F U p pp hab hbm hF hU hG loc.2.2 loc.2.1 pu).mp hp
      exact ⟨pp.mem_primeFactors (Int.natCast_dvd.mp info.1) hD,
        lt_of_not_ge (fun h => pu (loc.1.mpr h)),pB,info.2⟩
    · rintro ⟨mem,pd,pB,h⟩
      have pp := Nat.prime_of_mem_primeFactors mem
      have loc := localPrimes p pp pB
      have pu : ¬p ∣ U := fun dvd => pd.not_ge (loc.1.mp dvd)
      exact ⟨(new_evaluation_prime a b m G F U p pp hab hbm hF hU hG loc.2.2 loc.2.1 pu).mpr
        ⟨Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors mem),h⟩,pB⟩
  have est := coprime_factor_large_remainder q k qp kp B hB
  dsimp only at est ⊢
  rw [loeq] at est
  refine ⟨est.1,est.2.trans ?_⟩
  have gpos : 0 ≤ ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := Finset.prod_nonneg fun p hp =>
    div_nonneg (Nat.cast_nonneg _) (by
      have h := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h))
  apply mul_le_mul_of_nonneg_left _ gpos
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hB).le
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (fun p : ℕ => B < (p:ℝ))
    (Finset.sdiff_subset : P ⊆ k.primeFactors))

end

end Cogentic.Window
