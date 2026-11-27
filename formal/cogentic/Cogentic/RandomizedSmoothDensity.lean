import Cogentic.RandomizedBalancedStrip
import Cogentic.RandomizedOneThirdAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic

namespace Cogentic.Randomized

open Finset Filter
open scoped BigOperators

/-!
# Explicit Smooth-Number and Prime-Bin Strip Density Bounds

This file proves:
1. Elementary two-sided Stirling bounds on `k!` and resulting lower bounds on `J.choose k`.
2. Concrete and asymptotic density lower bounds for the balanced prime-bin strip
   (`centeredBinProducts`), connecting `centeredBinProducts_population`,
   `primeBinPatternProducts_card_lower`, and `primeBin_supply_from_critical_line`.
3. `L_N[1/3, c]` parameter scaling matching `Cogentic.RandomizedOneThirdAsymptotic.scale`.
4. Elementary Rankin upper bounds for `y`-smooth integer counts and weighted `y`-smooth
   reciprocal sums via finite Euler product expansion.
-/

/-! ## Section 1: Elementary Stirling and Binomial Lower Bounds -/

/-- Elementary Stirling lower bound: `k^k * exp (1 - k) ≤ k!` for all `1 ≤ k`. -/
theorem factorial_ge_pow_mul_exp {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ k * Real.exp (1 - (k : ℝ)) ≤ (k.factorial : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hstep : ((k : ℝ) + 1) ^ k ≤ (k : ℝ) ^ k * Real.exp 1 := by
      have h1 : 1 + 1 / (k : ℝ) ≤ Real.exp (1 / (k : ℝ)) := by
        linarith only [Real.add_one_le_exp (1 / (k : ℝ))]
      have hpow := pow_le_pow_left₀ (by positivity) h1 k
      rw [← Real.exp_nat_mul, mul_one_div_cancel hkpos.ne'] at hpow
      have heq : (1 + 1 / (k : ℝ)) ^ k = ((k : ℝ) + 1) ^ k / (k : ℝ) ^ k := by
        rw [← div_pow, show 1 + 1 / (k : ℝ) = ((k : ℝ) + 1) / (k : ℝ) by field_simp]
      rw [heq, div_le_iff₀ (pow_pos hkpos k)] at hpow
      simpa only [mul_comm] using hpow
    have hexp : Real.exp (1 - ((k + 1 : ℕ) : ℝ)) * Real.exp 1 = Real.exp (1 - (k : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      ((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.exp (1 - ((k + 1 : ℕ) : ℝ))
          = ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ k * Real.exp (1 - ((k + 1 : ℕ) : ℝ))) := by
              push_cast
              rw [pow_succ']
              ring
      _ ≤ ((k : ℝ) + 1) * (((k : ℝ) ^ k * Real.exp 1) * Real.exp (1 - ((k + 1 : ℕ) : ℝ))) := by
              gcongr
      _ = ((k : ℝ) + 1) * ((k : ℝ) ^ k * Real.exp (1 - (k : ℝ))) := by
              rw [mul_assoc ((k : ℝ) ^ k), mul_comm (Real.exp 1), hexp]
      _ ≤ ((k : ℝ) + 1) * (k.factorial : ℝ) := by gcongr
      _ = ((k + 1).factorial : ℝ) := by
              rw [Nat.factorial_succ]
              push_cast
              ring

/-- Elementary Stirling upper bound: `k! ≤ k * k^k * exp (1 - k)` for all `1 ≤ k`. -/
theorem factorial_le_mul_pow_mul_exp {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℝ) ≤ (k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ)) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hlog : 1 / ((k : ℝ) + 1) ≤ Real.log (((k : ℝ) + 1) / (k : ℝ)) := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hkpos hk1pos)
      rw [Real.log_div hkpos.ne' hk1pos.ne'] at h1
      rw [Real.log_div hk1pos.ne' hkpos.ne']
      have hsub : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
      linarith only [h1, hsub]
    have hstep : Real.exp 1 ≤ (((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hlog hk1pos.le
      rw [mul_one_div_cancel hk1pos.ne'] at hmul
      have hexp := Real.exp_le_exp.mpr hmul
      rwa [show ((k : ℝ) + 1) * Real.log (((k : ℝ) + 1) / (k : ℝ)) =
            Real.log ((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)) by
            rw [Real.log_pow]; push_cast; ring,
          Real.exp_log (pow_pos (div_pos hk1pos hkpos) _)] at hexp
    have hpow : (k : ℝ) ^ (k + 1) * Real.exp 1 ≤ ((k : ℝ) + 1) ^ (k + 1) := by
      rw [div_pow, le_div_iff₀ (pow_pos hkpos (k + 1))] at hstep
      linarith only [hstep]
    have hexp : Real.exp (1 - (k : ℝ)) = Real.exp 1 * Real.exp (1 - ((k + 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc
      ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ))) := by gcongr
      _ = ((k : ℝ) + 1) * (((k : ℝ) ^ (k + 1) * Real.exp 1) * Real.exp (1 - ((k + 1 : ℕ) : ℝ))) := by
        rw [hexp, pow_succ']
        ring
      _ ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ (k + 1) * Real.exp (1 - ((k + 1 : ℕ) : ℝ))) := by
        gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.exp (1 - ((k + 1 : ℕ) : ℝ)) := by
        push_cast
        ring

private theorem descFactorial_eq_prod_range (J k : ℕ) :
    J.descFactorial k = ∏ i ∈ range k, (J - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, ih, mul_comm]

/-- Lower bound `((J - k)^k) / k! ≤ J.choose k` for `k ≤ J`. -/
theorem choose_ge_sub_pow_div_factorial {J k : ℕ} (hkJ : k ≤ J) :
    ((J - k : ℝ) ^ k) / (k.factorial : ℝ) ≤ (J.choose k : ℝ) := by
  have hnat : (J - k) ^ k ≤ k.factorial * J.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod_range]
    calc
      (J - k) ^ k = ∏ _i ∈ range k, (J - k) := by simp
      _ ≤ ∏ i ∈ range k, (J - i) := Finset.prod_le_prod' fun i hi =>
        Nat.sub_le_sub_left (mem_range.mp hi).le J
  have hreal : ((J - k : ℝ) ^ k) ≤ (k.factorial : ℝ) * (J.choose k : ℝ) := by
    have hcast : (((J - k : ℕ) : ℝ) ^ k) ≤ (k.factorial : ℝ) * (J.choose k : ℝ) := by
      exact_mod_cast hnat
    rwa [Nat.cast_sub hkJ] at hcast
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k))).mpr (by linarith only [hreal])

/-- Stirling binomial lower bound: `((J - k) / k)^k * (exp (k - 1) / k) ≤ J.choose k`
for `1 ≤ k ≤ J`. -/
theorem choose_ge_stirling {J k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    ((J - k : ℝ) / (k : ℝ)) ^ k * (Real.exp ((k : ℝ) - 1) / (k : ℝ)) ≤ (J.choose k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsub : 0 ≤ (J : ℝ) - (k : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hkJ)
  have hfac := factorial_le_mul_pow_mul_exp hk
  have hfacpos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hdenpos : 0 < (k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ)) := by positivity
  have hinv : 1 / ((k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ))) ≤ 1 / (k.factorial : ℝ) :=
    one_div_le_one_div_of_le hfacpos hfac
  have hnum : ((J - k : ℝ) / (k : ℝ)) ^ k * (Real.exp ((k : ℝ) - 1) / (k : ℝ)) =
      ((J - k : ℝ) ^ k) * (1 / ((k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ)))) := by
    rw [div_pow, show (k : ℝ) - 1 = -(1 - (k : ℝ)) by ring, Real.exp_neg]
    field_simp
  calc
    ((J - k : ℝ) / (k : ℝ)) ^ k * (Real.exp ((k : ℝ) - 1) / (k : ℝ))
        = ((J - k : ℝ) ^ k) * (1 / ((k : ℝ) * (k : ℝ) ^ k * Real.exp (1 - (k : ℝ)))) := hnum
    _ ≤ ((J - k : ℝ) ^ k) * (1 / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hsub k)
    _ = ((J - k : ℝ) ^ k) / (k.factorial : ℝ) := by ring
    _ ≤ (J.choose k : ℝ) := choose_ge_sub_pow_div_factorial hkJ

/-- Elementary ratio lower bound: `(J / k)^k ≤ J.choose k` for `1 ≤ k ≤ J`. -/
theorem choose_ge_div_pow {J k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    ((J : ℝ) / (k : ℝ)) ^ k ≤ (J.choose k : ℝ) := by
  have hprod : J ^ k * k.factorial ≤ k ^ k * (k.factorial * J.choose k) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, ← Nat.descFactorial_self k,
      descFactorial_eq_prod_range, descFactorial_eq_prod_range]
    calc
      J ^ k * ∏ i ∈ range k, (k - i)
          = (∏ _i ∈ range k, J) * ∏ i ∈ range k, (k - i) := by simp
      _ = ∏ i ∈ range k, (J * (k - i)) := by rw [Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ range k, (k * (J - i)) := by
            refine Finset.prod_le_prod' fun i hi => ?_
            rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, Nat.mul_comm J k]
            exact Nat.sub_le_sub_left (Nat.mul_le_mul_right i hkJ) (k * J)
      _ = (∏ _i ∈ range k, k) * ∏ i ∈ range k, (J - i) := by rw [Finset.prod_mul_distrib]
      _ = k ^ k * ∏ i ∈ range k, (J - i) := by simp
  have hnat : J ^ k ≤ k ^ k * J.choose k := by
    have hmul : k.factorial * J ^ k ≤ k.factorial * (k ^ k * J.choose k) := by
      linarith only [hprod]
    exact Nat.le_of_mul_le_mul_left hmul (Nat.factorial_pos k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [div_pow, div_le_iff₀ (pow_pos hkpos k)]
  have hreal : (J : ℝ) ^ k ≤ (k : ℝ) ^ k * (J.choose k : ℝ) := by exact_mod_cast hnat
  linarith only [hreal]

/-! ## Section 2: Prime-Bin Strip Density Lower Bounds -/

/-- Real-valued pigeonhole bound: some index-sum fiber of `k`-subsets of `range J`
has cardinality at least `J.choose k / (k * J)`. -/
theorem exists_large_centeredBinPatterns {J k : ℕ} (hJ : 1 ≤ J) (hk : 1 ≤ k) :
    ∃ a ∈ range (k * (J - 1) + 1),
      (J.choose k : ℝ) / ((k : ℝ) * (J : ℝ)) ≤ ((centeredBinPatterns J k a).card : ℝ) := by
  let M := k * (J - 1) + 1
  have hMpos : 0 < M := Nat.succ_pos _
  have hMle : M ≤ k * J := by
    dsimp only [M]
    have h1 : k * (J - 1) + k = k * J := by
      rw [← mul_add_one, Nat.sub_add_cancel hJ]
    omega
  have hmaps : ∀ s ∈ (range J).powersetCard k, (∑ j ∈ s, j) ∈ range M := by
    intro s hs
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
    have hsum : (∑ j ∈ s, j) ≤ k * (J - 1) := by
      calc
        (∑ j ∈ s, j) ≤ ∑ _j ∈ s, (J - 1) := sum_le_sum fun j hj => by
          have := mem_range.mp (hsub hj)
          omega
        _ = k * (J - 1) := by simp [hcard]
    exact mem_range.mpr (by omega)
  have hsum_card : ∑ a ∈ range M, (centeredBinPatterns J k a).card = J.choose k := by
    have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_powersetCard, Finset.card_range] at hfiber
    simpa only [centeredBinPatterns] using hfiber.symm
  have hsum_real : ∑ a ∈ range M, ((centeredBinPatterns J k a).card : ℝ) = (J.choose k : ℝ) := by
    exact_mod_cast hsum_card
  have hex : ∃ a ∈ range M, (J.choose k : ℝ) / (M : ℝ) ≤ ((centeredBinPatterns J k a).card : ℝ) := by
    by_contra! hlt
    have hstrict :
        (∑ a ∈ range M, ((centeredBinPatterns J k a).card : ℝ)) <
          ∑ _a ∈ range M, ((J.choose k : ℝ) / (M : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hMpos.ne') hlt
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hMpos.ne'), hsum_real] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨a, ha, hcard⟩ := hex
  refine ⟨a, ha, ?_⟩
  have hdiv : (J.choose k : ℝ) / ((k : ℝ) * (J : ℝ)) ≤ (J.choose k : ℝ) / (M : ℝ) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr hMpos)
    exact_mod_cast hMle
  exact hdiv.trans hcard

/-- Uniform-bin lower bound combining `exists_large_centeredBinPatterns` and
`primeBinPatternProducts_card_lower`. -/
theorem primeBinPatternProducts_uniform_lower (A B : ℕ → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    {J m q : ℕ} (hJ : 1 ≤ J) (hm : 1 ≤ m)
    (hpop : ∀ j < J, q ≤ (primeBin (A j) (B j)).card) :
    ∃ a ∈ range (m * (J - 1) + 1),
      (1 / ((m : ℝ) * (J : ℝ))) * (J.choose m : ℝ) * (q : ℝ) ^ m ≤
        ((primeBinPatternProducts A B (centeredBinPatterns J m a)).card : ℝ) := by
  obtain ⟨a, ha, hcard⟩ := exists_large_centeredBinPatterns hJ hm
  refine ⟨a, ha, ?_⟩
  have hlow := primeBinPatternProducts_card_lower A B hdisj (centeredBinPatterns J m a) m q
    (fun s hs => (mem_powersetCard.mp (mem_filter.mp hs).1).2)
    (fun s hs j hj => hpop j (mem_range.mp ((mem_powersetCard.mp (mem_filter.mp hs).1).1 hj)))
  have hreal : ((centeredBinPatterns J m a).card : ℝ) * (q : ℝ) ^ m ≤
      ((primeBinPatternProducts A B (centeredBinPatterns J m a)).card : ℝ) := by
    exact_mod_cast hlow
  calc
    (1 / ((m : ℝ) * (J : ℝ))) * (J.choose m : ℝ) * (q : ℝ) ^ m
        = ((J.choose m : ℝ) / ((m : ℝ) * (J : ℝ))) * (q : ℝ) ^ m := by ring
    _ ≤ ((centeredBinPatterns J m a).card : ℝ) * (q : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((primeBinPatternProducts A B (centeredBinPatterns J m a)).card : ℝ) := hreal

/-- General prime-bin strip density lower bound for disjoint bins with per-bin
lower endpoints `ep j` multiplying to `X` on every pattern of sum `a`. -/
theorem primeBinPatternProducts_density_lower (A B : ℕ → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (ep : ℕ → ℝ) {X c₀ δ y : ℝ} {J m a : ℕ}
    (hX : 0 < X) (hc₀ : 0 ≤ c₀) (hδ : 0 ≤ δ) (hy : 1 < y)
    (hep : ∀ j < J, 0 ≤ ep j)
    (hprod : ∀ s ∈ centeredBinPatterns J m a, (∏ j ∈ s, ep j) = X)
    (hpop : ∀ j < J, c₀ * δ * ep j / Real.log y ≤ ((primeBin (A j) (B j)).card : ℝ)) :
    ((centeredBinPatterns J m a).card : ℝ) * (c₀ * δ / Real.log y) ^ m ≤
      ((primeBinPatternProducts A B (centeredBinPatterns J m a)).card : ℝ) / X := by
  let W := c₀ * δ / Real.log y
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hW : 0 ≤ W := div_nonneg (mul_nonneg hc₀ hδ) hlog.le
  rw [le_div_iff₀ hX, primeBinPatternProducts_card A B hdisj, Nat.cast_sum]
  calc
    ((centeredBinPatterns J m a).card : ℝ) * W ^ m * X
        = ∑ _s ∈ centeredBinPatterns J m a, X * W ^ m := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    _ ≤ ∑ s ∈ centeredBinPatterns J m a,
          ((primeBinProducts (fun i : s => A i) (fun i : s => B i)).card : ℝ) := by
            refine Finset.sum_le_sum fun s hs => ?_
            obtain ⟨hset, _⟩ := mem_filter.mp hs
            obtain ⟨hsub, hsize⟩ := mem_powersetCard.mp hset
            rw [primeBinProducts_card _ _ (fun i j hij => hdisj (Subtype.val_injective.ne hij)),
              Nat.cast_prod]
            calc
              X * W ^ m = ∏ j : s, (ep j * W) := by
                rw [Finset.prod_mul_distrib, Finset.prod_coe_sort s ep, hprod s hs,
                  Finset.prod_const, Finset.card_univ, Fintype.card_coe, hsize]
              _ ≤ ∏ j : s, ((primeBin (A j) (B j)).card : ℝ) := by
                refine Finset.prod_le_prod (fun j _ => mul_nonneg (hep j (mem_range.mp (hsub j.2))) hW)
                  fun j _ => ?_
                have hj := hpop j (mem_range.mp (hsub j.2))
                calc ep j * W = c₀ * δ * ep j / Real.log y := by dsimp only [W]; ring
                  _ ≤ _ := hj

/-- Every integer in `centeredBinProducts P δ J k a` is `y`-smooth once all upper
bin floors are at most `y`. -/
theorem centeredBinProducts_smooth {P δ y : ℝ} {J k a n : ℕ}
    (hy : ∀ j < J, (centeredBinFloor P δ a k (j + 1) : ℝ) ≤ y)
    (hn : n ∈ centeredBinProducts P δ J k a) :
    ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y := by
  unfold centeredBinProducts primeBinPatternProducts at hn
  obtain ⟨s, hs, hprod⟩ := mem_biUnion.mp hn
  have hsub := (mem_powersetCard.mp (mem_filter.mp hs).1).1
  obtain ⟨f, hf, rfl⟩ := mem_image.mp hprod
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hpPrime).dvd_finsetProd_iff f).mp hdvd
  have hfi := Fintype.mem_piFinset.mp hf i
  have hfiPrime := (mem_filter.mp hfi).2
  have hpeq : p = f i := (Nat.prime_dvd_prime_iff_eq hpPrime hfiPrime).mp hi
  have hle : f i ≤ centeredBinFloor P δ a k (i + 1) := (mem_Ioc.mp (mem_filter.mp hfi).1).2
  rw [hpeq]
  exact (Nat.cast_le.mpr hle).trans (hy i (mem_range.mp (hsub i.2)))

/-- Concrete prime-bin strip density lower bound from `PrimeBinSupplyBound` with
`a`-independent rounding and supply guards. -/
theorem centeredBinProducts_density_of_supply (supply : PrimeBinSupplyBound) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P δ c y : ℝ) (J m : ℕ),
      0 < P → 0 ≤ δ → 0 ≤ c → 1 < y → 1 ≤ J → 1 ≤ m →
      (2 : ℝ) ≤ P * Real.exp (-(δ * (J : ℝ))) →
      P * Real.exp (δ * (J : ℝ)) ≤ y →
      K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 ≤
        (1 - c) * δ * (P * Real.exp (-(δ * (J : ℝ)))) →
      ∃ a ∈ range (m * (J - 1) + 1),
        (1 / ((m : ℝ) * (J : ℝ))) * (J.choose m : ℝ) * (c * δ / Real.log y) ^ m ≤
          ((centeredBinProducts P δ J m a).card : ℝ) / P ^ m ∧
        (∀ n ∈ centeredBinProducts P δ J m a,
          P ^ m ≤ (n : ℝ) ∧ (n : ℝ) ≤ P ^ m * Real.exp ((m : ℝ) * δ) ∧
          ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y) := by
  obtain ⟨K, hK, hpop⟩ := centeredBinProducts_population supply
  refine ⟨K, hK, ?_⟩
  intro P δ c y J m hP hδ hc hy hJ hm hlo hhi hguard
  obtain ⟨a, ha, hcard⟩ := exists_large_centeredBinPatterns hJ hm
  have hmpos : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have ha_le : (a : ℝ) / (m : ℝ) ≤ (J : ℝ) := by
    have ha1 : a ≤ m * (J - 1) := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have ha2 : a ≤ m * J := ha1.trans (Nat.mul_le_mul_left m (Nat.sub_le J 1))
    exact (div_le_iff₀ hmr).mpr (by rw [mul_comm]; exact_mod_cast ha2)
  have ha_nonneg : 0 ≤ (a : ℝ) / (m : ℝ) := by positivity
  have hbin_lo (j : ℕ) : P * Real.exp (-(δ * (J : ℝ))) ≤ centeredBinEndpoint P δ a m j := by
    unfold centeredBinEndpoint
    apply mul_le_mul_of_nonneg_left _ hP.le
    apply Real.exp_le_exp.mpr
    have h1 : -(J : ℝ) ≤ (j : ℝ) - (a : ℝ) / (m : ℝ) := by
      linarith only [ha_le, Nat.cast_nonneg (α := ℝ) j]
    nlinarith only [hδ, h1]
  have hbin_hi (j : ℕ) (hj : j < J) : centeredBinEndpoint P δ a m (j + 1) ≤ y := by
    refine le_trans ?_ hhi
    unfold centeredBinEndpoint
    apply mul_le_mul_of_nonneg_left _ hP.le
    apply Real.exp_le_exp.mpr
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast (show j + 1 ≤ J by omega)
    have h1 : ((j + 1 : ℕ) : ℝ) - (a : ℝ) / (m : ℝ) ≤ (J : ℝ) := by linarith only [hj1, ha_nonneg]
    nlinarith only [hδ, h1]
  have hfloor_hi (j : ℕ) (hj : j < J) : (centeredBinFloor P δ a m (j + 1) : ℝ) ≤ y := by
    unfold centeredBinFloor
    exact (Nat.floor_le (mul_nonneg hP.le (Real.exp_pos _).le)).trans (hbin_hi j hj)
  have hguards : ∀ j < J,
      2 ≤ centeredBinFloor P δ a m j ∧
      (centeredBinFloor P δ a m (j + 1) : ℝ) ≤ y ∧
      K * (1 + Real.log (3 * (centeredBinFloor P δ a m (j + 1) : ℝ))) ^ 2 *
        Real.sqrt (centeredBinFloor P δ a m (j + 1)) + 1 ≤
        (1 - c) * δ * centeredBinEndpoint P δ a m j := by
    intro j hj
    have hA : 2 ≤ centeredBinFloor P δ a m j := by
      unfold centeredBinFloor
      exact Nat.le_floor (hlo.trans (hbin_lo j))
    have hBy : (centeredBinFloor P δ a m (j + 1) : ℝ) ≤ y := hfloor_hi j hj
    have hB2 : 2 ≤ centeredBinFloor P δ a m (j + 1) := by
      unfold centeredBinFloor
      exact Nat.le_floor (hlo.trans (hbin_lo (j + 1)))
    have hBpos : (0 : ℝ) < centeredBinFloor P δ a m (j + 1) := by
      exact_mod_cast (show 0 < centeredBinFloor P δ a m (j + 1) by omega)
    have hlog_nonneg : 0 ≤ 1 + Real.log (3 * (centeredBinFloor P δ a m (j + 1) : ℝ)) := by
      have hge1 : (1 : ℝ) ≤ 3 * (centeredBinFloor P δ a m (j + 1) : ℝ) := by
        have h2 : (2 : ℝ) ≤ centeredBinFloor P δ a m (j + 1) := by exact_mod_cast hB2
        linarith
      linarith only [Real.log_nonneg hge1]
    have hlog_le : 1 + Real.log (3 * (centeredBinFloor P δ a m (j + 1) : ℝ)) ≤
        1 + Real.log (3 * y) := by
      gcongr
    have hsq_le : (1 + Real.log (3 * (centeredBinFloor P δ a m (j + 1) : ℝ))) ^ 2 ≤
        (1 + Real.log (3 * y)) ^ 2 :=
      pow_le_pow_left₀ hlog_nonneg hlog_le 2
    have hsqrt_le : Real.sqrt (centeredBinFloor P δ a m (j + 1)) ≤ Real.sqrt y :=
      Real.sqrt_le_sqrt hBy
    have h1mc : 0 ≤ 1 - c := by
      by_contra hneg
      push_neg at hneg
      have hposL : 0 < K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 := by positivity
      have hnonposR : (1 - c) * δ * (P * Real.exp (-(δ * (J : ℝ)))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg.le hδ)
          (mul_nonneg hP.le (Real.exp_pos _).le)
      linarith only [hguard, hposL, hnonposR]
    have hE_le : K * (1 + Real.log (3 * (centeredBinFloor P δ a m (j + 1) : ℝ))) ^ 2 *
          Real.sqrt (centeredBinFloor P δ a m (j + 1)) + 1 ≤
        K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 := by
      gcongr
    have hR_le : (1 - c) * δ * (P * Real.exp (-(δ * (J : ℝ)))) ≤
        (1 - c) * δ * centeredBinEndpoint P δ a m j :=
      mul_le_mul_of_nonneg_left (hbin_lo j) (mul_nonneg h1mc hδ)
    exact ⟨hA, hBy, hE_le.trans (hguard.trans hR_le)⟩
  have hmain := hpop P δ c y J m a hP.le hδ hc hy hmpos hguards
  refine ⟨a, ha, ?_, ?_⟩
  · rw [le_div_iff₀ (pow_pos hP m)]
    have hW : 0 ≤ (c * δ / Real.log y) ^ m :=
      pow_nonneg (div_nonneg (mul_nonneg hc hδ) (Real.log_pos hy).le) m
    calc
      (1 / ((m : ℝ) * (J : ℝ))) * (J.choose m : ℝ) * (c * δ / Real.log y) ^ m * P ^ m
          = ((J.choose m : ℝ) / ((m : ℝ) * (J : ℝ))) * (P ^ m * (c * δ / Real.log y) ^ m) := by ring
      _ ≤ ((centeredBinPatterns J m a).card : ℝ) * (P ^ m * (c * δ / Real.log y) ^ m) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (pow_pos hP m).le hW)
      _ = ((centeredBinPatterns J m a).card : ℝ) * P ^ m * (c * δ / Real.log y) ^ m := by ring
      _ ≤ ((centeredBinProducts P δ J m a).card : ℝ) := hmain
  · intro n hn
    have hstrip := centeredBinProducts_mem_strip hP.le hmpos hn
    exact ⟨hstrip.1, hstrip.2, centeredBinProducts_smooth hfloor_hi hn⟩

/-- The concrete prime-bin strip density lower bound under `DirichletLZerosOnLine`. -/
theorem centeredBinProducts_density_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P δ c y : ℝ) (J m : ℕ),
      0 < P → 0 ≤ δ → 0 ≤ c → 1 < y → 1 ≤ J → 1 ≤ m →
      (2 : ℝ) ≤ P * Real.exp (-(δ * (J : ℝ))) →
      P * Real.exp (δ * (J : ℝ)) ≤ y →
      K * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y + 1 ≤
        (1 - c) * δ * (P * Real.exp (-(δ * (J : ℝ)))) →
      ∃ a ∈ range (m * (J - 1) + 1),
        (1 / ((m : ℝ) * (J : ℝ))) * (J.choose m : ℝ) * (c * δ / Real.log y) ^ m ≤
          ((centeredBinProducts P δ J m a).card : ℝ) / P ^ m ∧
        (∀ n ∈ centeredBinProducts P δ J m a,
          P ^ m ≤ (n : ℝ) ∧ (n : ℝ) ≤ P ^ m * Real.exp ((m : ℝ) * δ) ∧
          ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y) :=
  centeredBinProducts_density_of_supply (primeBin_supply_from_critical_line line)

/-- Helper: `J * δ ≥ cH * log y / log u` together with `δ ≤ Cδ / m` and
`Cδ * log u ≤ cH * log y` implies `m ≤ J`. -/
theorem eventually_le_bins_of_width {u y δ : ℕ → ℝ} {J m : ℕ → ℕ} {cH Cδ : ℝ}
    (hu : Tendsto u atTop atTop) (hCδ : 0 < Cδ)
    (hm : ∀ᶠ n in atTop, 1 ≤ m n)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hδup : ∀ᶠ n in atTop, δ n ≤ Cδ / (m n : ℝ))
    (hJδ : ∀ᶠ n in atTop, cH * Real.log (y n) / Real.log (u n) ≤ (J n : ℝ) * δ n)
    (hlog : ∀ᶠ n in atTop, Cδ * Real.log (u n) ≤ cH * Real.log (y n)) :
    ∀ᶠ n in atTop, m n ≤ J n := by
  filter_upwards [hu.eventually_gt_atTop 1, hm, hδpos, hδup, hJδ, hlog] with
    n hu1 hmn hδp hδu hJd hl
  have hlu : 0 < Real.log (u n) := Real.log_pos hu1
  have hmr : (0 : ℝ) < m n := by exact_mod_cast (show 0 < m n by omega)
  have h1 : Cδ ≤ (J n : ℝ) * δ n := ((le_div_iff₀ hlu).mpr hl).trans hJd
  have h2 : (J n : ℝ) * δ n ≤ (J n : ℝ) * (Cδ / (m n : ℝ)) :=
    mul_le_mul_of_nonneg_left hδu (Nat.cast_nonneg _)
  have h3 : Cδ * (m n : ℝ) ≤ (J n : ℝ) * Cδ := by
    have h := h1.trans h2
    rw [← mul_div_assoc, le_div_iff₀ hmr] at h
    exact h
  have h4 : (m n : ℝ) ≤ (J n : ℝ) := by nlinarith only [h3, hCδ]
  exact_mod_cast h4

/-- Explicit asymptotic leading exponent theorem for the prime-bin strip lower bound:
for `u(n) → ∞`, `m = ⌈u (1 + 1 / log u)⌉`, `J * δ ≥ cH * log y / log u`, `m ≤ J`,
and `log (m^2 * J) = o(u * log u)`, eventually
`(1 / (m * J)) * (J.choose m) * (c₀ * δ / log y)^m ≥ exp (-(1 + ε) * u * log u)`. -/
theorem eventually_primeBinStrip_density_lower
    {u y δ : ℕ → ℝ} {J : ℕ → ℕ} {c₀ cH ε : ℝ}
    (hu : Tendsto u atTop atTop)
    (hc₀ : 0 < c₀) (hcH : 0 < cH) (hε : 0 < ε)
    (hy : ∀ᶠ n in atTop, 1 < y n)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hJδ : ∀ᶠ n in atTop, cH * Real.log (y n) / Real.log (u n) ≤ (J n : ℝ) * δ n)
    (hJm : ∀ᶠ n in atTop, ⌈u n * (1 + 1 / Real.log (u n))⌉₊ ≤ J n)
    (hlog : Asymptotics.IsLittleO atTop
      (fun n => Real.log ((⌈u n * (1 + 1 / Real.log (u n))⌉₊ : ℝ) ^ 2 * (J n : ℝ)))
      (fun n => u n * Real.log (u n))) :
    ∀ᶠ n in atTop,
      let m := ⌈u n * (1 + 1 / Real.log (u n))⌉₊
      Real.exp (-(1 + ε) * u n * Real.log (u n)) ≤
        (1 / ((m : ℝ) * (J n : ℝ))) * ((J n).choose m : ℝ) *
          (c₀ * δ n / Real.log (y n)) ^ m := by
  let C := c₀ * cH
  have hC : 0 < C := mul_pos hc₀ hcH
  have hlog_u : Tendsto (fun n => Real.log (u n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hu
  have hloglog_o : Asymptotics.IsLittleO atTop
      (fun n => Real.log (Real.log (u n))) (fun n => Real.log (u n)) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto hlog_u
    simpa only [Function.comp_def, Real.rpow_one] using h1
  let K : ℝ := 2 + |Real.log C| + Real.log 3
  have hK : 0 < K := by
    have : 0 ≤ |Real.log C| := abs_nonneg _
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    dsimp [K]
    linarith
  have hη : 0 < ε / 4 := by positivity
  filter_upwards [
    hu.eventually_ge_atTop 3,
    hlog_u.eventually_ge_atTop (max 2 (8 * K / ε)),
    hloglog_o.def (show 0 < ε / 8 by positivity),
    hlog.def hη,
    hy, hδ, hJδ, hJm] with n hu3 hlu hll hlogJ hyn hδn hJδn hJmn
  dsimp only
  set m := ⌈u n * (1 + 1 / Real.log (u n))⌉₊ with hm_def
  have hu_pos : 0 < u n := by linarith only [hu3]
  have hlu2 : 2 ≤ Real.log (u n) := (le_max_left ..).trans hlu
  have hlu_pos : 0 < Real.log (u n) := by linarith only [hlu2]
  have hluK : 8 * K / ε ≤ Real.log (u n) := (le_max_right ..).trans hlu
  have hly_pos : 0 < Real.log (y n) := Real.log_pos hyn
  have hm_ge_u : u n ≤ (m : ℝ) := by
    have h1 : u n ≤ u n * (1 + 1 / Real.log (u n)) := by
      have : 0 ≤ u n / Real.log (u n) := by positivity
      linarith only [show u n * (1 + 1 / Real.log (u n)) = u n + u n / Real.log (u n) by ring, this]
    exact h1.trans (Nat.le_ceil _)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ (m : ℝ) := by linarith only [hu3, hm_ge_u]
    exact_mod_cast this
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hJ1 : 1 ≤ J n := hm1.trans hJmn
  have hJ_pos : (0 : ℝ) < J n := by exact_mod_cast (show 0 < J n by omega)
  have hm_le_2u : (m : ℝ) ≤ 2 * u n := by
    have hceil : (m : ℝ) < u n * (1 + 1 / Real.log (u n)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hinv : 1 / Real.log (u n) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hlu2
    have hmul : u n * (1 + 1 / Real.log (u n)) ≤ (3 / 2 : ℝ) * u n := by
      nlinarith only [hu_pos, hinv]
    linarith only [hceil, hmul, hu3]
  have hm_le_tight : (m : ℝ) ≤ u n * (1 + 2 / Real.log (u n)) := by
    have hceil : (m : ℝ) < u n * (1 + 1 / Real.log (u n)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hlog_le_u : Real.log (u n) ≤ u n := by
      linarith only [Real.log_le_sub_one_of_pos hu_pos]
    have hone : 1 ≤ u n / Real.log (u n) := (one_le_div hlu_pos).mpr hlog_le_u
    have heq : u n * (1 + 2 / Real.log (u n)) =
        u n * (1 + 1 / Real.log (u n)) + u n / Real.log (u n) := by ring
    linarith only [hceil, hone, heq]
  have hlog_m : Real.log (m : ℝ) ≤ Real.log (u n) + Real.log 3 := by
    have h3 : (m : ℝ) ≤ 3 * u n := by linarith only [hm_le_2u, hu_pos]
    calc
      Real.log (m : ℝ) ≤ Real.log (3 * u n) := Real.log_le_log hm_pos h3
      _ = Real.log 3 + Real.log (u n) := Real.log_mul (by norm_num) hu_pos.ne'
      _ = Real.log (u n) + Real.log 3 := by ring
  -- Step 1: reduce binomial product using choose_ge_div_pow
  have hchoose := choose_ge_div_pow hm1 hJmn
  have hbase_le : C / ((m : ℝ) * Real.log (u n)) ≤
      ((J n : ℝ) / (m : ℝ)) * (c₀ * δ n / Real.log (y n)) := by
    have h1 := mul_le_mul_of_nonneg_left hJδn (div_nonneg hc₀.le (mul_pos hm_pos hly_pos).le)
    have hL : c₀ / ((m : ℝ) * Real.log (y n)) * (cH * Real.log (y n) / Real.log (u n)) =
        C / ((m : ℝ) * Real.log (u n)) := by
      dsimp [C]; field_simp
    have hR : c₀ / ((m : ℝ) * Real.log (y n)) * ((J n : ℝ) * δ n) =
        ((J n : ℝ) / (m : ℝ)) * (c₀ * δ n / Real.log (y n)) := by
      field_simp
    linarith only [h1, hL, hR]
  have hbase_pos : 0 < C / ((m : ℝ) * Real.log (u n)) := by positivity
  have hpow_le : (C / ((m : ℝ) * Real.log (u n))) ^ m ≤
      ((J n).choose m : ℝ) * (c₀ * δ n / Real.log (y n)) ^ m := by
    calc
      (C / ((m : ℝ) * Real.log (u n))) ^ m
          ≤ (((J n : ℝ) / (m : ℝ)) * (c₀ * δ n / Real.log (y n))) ^ m :=
              pow_le_pow_left₀ hbase_pos.le hbase_le m
      _ = ((J n : ℝ) / (m : ℝ)) ^ m * (c₀ * δ n / Real.log (y n)) ^ m := mul_pow _ _ _
      _ ≤ ((J n).choose m : ℝ) * (c₀ * δ n / Real.log (y n)) ^ m :=
              mul_le_mul_of_nonneg_right hchoose (pow_nonneg (div_nonneg (mul_nonneg hc₀.le hδn) hly_pos.le) m)
  -- Step 2: rewrite target as an exponential inequality
  have hRHS_ge : Real.exp (-(Real.log ((m : ℝ) * (J n : ℝ))) +
      (m : ℝ) * (Real.log C - Real.log (m : ℝ) - Real.log (Real.log (u n)))) ≤
      (1 / ((m : ℝ) * (J n : ℝ))) * ((J n).choose m : ℝ) * (c₀ * δ n / Real.log (y n)) ^ m := by
    have hlog_base : Real.log (C / ((m : ℝ) * Real.log (u n))) =
        Real.log C - Real.log (m : ℝ) - Real.log (Real.log (u n)) := by
      rw [Real.log_div hC.ne' (mul_pos hm_pos hlu_pos).ne', Real.log_mul hm_pos.ne' hlu_pos.ne']
      ring
    rw [Real.exp_add, Real.exp_neg, Real.exp_log (mul_pos hm_pos hJ_pos), ← one_div,
      ← hlog_base, ← Real.log_pow, Real.exp_log (pow_pos hbase_pos m), mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  refine le_trans (Real.exp_le_exp.mpr ?_) hRHS_ge
  -- Step 3: bound each term in the exponent
  have hlogmJ_le : Real.log ((m : ℝ) * (J n : ℝ)) ≤ (ε / 4) * (u n * Real.log (u n)) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) * (J n : ℝ) := by
      have : 1 ≤ m * J n := Nat.mul_pos hm1 hJ1
      exact_mod_cast this
    have h2 : (m : ℝ) * (J n : ℝ) ≤ (m : ℝ) ^ 2 * (J n : ℝ) := by
      have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hm1r (by norm_num)) hJ_pos.le
    have hge1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 * (J n : ℝ) := h1.trans h2
    have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) ^ 2 * (J n : ℝ)) := Real.log_nonneg hge1
    have hprod_nonneg : 0 ≤ u n * Real.log (u n) := mul_nonneg hu_pos.le hlu_pos.le
    change ‖Real.log ((m : ℝ) ^ 2 * (J n : ℝ))‖ ≤ (ε / 4) * ‖u n * Real.log (u n)‖ at hlogJ
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hprod_nonneg] at hlogJ
    exact (Real.log_le_log (mul_pos hm_pos hJ_pos) h2).trans hlogJ
  have hll_le : Real.log (Real.log (u n)) ≤ (ε / 8) * Real.log (u n) := by
    have hll_nonneg : 0 ≤ Real.log (Real.log (u n)) := Real.log_nonneg (by linarith only [hlu2])
    change ‖Real.log (Real.log (u n))‖ ≤ (ε / 8) * ‖Real.log (u n)‖ at hll
    rw [Real.norm_of_nonneg hll_nonneg, Real.norm_of_nonneg hlu_pos.le] at hll
    exact hll
  have hterm1 : (m : ℝ) * Real.log (m : ℝ) ≤
      u n * Real.log (u n) + 2 * (2 + Real.log 3) * u n := by
    have hprod1 : (m : ℝ) * Real.log (u n) ≤ u n * Real.log (u n) + 2 * u n := by
      have h := mul_le_mul_of_nonneg_right hm_le_tight hlu_pos.le
      have heq : u n * (1 + 2 / Real.log (u n)) * Real.log (u n) =
          u n * Real.log (u n) + 2 * u n := by field_simp
      linarith only [h, heq]
    have hprod2 : (m : ℝ) * Real.log 3 ≤ 2 * Real.log 3 * u n := by
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith only [hm_le_2u, this]
    have hprod3 : (m : ℝ) * Real.log (m : ℝ) ≤ (m : ℝ) * (Real.log (u n) + Real.log 3) :=
      mul_le_mul_of_nonneg_left hlog_m hm_pos.le
    linarith only [hprod1, hprod2, hprod3, hu_pos]
  have hterm2 : (m : ℝ) * Real.log (Real.log (u n)) ≤ (ε / 4) * (u n * Real.log (u n)) := by
    have h1 := mul_le_mul_of_nonneg_left hll_le hm_pos.le
    have h2 : (m : ℝ) * ((ε / 8) * Real.log (u n)) ≤ (2 * u n) * ((ε / 8) * Real.log (u n)) :=
      mul_le_mul_of_nonneg_right hm_le_2u (by positivity)
    linarith only [h1, h2]
  have hterm3 : (m : ℝ) * (-Real.log C) ≤ 2 * |Real.log C| * u n := by
    have h1 : -Real.log C ≤ |Real.log C| := neg_le_abs _
    have h2 := mul_le_mul_of_nonneg_left h1 hm_pos.le
    have h3 := mul_le_mul_of_nonneg_right hm_le_2u (abs_nonneg (Real.log C))
    linarith only [h2, h3]
  have hK_budget : 2 * K * u n ≤ (ε / 4) * (u n * Real.log (u n)) := by
    have h1 := (div_le_iff₀ hε).mp hluK
    have h2 : 2 * K ≤ (ε / 4) * Real.log (u n) := by linarith only [h1]
    nlinarith only [h2, hu_pos]
  have hsum_linear : 2 * (2 + Real.log 3) * u n + 2 * |Real.log C| * u n = 2 * K * u n := by
    dsimp [K]; ring
  have hεX : 0 ≤ ε * (u n * Real.log (u n)) :=
    mul_nonneg hε.le (mul_nonneg hu_pos.le hlu_pos.le)
  linarith only [hlogmJ_le, hterm1, hterm2, hterm3, hK_budget, hsum_linear, hεX]

/-- End-to-end asymptotic leading density theorem for `centeredBinProducts`
under `DirichletLZerosOnLine`. -/
theorem eventually_centeredBinProducts_density_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u P y δ : ℕ → ℝ} {J : ℕ → ℕ} {c cH ε : ℝ},
      Tendsto u atTop atTop →
      0 < c → 0 < cH → 0 < ε →
      (∀ᶠ n in atTop, 0 < P n) →
      (∀ᶠ n in atTop, 0 ≤ δ n) →
      (∀ᶠ n in atTop, 1 < y n) →
      (∀ᶠ n in atTop, cH * Real.log (y n) / Real.log (u n) ≤ (J n : ℝ) * δ n) →
      (∀ᶠ n in atTop, ⌈u n * (1 + 1 / Real.log (u n))⌉₊ ≤ J n) →
      Asymptotics.IsLittleO atTop
        (fun n => Real.log ((⌈u n * (1 + 1 / Real.log (u n))⌉₊ : ℝ) ^ 2 * (J n : ℝ)))
        (fun n => u n * Real.log (u n)) →
      (∀ᶠ n in atTop, (2 : ℝ) ≤ P n * Real.exp (-(δ n * (J n : ℝ)))) →
      (∀ᶠ n in atTop, P n * Real.exp (δ n * (J n : ℝ)) ≤ y n) →
      (∀ᶠ n in atTop,
        K * (1 + Real.log (3 * y n)) ^ 2 * Real.sqrt (y n) + 1 ≤
          (1 - c) * δ n * (P n * Real.exp (-(δ n * (J n : ℝ))))) →
      ∀ᶠ n in atTop,
        let m := ⌈u n * (1 + 1 / Real.log (u n))⌉₊
        ∃ a ∈ range (m * (J n - 1) + 1),
          Real.exp (-(1 + ε) * u n * Real.log (u n)) ≤
            ((centeredBinProducts (P n) (δ n) (J n) m a).card : ℝ) / (P n) ^ m ∧
          (∀ x ∈ centeredBinProducts (P n) (δ n) (J n) m a,
            (P n) ^ m ≤ (x : ℝ) ∧ (x : ℝ) ≤ (P n) ^ m * Real.exp ((m : ℝ) * δ n) ∧
            ∀ p ∈ x.primeFactors, (p : ℝ) ≤ y n) := by
  obtain ⟨K, hK, hconcrete⟩ := centeredBinProducts_density_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro u P y δ J c cH ε hu hc hcH hε hP hδ hy hJδ hJm hlog hlo hhi hguard
  have hasymp := eventually_primeBinStrip_density_lower hu hc hcH hε hy hδ hJδ hJm hlog
  filter_upwards [hu.eventually_ge_atTop 2, hP, hδ, hy, hJm, hlo, hhi, hguard, hasymp] with
    n hu2 hPn hδn hyn hJmn hlon hhin hguardn hasympn
  dsimp only
  set m := ⌈u n * (1 + 1 / Real.log (u n))⌉₊
  have hm1 : 1 ≤ m := by
    have hlu : 0 < Real.log (u n) := Real.log_pos (by linarith only [hu2])
    have h1 : (1 : ℝ) ≤ u n * (1 + 1 / Real.log (u n)) := by
      have : 0 ≤ u n / Real.log (u n) := by positivity
      linarith only [hu2, show u n * (1 + 1 / Real.log (u n)) = u n + u n / Real.log (u n) by ring, this]
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hJ1 : 1 ≤ J n := hm1.trans hJmn
  obtain ⟨a, ha, hdens, hmem⟩ :=
    hconcrete (P n) (δ n) c (y n) (J n) m hPn hδn hc.le hyn hJ1 hm1 hlon hhin hguardn
  exact ⟨a, ha, hasympn.trans hdens, hmem⟩

/-! ## Section 3: `L_N[1/3, c]` Parameter Scaling -/

/-- Exact asymptotic ratio for `L_N[2/3, a]` divided by `L_N[1/3, b]`:
if `u n = (a / b) * (log n / log (log n))^(1/3)`, then
`u n * log (u n) / scale n → a / (3 * b)`. -/
theorem oneThird_u_mul_log_u_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let u : ℕ → ℝ := fun n => (a / b) * (Real.log n / Real.log (Real.log n)) ^ (1 / 3 : ℝ)
    Tendsto u atTop atTop ∧
    Tendsto (fun n => u n * Real.log (u n) / RandomizedOneThirdAsymptotic.scale n)
      atTop (nhds (a / (3 * b))) := by
  dsimp only
  let u : ℕ → ℝ := fun n => (a / b) * (Real.log n / Real.log (Real.log n)) ^ (1 / 3 : ℝ)
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hratio_zero : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one] using h1
  have hL_div_LL : Tendsto (fun n : ℕ => Real.log n / Real.log (Real.log n)) atTop atTop := by
    have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
      filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℝ)] with
        x hlx hx
      exact div_pos hlx hx
    have hinv : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop :=
      Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratio_zero hpos)
    have hcomp := hinv.comp hL
    refine hcomp.congr fun n => ?_
    simp [Function.comp_def, inv_div]
  have hu_grows : Tendsto u atTop atTop :=
    Tendsto.const_mul_atTop (div_pos ha hb)
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hL_div_LL)
  have hlogLL_div : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n)) / Real.log (Real.log n))
      atTop (nhds 0) :=
    hratio_zero.comp hLL
  have hconst_div : Tendsto (fun n : ℕ => Real.log (a / b) / Real.log (Real.log n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLL
  have hlim : Tendsto
      (fun n : ℕ =>
        (a / b) * (1 / 3 - (1 / 3) * (Real.log (Real.log (Real.log n)) / Real.log (Real.log n)) +
          Real.log (a / b) / Real.log (Real.log n)))
      atTop (nhds (a / (3 * b))) := by
    have htarget : (a / b) * (1 / 3 - (1 / 3) * (0 : ℝ) + 0) = a / (3 * b) := by ring
    rw [← htarget]
    exact tendsto_const_nhds.mul
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hlogLL_div)).add hconst_div)
  refine ⟨hu_grows, ?_⟩
  refine hlim.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 1, hLL.eventually_gt_atTop 1] with n hLn hLLn
  have hLpos : 0 < Real.log n := by linarith only [hLn]
  have hLLpos : 0 < Real.log (Real.log n) := by linarith only [hLLn]
  have hpow_eq : (Real.log n / Real.log (Real.log n)) ^ (1 / 3 : ℝ) /
      RandomizedOneThirdAsymptotic.scale n = 1 / Real.log (Real.log n) := by
    unfold RandomizedOneThirdAsymptotic.scale
    rw [Real.div_rpow hLpos.le hLLpos.le]
    have h1 : (Real.log (Real.log n)) ^ (1 / 3 : ℝ) * (Real.log (Real.log n)) ^ (2 / 3 : ℝ) =
        Real.log (Real.log n) := by
      rw [← Real.rpow_add hLLpos]
      norm_num
    have hL13 : (Real.log n) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hLpos _).ne'
    have hLL13 : (Real.log (Real.log n)) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hLLpos _).ne'
    have hLL23 : (Real.log (Real.log n)) ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hLLpos _).ne'
    calc
      (Real.log n) ^ (1 / 3 : ℝ) / (Real.log (Real.log n)) ^ (1 / 3 : ℝ) /
          ((Real.log n) ^ (1 / 3 : ℝ) * (Real.log (Real.log n)) ^ (2 / 3 : ℝ))
          = 1 / ((Real.log (Real.log n)) ^ (1 / 3 : ℝ) * (Real.log (Real.log n)) ^ (2 / 3 : ℝ)) := by
              field_simp
      _ = 1 / Real.log (Real.log n) := by rw [h1]
  have hlog_u : Real.log (u n) =
      Real.log (a / b) + (1 / 3 : ℝ) * Real.log (Real.log n) -
        (1 / 3 : ℝ) * Real.log (Real.log (Real.log n)) := by
    dsimp only [u]
    rw [Real.log_mul (div_pos ha hb).ne' (Real.rpow_pos_of_pos (div_pos hLpos hLLpos) _).ne',
      Real.log_rpow (div_pos hLpos hLLpos), Real.log_div hLpos.ne' hLLpos.ne']
    ring
  have hdiv : u n / RandomizedOneThirdAsymptotic.scale n = (a / b) / Real.log (Real.log n) := by
    dsimp only [u]
    rw [mul_div_assoc, hpow_eq]
    ring
  rw [mul_div_right_comm, hdiv, hlog_u]
  field_simp
  ring

/-- Converting `exp (-(1 + δ) * u * log u)` into the `L_N[1/3, c]` scale
`exp (-((1 + δ) * a / (3 * b) + ε) * scale n)`. -/
theorem eventually_oneThird_density_scale {a b δ ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hε : 0 < ε) :
    let u : ℕ → ℝ := fun n => (a / b) * (Real.log n / Real.log (Real.log n)) ^ (1 / 3 : ℝ)
    ∀ᶠ n in atTop,
      Real.exp (-((1 + δ) * (a / (3 * b)) + ε) * RandomizedOneThirdAsymptotic.scale n) ≤
        Real.exp (-(1 + δ) * u n * Real.log (u n)) := by
  dsimp only
  let u : ℕ → ℝ := fun n => (a / b) * (Real.log n / Real.log (Real.log n)) ^ (1 / 3 : ℝ)
  have hlim := (oneThird_u_mul_log_u_tendsto ha hb).2
  have hslack : 0 < ε / (1 + δ) := div_pos hε (by linarith)
  have hev := (tendsto_order.mp hlim).2 (a / (3 * b) + ε / (1 + δ)) (by linarith)
  filter_upwards [hev, RandomizedOneThirdAsymptotic.scale_grows.eventually_gt_atTop 0] with
    n hlt hsc
  apply Real.exp_le_exp.mpr
  have h1 := (div_lt_iff₀ hsc).mp hlt
  have h2 := mul_le_mul_of_nonneg_left h1.le (show 0 ≤ 1 + δ by linarith)
  have h3 : (1 + δ) * (a / (3 * b) + ε / (1 + δ)) = (1 + δ) * (a / (3 * b)) + ε := by
    field_simp
  rw [← mul_assoc (1 + δ) (a / (3 * b) + ε / (1 + δ)), h3] at h2
  linarith only [h2]

/-! ## Section 4: Rankin Smooth-Number Upper Bounds -/

private theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ k ∈ range N, r ^ k) ≤ (1 - r)⁻¹ := by
  have h1mr : 0 < 1 - r := sub_pos.mpr hr1
  have hmul : (1 - r) * (∑ k ∈ range N, r ^ k) = 1 - r ^ N := by
    have hdiff : ∀ k : ℕ, (1 - r) * r ^ k = r ^ k - r ^ (k + 1) := fun k => by
      rw [pow_succ]; ring
    rw [Finset.mul_sum]
    simp_rw [hdiff]
    rw [Finset.sum_range_sub' (fun k => r ^ k) N, pow_zero]
  have hle : (1 - r) * (∑ k ∈ range N, r ^ k) ≤ 1 := by
    rw [hmul]
    linarith only [pow_nonneg hr0 N]
  rw [← one_div, le_div_iff₀' h1mr]
  exact hle

/-- Master finite Euler product bound: for any finite set `S` of positive `y`-smooth
integers and any `α > 0`,
`∑ n ∈ S, n^(-α) ≤ ∏_{p ≤ y, p prime} (1 - p^(-α))⁻¹`. -/
theorem sum_rpow_neg_le_euler_prod {S : Finset ℕ} {y α : ℝ}
    (hy : 0 ≤ y) (hα : 0 < α)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y) :
    (∑ n ∈ S, (n : ℝ) ^ (-α)) ≤
      ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime
  let E : ℕ := S.sup id
  let Box : Finset (P → ℕ) := Fintype.piFinset fun _ : P => range (E + 1)
  let φ : (P → ℕ) → ℕ := fun e => ∏ p : P, (p : ℕ) ^ (e p)
  let ψ : ℕ → (P → ℕ) := fun n p => n.factorization (p : ℕ)
  have hφψ : ∀ n ∈ S, φ (ψ n) = n := by
    intro n hn
    have hnpos : 0 < n := (hS n hn).1
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hple : p ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).mpr ((hS n hn).2 p hp)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpPrime.two_le, hple⟩, hpPrime⟩
    calc
      φ (ψ n) = ∏ p ∈ P, p ^ (n.factorization p) := by
            dsimp only [φ, ψ]
            exact Finset.prod_coe_sort P (fun p => p ^ n.factorization p)
      _ = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
            symm
            refine Finset.prod_subset hsub fun p _ hpnot => ?_
            rw [(Finsupp.notMem_support_iff (f := n.factorization)).mp hpnot, pow_zero]
      _ = n := by
            simpa only [Finsupp.prod, Nat.support_factorization] using
              Nat.prod_factorization_pow_eq_self hnpos.ne'
  have hψmem : ∀ n ∈ S, ψ n ∈ Box := by
    intro n hn
    have hnpos : 0 < n := (hS n hn).1
    rw [Fintype.mem_piFinset]
    intro p
    have hpPrime : (p : ℕ).Prime := (mem_filter.mp p.2).2
    have hlt : n.factorization (p : ℕ) < n := by
      calc
        n.factorization (p : ℕ) < 2 ^ (n.factorization (p : ℕ)) := Nat.lt_two_pow_self
        _ ≤ (p : ℕ) ^ (n.factorization (p : ℕ)) := Nat.pow_le_pow_left hpPrime.two_le _
        _ ≤ n := Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p)
    have hleE : n ≤ E := Finset.le_sup (f := id) hn
    exact mem_range.mpr (show n.factorization (p : ℕ) < E + 1 by omega)
  have hψinj : Set.InjOn ψ S := by
    intro a ha b hb hab
    rw [← hφψ a ha, ← hφψ b hb, hab]
  have hstep1 : (∑ n ∈ S, (n : ℝ) ^ (-α)) ≤ ∑ e ∈ Box, ((φ e : ℕ) : ℝ) ^ (-α) := by
    calc
      (∑ n ∈ S, (n : ℝ) ^ (-α))
          = ∑ n ∈ S, ((φ (ψ n) : ℕ) : ℝ) ^ (-α) :=
              Finset.sum_congr rfl fun n hn => by rw [hφψ n hn]
      _ = ∑ e ∈ S.image ψ, ((φ e : ℕ) : ℝ) ^ (-α) :=
              (Finset.sum_image (f := fun e => ((φ e : ℕ) : ℝ) ^ (-α)) hψinj).symm
      _ ≤ ∑ e ∈ Box, ((φ e : ℕ) : ℝ) ^ (-α) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.image_subset_iff.mpr hψmem)
                (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hterm : ∀ e : P → ℕ,
      ((φ e : ℕ) : ℝ) ^ (-α) = ∏ p : P, ((p : ℝ) ^ (-α)) ^ (e p) := by
    intro e
    dsimp only [φ]
    rw [Nat.cast_prod, ← Real.finsetProd_rpow Finset.univ
      (fun i : P => (((i : ℕ) ^ e i : ℕ) : ℝ)) (fun _ _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      mul_comm, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
  have hstep2 : (∑ e ∈ Box, ((φ e : ℕ) : ℝ) ^ (-α)) =
      ∏ p : P, ∑ k ∈ range (E + 1), ((p : ℝ) ^ (-α)) ^ k := by
    simp_rw [hterm]
    exact (Finset.prod_univ_sum (fun _ : P => range (E + 1))
      (fun p k => ((p : ℝ) ^ (-α)) ^ k)).symm
  have hstep3 : (∏ p : P, ∑ k ∈ range (E + 1), ((p : ℝ) ^ (-α)) ^ k) ≤
      ∏ p : P, (1 - (p : ℝ) ^ (-α))⁻¹ := by
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun k _ => by positivity) fun p _ => ?_
    have hp2 : (1 : ℝ) < (p : ℕ) := by
      have hpPrime : (p : ℕ).Prime := (mem_filter.mp p.2).2
      exact_mod_cast hpPrime.one_lt
    have hr1 : ((p : ℕ) : ℝ) ^ (-α) < 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hp2 (neg_lt_zero.mpr hα)
    exact geom_sum_le_inv_one_sub (Real.rpow_nonneg (Nat.cast_nonneg _) _) hr1 (E + 1)
  calc
    (∑ n ∈ S, (n : ℝ) ^ (-α)) ≤ ∑ e ∈ Box, ((φ e : ℕ) : ℝ) ^ (-α) := hstep1
    _ = ∏ p : P, ∑ k ∈ range (E + 1), ((p : ℝ) ^ (-α)) ^ k := hstep2
    _ ≤ ∏ p : P, (1 - (p : ℝ) ^ (-α))⁻¹ := hstep3
    _ = ∏ p ∈ P, (1 - (p : ℝ) ^ (-α))⁻¹ :=
        Finset.prod_coe_sort P (fun p : ℕ => (1 - (p : ℝ) ^ (-α))⁻¹)

/-- Elementary Rankin upper bound for `y`-smooth integers `≤ ⌊x⌋₊`:
for any `1 ≤ x`, `2 ≤ y`, and `α ∈ (0, 1)` (in fact any `0 < α`),
`Ψ(x, y) ≤ x^α * ∏_{p ≤ y, p prime} (1 - p^(-α))⁻¹`. -/
theorem smoothCount_rankin_upper {x y α : ℝ} (hx : 1 ≤ x) (hy : 2 ≤ y)
    (hα0 : 0 < α) (_hα1 : α < 1) :
    (((Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y)).card : ℝ) ≤
      x ^ α * ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  let S := (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y)
  have hxpos : 0 < x := by linarith only [hx]
  have hS : ∀ n ∈ S, 1 ≤ n ∧ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y := by
    intro n hn
    obtain ⟨hIcc, hsm⟩ := mem_filter.mp hn
    exact ⟨(mem_Icc.mp hIcc).1, hsm⟩
  have hsum : (S.card : ℝ) ≤ x ^ α * ∑ n ∈ S, (n : ℝ) ^ (-α) := by
    rw [Finset.mul_sum]
    calc
      (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, x ^ α * (n : ℝ) ^ (-α) := by
            refine Finset.sum_le_sum fun n hn => ?_
            obtain ⟨hIcc, _⟩ := mem_filter.mp hn
            obtain ⟨hn1, hnx⟩ := mem_Icc.mp hIcc
            have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
            have hnlex : (n : ℝ) ≤ x := (Nat.cast_le.mpr hnx).trans (Nat.floor_le hxpos.le)
            have hpow : (n : ℝ) ^ α ≤ x ^ α := Real.rpow_le_rpow hnpos.le hnlex hα0.le
            have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hnpos.le (-α))
            rwa [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero] at hmul
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (sum_rpow_neg_le_euler_prod (by linarith only [hy]) hα0 hS) (Real.rpow_nonneg hxpos.le α))

/-- Companion weighted smooth reciprocal bound (real threshold `T > 0`, upper bound `U`):
for any `0 < T`, `2 ≤ y`, and `α ∈ (0, 1)`,
`∑_{T ≤ d ≤ U, P^+(d) ≤ y} (1 / d) ≤ T^(α - 1) * ∏_{p ≤ y, p prime} (1 - p^(-α))⁻¹`. -/
theorem smoothReciprocal_rankin_upper {T U y α : ℝ} (hT : 0 < T) (hy : 2 ≤ y)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∑ d ∈ (Finset.Icc 1 ⌊U⌋₊).filter
        (fun d : ℕ => T ≤ (d : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y), (1 / (d : ℝ))) ≤
      T ^ (α - 1) * ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  let S := (Finset.Icc 1 ⌊U⌋₊).filter (fun d : ℕ => T ≤ (d : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y)
  have hS : ∀ d ∈ S, 1 ≤ d ∧ ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y := by
    intro d hd
    obtain ⟨hIcc, _, hsm⟩ := mem_filter.mp hd
    exact ⟨(mem_Icc.mp hIcc).1, hsm⟩
  have hsum : (∑ d ∈ S, (1 / (d : ℝ))) ≤ T ^ (α - 1) * ∑ d ∈ S, (d : ℝ) ^ (-α) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    obtain ⟨hIcc, hTd, _⟩ := mem_filter.mp hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := (mem_Icc.mp hIcc).1; omega)
    have hpow : (d : ℝ) ^ (α - 1) ≤ T ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hT hTd (by linarith only [hα1])
    have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hdpos.le (-α))
    have heq : (d : ℝ) ^ (α - 1) * (d : ℝ) ^ (-α) = 1 / (d : ℝ) := by
      rw [← Real.rpow_add hdpos, show α - 1 + -α = (-1 : ℝ) by ring, Real.rpow_neg_one, one_div]
    linarith only [hmul, heq]
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (sum_rpow_neg_le_euler_prod (by linarith only [hy]) hα0 hS) (Real.rpow_nonneg hT.le _))

/-- Companion weighted smooth reciprocal bound with natural-number endpoints `1 ≤ T`, `U`. -/
theorem smoothReciprocal_Icc_rankin_upper {T U : ℕ} {y α : ℝ} (hT : 1 ≤ T) (hy : 2 ≤ y)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∑ d ∈ (Finset.Icc T U).filter (fun d : ℕ => ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y), (1 / (d : ℝ))) ≤
      (T : ℝ) ^ (α - 1) * ∏ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hset : (Finset.Icc T U).filter (fun d : ℕ => ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y) =
      (Finset.Icc 1 ⌊(U : ℝ)⌋₊).filter
        (fun d : ℕ => (T : ℝ) ≤ (d : ℝ) ∧ ∀ p ∈ d.primeFactors, (p : ℝ) ≤ y) := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.floor_natCast, Nat.cast_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, h1, h3⟩
    · rintro ⟨⟨_, h2⟩, h3, h4⟩
      exact ⟨⟨h3, h2⟩, h4⟩
  rw [hset]
  exact smoothReciprocal_rankin_upper hTpos hy hα0 hα1

#print axioms factorial_ge_pow_mul_exp
#print axioms factorial_le_mul_pow_mul_exp
#print axioms choose_ge_sub_pow_div_factorial
#print axioms choose_ge_stirling
#print axioms choose_ge_div_pow
#print axioms exists_large_centeredBinPatterns
#print axioms primeBinPatternProducts_uniform_lower
#print axioms primeBinPatternProducts_density_lower
#print axioms centeredBinProducts_density_of_supply
#print axioms centeredBinProducts_density_from_critical_line
#print axioms eventually_primeBinStrip_density_lower
#print axioms eventually_centeredBinProducts_density_from_critical_line
#print axioms oneThird_u_mul_log_u_tendsto
#print axioms eventually_oneThird_density_scale
#print axioms sum_rpow_neg_le_euler_prod
#print axioms smoothCount_rankin_upper
#print axioms smoothReciprocal_rankin_upper
#print axioms smoothReciprocal_Icc_rankin_upper

end Cogentic.Randomized
