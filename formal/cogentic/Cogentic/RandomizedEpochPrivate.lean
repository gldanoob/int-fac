import Cogentic.RandomizedReducedFormSupply
import Cogentic.RandomizedFormGroup
import Cogentic.RandomizedBalancedAllocation
import Cogentic.RandomizedPrivateFloor
import Cogentic.RandomizedPrivateGates
import Cogentic.RandomizedOneThirdAsymptotic
import Mathlib.Probability.Distributions.Uniform

/-!
# Private supply assembly for one epoch slot

This file isolates the private-supply estimate of the randomized epoch
(blueprint L23--L26).  The only non-combinatorial input is the
form-composition / class-group bridge L25: every squarefree principal-genus
product of distinct split primes is realised as the leading coefficient of a
reduced form.  It is an explicit field of `PrivateSupplyInputs`.

The combinatorial part is proved unconditionally from
`principal_genus_distinct_tuple_fraction_lower`; the analytic band and genus
estimates are left as named hypotheses in the final assembly theorem.
-/

namespace Cogentic.RandomizedEpochPrivate

open Filter
open scoped BigOperators Topology

noncomputable section

open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedReducedFormSupply
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## Section 1: The L24 class-number sandwich and the private-supply inputs -/

/-- The principal reduced form `[1, 0, 2N]` is always present, so the uniform
slot law is well defined. -/
theorem reducedForms_nonempty {N : ℕ} (hN : 0 < N) : (ReducedForms N).Nonempty := by
  refine ⟨(1, 0, 2 * N), mem_reducedForms.mpr ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; ring
  · norm_num
  · norm_num
  · norm_num
  · exact_mod_cast (show 1 ≤ 2 * N by omega)
  · intro _; norm_num
  · simp

/-- The two class-number bounds of L24, packaged together. -/
structure PrivateSupplyClassBounds (N : ℕ) : Prop where
  upper : ((ReducedForms N).card : ℝ) ≤
    (2 * Real.exp 18) * Real.sqrt (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) ^ 7
  lower : (1 / 8 : ℝ) * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ≤
    ((ReducedForms N).card : ℝ)

/-- Construct the L24 sandwich from `DirichletLZerosOnLine` and the polylog
upper bound.  This is the only place where the two class-number estimates enter
the private-supply reduction. -/
theorem classBounds_of_criticalLine (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N → PrivateSupplyClassBounds N := by
  obtain ⟨N₀, hlow⟩ := reducedForms_card_lower_from_critical_line line
  refine ⟨N₀, fun N hN hodd => ⟨?_, hlow N hN hodd⟩⟩
  simpa using reducedForms_card_le_sqrt_mul_log_pow (N := N) hodd

/-- L23 in the exact band form consumed by `PrivateSupplyInputs`: under
`DirichletLZerosOnLine`, after deleting an exceptional subset of relative size
`ε < 1`, every nontrivial genus character has normalized bias at most
`(C_bias * base^(-1/2) * (1 + log(N*base))^3 + ε) / (1 - ε)`. -/
theorem splitBand_bias_after_deletion_from_criticalLine (line : DirichletLZerosOnLine) :
    ∃ C_thresh C_bias : ℝ, 0 ≤ C_thresh ∧ 0 ≤ C_bias ∧
      ∀ (N base : ℕ), Odd N → 3 ≤ N → 2 ≤ base →
        C_thresh * (1 + Real.log ((N : ℝ) * base)) ^ 3 ≤ Real.sqrt base →
        ∀ (E : Finset ℕ) (ε : ℝ),
          E ⊆ splitPrimeBin N base (2 * base) →
          (E.card : ℝ) ≤ ε * ((splitPrimeBin N base (2 * base)).card : ℝ) →
          0 ≤ ε → ε < 1 →
            (splitPrimeBin N base (2 * base) \ E).Nonempty ∧
            ∀ S ⊆ N.primeFactors, S.Nonempty →
              |(∑ p ∈ splitPrimeBin N base (2 * base) \ E,
                  genusCharReal N S (p : ZMod (8 * N))) /
                  ((splitPrimeBin N base (2 * base) \ E).card : ℝ)| ≤
                (C_bias * (base : ℝ) ^ (-(1 / 2 : ℝ)) *
                    (1 + Real.log ((N : ℝ) * base)) ^ 3 + ε) / (1 - ε) :=
  splitPrimeBin_genus_bias_after_deletion_from_critical_line line

/-- L23 band-count lower bound: the split-prime dyadic band contains at least
`base / (2 log(2 base)) - O(sqrt base * (1 + log(N base))^2)` primes. -/
theorem splitBand_card_lower_from_criticalLine (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N base : ℕ), Odd N → 3 ≤ N → 2 ≤ base →
      (base : ℝ) / (2 * Real.log (2 * (base : ℝ))) -
          C * Real.sqrt base * (1 + Real.log ((N : ℝ) * base)) ^ 2 ≤
        ((splitPrimeBin N base (2 * base)).card : ℝ) :=
  splitPrimeBin_card_lower_from_critical_line line

/-- On a tuple of distinct primes from pairwise disjoint bands, the product map
is injective: unique factorization recovers the prime set, and the bands recover
the index of each prime. -/
theorem prod_tuple_injective {m : ℕ} {P : Fin m → Finset ℕ}
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    Function.Injective
      (fun t : (∀ i : Fin m, {p : ℕ // p ∈ P i}) => ∏ i, (t i).1) := by
  intro t s hts
  funext i
  apply Subtype.ext
  have hdvd0 : (t i).1 ∣ ∏ j, (t j).1 :=
    Finset.dvd_prod_of_mem (fun j => (t j).1) (Finset.mem_univ i)
  have hts' : (∏ j, (t j).1) = (∏ j, (s j).1) := hts
  have hdvd : (t i).1 ∣ ∏ j, (s j).1 := by
    simpa [hts'] using hdvd0
  have htprime : (t i).1.Prime := hprime i (t i).1 (t i).2
  obtain ⟨j, -, hdvdj⟩ :=
    (Prime.dvd_finsetProd_iff htprime.prime (fun j => (s j).1)).mp hdvd
  have hsprime : (s j).1.Prime := hprime j (s j).1 (s j).2
  have heq : (t i).1 = (s j).1 := (Nat.prime_dvd_prime_iff_eq htprime hsprime).mp hdvdj
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj i j hne) (heq ▸ (t i).2) (s j).2
  subst j
  exact heq

/-- The uniform slot law: a uniformly random reduced form of discriminant `-8N`. -/
noncomputable def privateSlotPMF (N : ℕ) (hN : 0 < N) : PMF (ℕ × ℤ × ℕ) :=
  PMF.uniformOfFinset (ReducedForms N) (reducedForms_nonempty hN)

/-- The private-supply inputs of one epoch slot.

The data are the band sets `P i`, their genus-character biases, the collision
scale `M_min`, and the class-number sandwich.  The field `realized` is the
missing form-composition / class-group bridge L25: every squarefree
principal-genus product of distinct primes, one from each band, is the leading
coefficient of a reduced form of discriminant `-8N`.  No other property of the
class group is assumed. -/
structure PrivateSupplyInputs (N : ℕ) where
  hNpos : 0 < N
  hN3 : 3 ≤ N
  m : ℕ
  hm : 0 < m
  P : Fin m → Finset ℕ
  hPprime : ∀ i, ∀ p ∈ P i, p.Prime
  hPcop : ∀ i, ∀ p ∈ P i, Nat.Coprime p (8 * N)
  hPne : ∀ i, (P i).Nonempty
  hPdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  M_min : ℕ
  hM_min : 0 < M_min
  hPsize : ∀ i, M_min ≤ (P i).card
  δ : ℝ
  hδ : 0 ≤ δ
  hbias : ∀ i (S : Finset ℕ), S ⊆ N.primeFactors → S.Nonempty →
    |(∑ p ∈ P i, genusCharReal N S (p : ZMod (8 * N))) / ((P i).card : ℝ)| ≤ δ
  realized : ∀ (t : ∀ i : Fin m, {p : ℕ // p ∈ P i}),
    (∏ i, genusMap N (t i).1) = 1 →
    Function.Injective (fun i => (t i).1) →
      ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1
  classBounds : PrivateSupplyClassBounds N

namespace PrivateSupplyInputs

variable {N : ℕ} (I : PrivateSupplyInputs N)

/-- The normalized principal-genus, distinct-prime tuple fraction of L23/L26. -/
noncomputable def principalGenusFraction : ℝ :=
  let g : ℝ := ((2 ^ N.primeFactors.card : ℕ) : ℝ)
  g⁻¹ * (1 - (g - 1) * I.δ ^ I.m) - (I.m : ℝ) ^ 2 / (I.M_min : ℝ)

/-- L26 positivity criterion: if the genus-bias loss consumes at most half of
the numerator `1 - (g-1) δ^m` and the repeated-prime collision loss is at most
`1/(4g)`, then the principal-genus fraction is at least `1/(4g)`. -/
theorem principalGenusFraction_ge_inv_four_g
    (hdelta : (((2 ^ N.primeFactors.card : ℕ) : ℝ) - 1) * I.δ ^ I.m ≤ 1 / 2)
    (hcoll : (I.m : ℝ) ^ 2 / (I.M_min : ℝ) ≤
      1 / (4 * ((2 ^ N.primeFactors.card : ℕ) : ℝ))) :
    1 / (4 * ((2 ^ N.primeFactors.card : ℕ) : ℝ)) ≤ I.principalGenusFraction := by
  let g : ℝ := ((2 ^ N.primeFactors.card : ℕ) : ℝ)
  have hgpos : 0 < g := by dsimp [g]; positivity
  have hdelta' : (g - 1) * I.δ ^ I.m ≤ 1 / 2 := by simpa [g] using hdelta
  have hcoll' : (I.m : ℝ) ^ 2 / (I.M_min : ℝ) ≤ 1 / (4 * g) := by
    simpa [g] using hcoll
  have hfirst : 1 / (2 * g) ≤ g⁻¹ * (1 - (g - 1) * I.δ ^ I.m) := by
    have h1 : (1 : ℝ) / 2 ≤ 1 - (g - 1) * I.δ ^ I.m := by linarith
    calc
      1 / (2 * g) = g⁻¹ * (1 / 2) := by
        field_simp [hgpos.ne']
      _ ≤ g⁻¹ * (1 - (g - 1) * I.δ ^ I.m) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hgpos.le)
  have hhalf : 1 / (2 * ((2 ^ N.primeFactors.card : ℕ) : ℝ)) =
      2 * (1 / (4 * ((2 ^ N.primeFactors.card : ℕ) : ℝ))) := by
    field_simp
    ring
  dsimp [principalGenusFraction, g] at hfirst hcoll' ⊢
  linarith [hfirst, hcoll', hhalf]

/-- Ordered tuples in the principal genus with pairwise distinct prime values. -/
noncomputable def goodTuples : Finset (∀ i : Fin I.m, {p : ℕ // p ∈ I.P i}) := by
  classical
  exact Finset.univ.filter (fun t =>
    (∏ i, genusMap N (t i).1) = 1 ∧ Function.Injective (fun i => (t i).1))

/-- The leading coefficients obtained from good tuples. -/
noncomputable def goodLeading : Finset ℕ :=
  I.goodTuples.image (fun t => ∏ i, (t i).1)

/-- Reduced forms whose leading coefficient is a good leading coefficient. -/
noncomputable def goodForms : Finset (ℕ × ℤ × ℕ) := by
  classical
  exact (ReducedForms N).filter (fun f => f.1 ∈ I.goodLeading)

/-- A chosen reduced-form witness for a good tuple, and an arbitrary fallback
outside the good set.  The fallback is never used in the injection proof. -/
noncomputable def witnessForm (t : ∀ i : Fin I.m, {p : ℕ // p ∈ I.P i}) :
    ℕ × ℤ × ℕ :=
  if h : (∏ i, genusMap N (t i).1) = 1 ∧ Function.Injective (fun i => (t i).1) then
    Classical.choose (I.realized t h.1 h.2)
  else
    (1, 0, 2 * N)

/-! ## Section 2: The combinatorial private-supply lower bound -/

/-- The L23/L26 principal-genus distinct-tuple fraction, multiplied by the
number of band tuples, is a lower bound for the number of good tuples. -/
theorem goodTuples_card_lower :
    I.principalGenusFraction * (∏ i : Fin I.m, ((I.P i).card : ℝ)) ≤
      (I.goodTuples.card : ℝ) := by
  classical
  have h := principal_genus_distinct_tuple_fraction_lower (N := N) (m := I.m)
    (M_min := I.M_min) I.P I.hM_min I.hPsize I.hPcop I.hδ I.hbias
  dsimp only [principalGenusFraction, goodTuples] at h
  have hpos : 0 < ∏ i : Fin I.m, ((I.P i).card : ℝ) := by
    refine Finset.prod_pos ?_
    intro i _
    exact Nat.cast_pos.mpr (lt_of_lt_of_le I.hM_min (I.hPsize i))
  exact (le_div_iff₀ hpos).mp h

/-- A good leading coefficient is a squarefree principal-genus product of the
prescribed split primes, i.e. the counted shape of L25. -/
theorem goodLeading_squarefree_and_principal {A : ℕ} (hA : A ∈ I.goodLeading) :
    Squarefree A ∧ Nat.Coprime A (8 * N) ∧
      ∀ S ⊆ N.primeFactors,
        genusCharReal N S (A : ZMod (8 * N)) = 1 := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hA
  have hgood : (∏ i, genusMap N (t i).1) = 1 ∧
      Function.Injective (fun i => (t i).1) := by
    simpa [goodTuples] using ht
  exact distinct_prime_tuple_prod_squarefree_and_principal I.P
    (fun i p hp => I.hPprime i p hp) I.hPcop t hgood.1 hgood.2

/-- A good tuple's chosen witness form lies in `goodForms`. -/
theorem witnessForm_mem_goodForms {t : ∀ i : Fin I.m, {p : ℕ // p ∈ I.P i}}
    (ht : t ∈ I.goodTuples) : I.witnessForm t ∈ I.goodForms := by
  classical
  have hgood : (∏ i, genusMap N (t i).1) = 1 ∧
      Function.Injective (fun i => (t i).1) := by
    simpa [goodTuples] using ht
  simp only [witnessForm, dif_pos hgood]
  let f := Classical.choose (I.realized t hgood.1 hgood.2)
  have hfR : f ∈ ReducedForms N :=
    (Classical.choose_spec (I.realized t hgood.1 hgood.2)).1
  have hfA : f.1 = ∏ i, (t i).1 :=
    (Classical.choose_spec (I.realized t hgood.1 hgood.2)).2
  change f ∈ I.goodForms
  refine Finset.mem_filter.mpr ⟨hfR, ?_⟩
  exact Finset.mem_image.mpr ⟨t, ht, hfA.symm⟩

/-- Distinct good tuples give distinct witness forms, because their leading
coefficients are distinct products. -/
theorem witnessForm_injOn :
    Set.InjOn I.witnessForm
      (I.goodTuples : Set (∀ i : Fin I.m, {p : ℕ // p ∈ I.P i})) := by
  intro t ht s hs heq
  classical
  have htgood : (∏ i, genusMap N (t i).1) = 1 ∧
      Function.Injective (fun i => (t i).1) := by
    simpa [goodTuples] using ht
  have hsgood : (∏ i, genusMap N (s i).1) = 1 ∧
      Function.Injective (fun i => (s i).1) := by
    simpa [goodTuples] using hs
  rw [witnessForm, dif_pos htgood, witnessForm, dif_pos hsgood] at heq
  have htSpec := Classical.choose_spec (I.realized t htgood.1 htgood.2)
  have hsSpec := Classical.choose_spec (I.realized s hsgood.1 hsgood.2)
  have hlead : (∏ i, (t i).1) = (∏ i, (s i).1) := by
    have hfst := congrArg Prod.fst heq
    simpa [htSpec.2, hsSpec.2] using hfst
  exact prod_tuple_injective I.hPprime I.hPdisj hlead

/-- The bridge L25 converts the combinatorial lower bound on good tuples into
a lower bound on the number of reduced forms with a good leading coefficient. -/
theorem goodTuples_card_le_goodForms_card : I.goodTuples.card ≤ I.goodForms.card := by
  classical
  refine Finset.card_le_card_of_injOn I.witnessForm ?_ ?_
  · intro t ht
    exact I.witnessForm_mem_goodForms ht
  · intro t ht s hs heq
    exact I.witnessForm_injOn ht hs heq

theorem goodForms_subset_reducedForms : I.goodForms ⊆ ReducedForms N := by
  intro f hf
  exact (Finset.mem_filter.mp hf).1

/-- The L24 lower class-number bound makes the uniform slot denominator
positive. -/
theorem reducedForms_card_pos (I : PrivateSupplyInputs N) :
    0 < ((ReducedForms N).card : ℝ) := by
  have hN3 := I.hN3
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast I.hNpos)
  have hlowpos : 0 < (1 / 8 : ℝ) * Real.sqrt (N : ℝ) / Real.log (N : ℝ) := by
    positivity
  exact lt_of_lt_of_le hlowpos I.classBounds.lower

/-- Probability that one uniformly random private slot yields a counted
shape, i.e. a reduced form whose leading coefficient is a good band product. -/
noncomputable def privateSlotProbability : ℝ :=
  ((privateSlotPMF N I.hNpos).toOuterMeasure {f | f ∈ I.goodForms}).toReal

theorem privateSlotProbability_eq_ratio :
    I.privateSlotProbability =
      ((I.goodForms).card : ℝ) / ((ReducedForms N).card : ℝ) := by
  classical
  simp only [privateSlotProbability, privateSlotPMF,
    PMF.toOuterMeasure_uniformOfFinset_apply, Set.mem_ofPred_eq]
  have hfilter : (ReducedForms N).filter (fun x => x ∈ I.goodForms) = I.goodForms := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hg⟩
      exact hg
    · intro hg
      exact ⟨I.goodForms_subset_reducedForms hg, hg⟩
  rw [hfilter, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Exact combinatorial lower bound for the private-slot probability. -/
theorem privateSlotProbability_lower :
    I.principalGenusFraction * (∏ i : Fin I.m, ((I.P i).card : ℝ)) /
        ((ReducedForms N).card : ℝ) ≤ I.privateSlotProbability := by
  rw [I.privateSlotProbability_eq_ratio]
  have htuples := I.goodTuples_card_lower
  have hforms : (I.goodTuples.card : ℝ) ≤ (I.goodForms.card : ℝ) := by
    exact_mod_cast I.goodTuples_card_le_goodForms_card
  have hden : 0 < ((ReducedForms N).card : ℝ) := I.reducedForms_card_pos
  calc
    _ ≤ (I.goodTuples.card : ℝ) / ((ReducedForms N).card : ℝ) :=
      div_le_div_of_nonneg_right htuples hden.le
    _ ≤ (I.goodForms.card : ℝ) / ((ReducedForms N).card : ℝ) :=
      div_le_div_of_nonneg_right hforms hden.le

/-- The reduced-form leading-coefficient cutoff `sqrt(8N/3)`. -/
def privateBandBound (N : ℕ) : ℕ := Nat.sqrt (8 * N / 3)

/-- The certified-prefix set with trivial prefix and with each band part a
single prime below the reduced-form cutoff. -/
noncomputable def certifiedBandSet (N m : ℕ) : Finset ℕ :=
  certifiedPrefixSet (fun _ : Fin m => 1) (fun _ : Fin m => privateBandBound N)
    (privateBandBound N) m

/-- Primitive Num lemma: a finite product of primes has at most `m` prime
factors. -/
lemma primeFactors_prod_card_le {m : ℕ} {f : Fin m → ℕ}
    (hprime : ∀ i, (f i).Prime) :
    (∏ i, f i).primeFactors.card ≤ m := by
  have hsub : (∏ i, f i).primeFactors ⊆ Finset.univ.image f := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hdvd : q ∣ ∏ i, f i := Nat.dvd_of_mem_primeFactors hq
    obtain ⟨i, -, hqi⟩ := (Prime.dvd_finsetProd_iff hqprime.prime f).mp hdvd
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
      ((Nat.prime_dvd_prime_iff_eq hqprime (hprime i)).mp hqi).symm⟩
  calc
    (∏ i, f i).primeFactors.card ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = m := by simp

/-- A finite product of distinct primes has at least `m` prime factors. -/
lemma primeFactors_prod_card_ge_of_injective {m : ℕ} {f : Fin m → ℕ}
    (hprime : ∀ i, (f i).Prime) (hinj : Function.Injective f) :
    m ≤ (∏ i, f i).primeFactors.card := by
  have hsub : Finset.univ.image f ⊆ (∏ i, f i).primeFactors := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mem_primeFactors.mpr
      ⟨hprime i, Finset.dvd_prod_of_mem f (Finset.mem_univ i),
        Finset.prod_ne_zero_iff.mpr (fun j _ => (hprime j).ne_zero)⟩
  calc
    m = (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ (∏ i, f i).primeFactors.card := Finset.card_le_card hsub

theorem privateBandBound_pos (I : PrivateSupplyInputs N) : 1 ≤ privateBandBound N := by
  unfold privateBandBound
  apply Nat.le_sqrt.mpr
  have hN3 := I.hN3
  have h : (1 : ℕ) ^ 2 ≤ 8 * N / 3 := by
    norm_num
    omega
  simpa using h

/-- Every good leading coefficient is a certified prefix integer: take the
prefix `1` and the tuple itself as the band parts. -/
theorem goodLeading_subset_certifiedBandSet :
    I.goodLeading ⊆ certifiedBandSet N I.m := by
  classical
  intro A hA
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hA
  have hgood : (∏ i, genusMap N (t i).1) = 1 ∧
      Function.Injective (fun i => (t i).1) := by
    simpa [goodTuples] using ht
  let f := Classical.choose (I.realized t hgood.1 hgood.2)
  have hfR : f ∈ ReducedForms N :=
    (Classical.choose_spec (I.realized t hgood.1 hgood.2)).1
  have hfA : f.1 = ∏ i, (t i).1 :=
    (Classical.choose_spec (I.realized t hgood.1 hgood.2)).2
  have hU : (∏ i, (t i).1) ≤ privateBandBound N := by
    rw [← hfA]
    exact leading_le_sqrt (mem_reducedForms.mp hfR)
  have hprodpos : 0 < ∏ i, (t i).1 :=
    Finset.prod_pos fun i _ => (I.hPprime i (t i).1 (t i).2).pos
  unfold certifiedBandSet
  refine Finset.mem_image.mpr ⟨(1, fun i => (t i).1), ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨le_rfl, I.privateBandBound_pos⟩
    · refine Fintype.mem_piFinset.mpr fun i => ?_
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_Icc.mpr ⟨(I.hPprime i (t i).1 (t i).2).pos, ?_⟩
        exact (Nat.le_of_dvd hprodpos
          (Finset.dvd_prod_of_mem (fun j => (t j).1) (Finset.mem_univ i))).trans hU
      · refine ⟨(I.hPprime i (t i).1 (t i).2).pos, ?_⟩
        intro q hq
        have hqeq : q = (t i).1 := by
          simpa [smoothBandParts, (I.hPprime i (t i).1 (t i).2).primeFactors] using hq
        rw [hqeq]
        exact (Nat.le_of_dvd hprodpos
          (Finset.dvd_prod_of_mem (fun j => (t j).1) (Finset.mem_univ i))).trans hU
    · simpa using hU
    · simpa using primeFactors_prod_card_le (fun i => I.hPprime i (t i).1 (t i).2)
    · intro i j hij
      have hne : (t i).1 ≠ (t j).1 := fun heq => hij (hgood.2 heq)
      exact (Nat.coprime_primes (I.hPprime i (t i).1 (t i).2)
        (I.hPprime j (t j).1 (t j).2)).mpr hne
  · simp

/-- Rankin's inequality bounds the `2^{ω(A)}`-weighted good-leading-coefficient
count by the product of the band Euler products. -/
theorem goodLeading_weighted_sum_le_rankin :
    (∑ A ∈ I.goodLeading, (2 : ℝ) ^ A.primeFactors.card) ≤
      (2 : ℝ) ^ I.m * (privateBandBound N : ℝ) *
        (1 + Real.log (privateBandBound N : ℝ)) *
        ∏ _i : Fin I.m,
          ((1 : ℝ) ^ ((1 / 2 : ℝ) - 1) *
            ∏ p ∈ primesUpTo (privateBandBound N),
              (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) := by
  have hsub := I.goodLeading_subset_certifiedBandSet
  have hrank := certified_prefix_rankin_bound
    (fun _ : Fin I.m => 1) (fun _ : Fin I.m => privateBandBound N)
    (fun _ : Fin I.m => (1 / 2 : ℝ)) (privateBandBound N) I.m
    (I.privateBandBound_pos) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun _ => by norm_num)
  simpa using
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hrank

/-- The Rankin upper estimate for the number of good leading coefficients. -/
theorem goodLeading_card_le_rankin :
    (I.goodLeading.card : ℝ) ≤
      (privateBandBound N : ℝ) * (1 + Real.log (privateBandBound N : ℝ)) *
        ∏ _i : Fin I.m,
          ((1 : ℝ) ^ ((1 / 2 : ℝ) - 1) *
            ∏ p ∈ primesUpTo (privateBandBound N),
              (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) := by
  have hterm : ∀ A ∈ I.goodLeading,
      (2 : ℝ) ^ I.m ≤ (2 : ℝ) ^ A.primeFactors.card := by
    intro A hA
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hA
    have hgood : (∏ i, genusMap N (t i).1) = 1 ∧
        Function.Injective (fun i => (t i).1) := by
      simpa [goodTuples] using ht
    exact pow_le_pow_right₀ (by norm_num)
      (primeFactors_prod_card_ge_of_injective
        (fun i => I.hPprime i (t i).1 (t i).2) hgood.2)
  have hweight : (2 : ℝ) ^ I.m * (I.goodLeading.card : ℝ) ≤
      ∑ A ∈ I.goodLeading, (2 : ℝ) ^ A.primeFactors.card := by
    calc
      (2 : ℝ) ^ I.m * (I.goodLeading.card : ℝ) =
          ∑ _A ∈ I.goodLeading, (2 : ℝ) ^ I.m := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ A ∈ I.goodLeading, (2 : ℝ) ^ A.primeFactors.card :=
        Finset.sum_le_sum hterm
  have hpow : 0 < (2 : ℝ) ^ I.m := by positivity
  have hmul : (2 : ℝ) ^ I.m * (I.goodLeading.card : ℝ) ≤
      (2 : ℝ) ^ I.m * (privateBandBound N : ℝ) *
        (1 + Real.log (privateBandBound N : ℝ)) *
        ∏ _i : Fin I.m,
          ((1 : ℝ) ^ ((1 / 2 : ℝ) - 1) *
            ∏ p ∈ primesUpTo (privateBandBound N),
              (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) :=
    hweight.trans I.goodLeading_weighted_sum_le_rankin
  have hmul' : (2 : ℝ) ^ I.m * (I.goodLeading.card : ℝ) ≤
      (2 : ℝ) ^ I.m * ((privateBandBound N : ℝ) *
        (1 + Real.log (privateBandBound N : ℝ)) *
        ∏ _i : Fin I.m,
          ((1 : ℝ) ^ ((1 / 2 : ℝ) - 1) *
            ∏ p ∈ primesUpTo (privateBandBound N),
              (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹)) := by
    simpa [mul_assoc] using hmul
  exact (mul_le_mul_iff_of_pos_left hpow).mp hmul'

end PrivateSupplyInputs

/-! ## Section 3: Absorbing polynomial factors and the slot loss on the `H`-scale -/

/-- `log n` is at most a constant multiple of the bit length. -/
private theorem log_two_mul_le_bit {n : ℕ} (hn : 1 ≤ n) :
    1 + Real.log (2 * (n : ℝ)) ≤
      (1 + 2 * Real.log 2) * ((n.log2 : ℝ) + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbits : Real.log (n : ℝ) ≤ ((n.log2 : ℝ) + 1) * Real.log 2 := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (n.log2 + 1)) := by
        apply Real.log_le_log hnpos
        exact_mod_cast (Nat.lt_log2_self (n := n)).le
      _ = ((n.log2 + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ = _ := by push_cast; ring
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hnpos.ne']
  rw [hlog2n]
  nlinarith [hbits, hlog2, Nat.cast_nonneg (α := ℝ) n.log2]

/-- A fixed polynomial in the natural logarithm is `exp(o(H))`. -/
theorem eventually_const_mul_log_pow_le_exp {C : ℝ} (hC : 0 ≤ C) {η : ℝ}
    (hη : 0 < η) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * (1 + Real.log (2 * (n : ℝ))) ^ k ≤ Real.exp (η * scale n) := by
  let B : ℝ := 1 + 2 * Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_bitPoly_le_exp (A := C * B ^ k) hη k] with n hn hp
  have hlog : 1 + Real.log (2 * (n : ℝ)) ≤ B * ((n.log2 : ℝ) + 1) :=
    log_two_mul_le_bit hn
  have hnonneg : 0 ≤ 1 + Real.log (2 * (n : ℝ)) := by
    have h2n : (1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (show 1 ≤ 2 * n by omega)
    linarith [Real.log_nonneg h2n]
  have hpow : (1 + Real.log (2 * (n : ℝ))) ^ k ≤
      (B * ((n.log2 : ℝ) + 1)) ^ k := pow_le_pow_left₀ hnonneg hlog k
  calc
    C * (1 + Real.log (2 * (n : ℝ))) ^ k
        ≤ C * (B * ((n.log2 : ℝ) + 1)) ^ k :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = (C * B ^ k) * ((n.log2 : ℝ) + 1) ^ k := by rw [mul_pow]; ring
    _ ≤ Real.exp (η * scale n) := hp

/-- `exp(-C k)` with `k = o(H)` is absorbed by `exp(-η H)`. -/
theorem eventually_exp_neg_mul_le_exp_neg_of_div_tendsto_zero {k : ℕ → ℝ} {C : ℝ}
    (hk : Tendsto (fun n => k n / scale n) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-η * scale n) ≤ Real.exp (-C * k n) := by
  have hdiv : Tendsto (fun n => C * (k n / scale n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hk
  have hsmall : ∀ᶠ n : ℕ in atTop, C * (k n / scale n) < η :=
    hdiv.eventually_lt_const hη
  filter_upwards [hsmall, scale_grows.eventually_gt_atTop 0] with n hn hs
  have hmul : C * k n < η * scale n := by
    have h : C * (k n / scale n) * scale n = C * k n := by
      field_simp [hs.ne']
    rw [← h]
    exact mul_lt_mul_of_pos_right hn hs
  rw [Real.exp_le_exp]
  linarith

/-! ## Section 4: Assembly of the private-slot supply estimate -/

/-- The conclusion form `P(slot good) ≥ exp(-(S + o(1)) H)`. -/
def IsExpLowerBoundWithSlope (p : ℕ → ℝ) (S : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    Real.exp (-(S + η) * scale n) ≤ p n

/-- Main reduction: the combinatorial bound plus the named analytic supply
estimate gives the L23--L26 probability lower bound. -/
theorem privateSlotProbability_isExpLowerBound
    (I : ∀ n : ℕ, PrivateSupplyInputs n) {S : ℝ}
    (hsupply : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Real.exp (-(S + η) * scale n) ≤
        (I n).principalGenusFraction *
          (∏ i : Fin (I n).m, (((I n).P i).card : ℝ)) /
          ((ReducedForms n).card : ℝ))
    : IsExpLowerBoundWithSlope (fun n => (I n).privateSlotProbability) S := by
  intro η hη
  filter_upwards [hsupply η hη] with n hn
  exact hn.trans (I n).privateSlotProbability_lower

/-- Band/genus form of the assembly: the genus fraction and the band product
are bounded separately, the class-number upper bound is the explicit L24
factor, and the polylogarithmic loss is absorbed on the `H`-scale. -/
theorem privateSlotProbability_isExpLowerBound_of_band_genus
    (I : ∀ n : ℕ, PrivateSupplyInputs n) {Sg Sb : ℝ}
    (hgenus : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Real.exp (-(Sg + η) * scale n) ≤ (I n).principalGenusFraction)
    (hband : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Real.exp (-(Sb + η) * scale n) * Real.sqrt (n : ℝ) ≤
        ∏ i : Fin (I n).m, (((I n).P i).card : ℝ))
    : IsExpLowerBoundWithSlope (fun n => (I n).privateSlotProbability) (Sg + Sb) := by
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  filter_upwards [hgenus (η / 3) hη3, hband (η / 3) hη3,
    eventually_const_mul_log_pow_le_exp (C := 2 * Real.exp 18) (by positivity) hη3 7,
    eventually_ge_atTop (1 : ℕ)] with n hg hb hlog hn
  let G : ℝ := ((ReducedForms n).card : ℝ)
  let fr : ℝ := (I n).principalGenusFraction
  let band : ℝ := ∏ i : Fin (I n).m, (((I n).P i).card : ℝ)
  let L : ℝ := (2 * Real.exp 18) * (1 + Real.log (2 * (n : ℝ))) ^ 7
  have hGpos : 0 < G := (I n).reducedForms_card_pos
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hlogarg : 0 < 1 + Real.log (2 * (n : ℝ)) := by
    have h2n : (1 : ℝ) < 2 * (n : ℝ) := by
      exact_mod_cast (show 1 < 2 * n by omega)
    linarith [Real.log_pos h2n]
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (by positivity) (pow_pos hlogarg 7)
  have hfr_nonneg : 0 ≤ fr := le_trans (Real.exp_pos _).le hg
  have hband_nonneg : 0 ≤ band :=
    le_trans (mul_nonneg (Real.exp_pos _).le hsqrtpos.le) hb
  have hclass : G ≤ L * Real.sqrt (n : ℝ) := by
    calc
      G = ((ReducedForms n).card : ℝ) := rfl
      _ ≤ (2 * Real.exp 18) * Real.sqrt (n : ℝ) *
            (1 + Real.log (2 * (n : ℝ))) ^ 7 := (I n).classBounds.upper
      _ = L * Real.sqrt (n : ℝ) := by dsimp [L]; ring
  have hinv : 1 / (L * Real.sqrt (n : ℝ)) ≤ 1 / G :=
    one_div_le_one_div_of_le hGpos hclass
  have hfactor :
      Real.exp (-(Sg + η / 3) * scale n) *
          (Real.exp (-(Sb + η / 3) * scale n) * Real.sqrt (n : ℝ)) *
          (1 / (L * Real.sqrt (n : ℝ))) ≤ fr * band * (1 / G) := by
    have h1 : Real.exp (-(Sg + η / 3) * scale n) *
          (Real.exp (-(Sb + η / 3) * scale n) * Real.sqrt (n : ℝ)) ≤
        fr * band :=
      mul_le_mul hg hb (mul_nonneg (Real.exp_pos _).le hsqrtpos.le) hfr_nonneg
    exact mul_le_mul h1 hinv (by positivity) (mul_nonneg hfr_nonneg hband_nonneg)
  have heq :
      Real.exp (-(Sg + η / 3) * scale n) *
          (Real.exp (-(Sb + η / 3) * scale n) * Real.sqrt (n : ℝ)) *
          (1 / (L * Real.sqrt (n : ℝ))) =
        Real.exp (-(Sg + η / 3) * scale n) *
          Real.exp (-(Sb + η / 3) * scale n) * (1 / L) := by
    field_simp [hLpos.ne', hsqrtpos.ne']
  have hAB :
      Real.exp (-(Sg + η / 3) * scale n) *
          Real.exp (-(Sb + η / 3) * scale n) =
        Real.exp (-(Sg + Sb + 2 * η / 3) * scale n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmulLog :
      Real.exp (-(η / 3) * scale n) * L ≤ 1 := by
    calc
      Real.exp (-(η / 3) * scale n) * L
          ≤ Real.exp (-(η / 3) * scale n) *
              Real.exp ((η / 3) * scale n) :=
        mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hLinv : Real.exp (-(η / 3) * scale n) ≤ 1 / L :=
    (le_div_iff₀ hLpos).mpr hmulLog
  have htarget :
      Real.exp (-(Sg + Sb + η) * scale n) ≤
        Real.exp (-(Sg + η / 3) * scale n) *
          Real.exp (-(Sb + η / 3) * scale n) * (1 / L) := by
    have he : Real.exp (-(Sg + Sb + η) * scale n) =
        Real.exp (-(Sg + Sb + 2 * η / 3) * scale n) *
          Real.exp (-(η / 3) * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, hAB]
    exact mul_le_mul_of_nonneg_left hLinv (Real.exp_pos _).le
  calc
    Real.exp (-(Sg + Sb + η) * scale n)
        ≤ Real.exp (-(Sg + η / 3) * scale n) *
          Real.exp (-(Sb + η / 3) * scale n) * (1 / L) := htarget
    _ = Real.exp (-(Sg + η / 3) * scale n) *
          (Real.exp (-(Sb + η / 3) * scale n) * Real.sqrt (n : ℝ)) *
          (1 / (L * Real.sqrt (n : ℝ))) := heq.symm
    _ ≤ fr * band * (1 / G) := hfactor
    _ = fr * band / G := by ring
    _ ≤ (I n).privateSlotProbability := (I n).privateSlotProbability_lower

/-! ## Section 5: The finite screening floor, gate telescoping, and slot loss -/

/-- The finite stage profile of the private screening pass.  The fields are
exactly the hypotheses of `finite_stage_private_floor`, plus nonnegativity of
the stage cutoffs needed by the gate estimates. -/
structure PrivateScreeningProfile where
  stages : ℕ
  z : ℕ → ℝ
  weight : ℕ → ℝ
  h : ℝ
  P : ℝ
  hh : 0 ≤ h
  hz0 : z 0 = 0
  hzn : z stages = 1
  hstep : ∀ i < stages, z i ≤ z (i + 1)
  hzero : ∀ i < stages, 0 ≤ z i
  htail : ∀ i < stages, (∑ j ∈ Finset.Ico i stages, weight j) ≤ P - h * z (i + 1)

namespace PrivateScreeningProfile

variable (S : PrivateScreeningProfile)

/-- `RandomizedPrivateFloor`: the integrated private screening cost is at most
the budget. -/
theorem floor_le_budget :
    (∑ i ∈ Finset.range S.stages, S.z (i + 1) ^ 2 * S.weight i) + 2 * S.h / 3 ≤ S.P :=
  Cogentic.finite_stage_private_floor S.z S.weight S.hh S.hz0 S.hzn S.hstep S.htail

/-- `RandomizedPrivateGates`: the stage costs telescope to the final stage. -/
theorem gate_telescope {i : ℕ} (hi : i ≤ S.stages) (terminal : ℝ) :
    S.h * S.z i +
        (∑ j ∈ Finset.Ico i S.stages, S.h * (S.z (j + 1) - S.z j)) + terminal =
      S.h * S.z S.stages + terminal :=
  Cogentic.RandomizedPrivateGates.gate_equalization S.z S.h terminal hi

/-- `RandomizedPrivateGates`: a budget strictly above the cubic bound leaves a
positive terminal weight. -/
theorem positive_remainder {budget : ℝ}
    (hbudget : (S.h / 3) * (S.z S.stages ^ 3 - S.z 0 ^ 3) < budget) :
    0 < budget -
      ∑ j ∈ Finset.range S.stages, S.z j ^ 2 * (S.h * (S.z (j + 1) - S.z j)) :=
  Cogentic.RandomizedPrivateGates.terminal_weight_pos S.z S.hh S.hstep S.hzero hbudget

end PrivateScreeningProfile

/-- `exp (C * cost)` with `cost` capped by a sublinear `k₀ = o(H)` is absorbed
on the `H`-scale.  This is the `exp(O(k₀)) = exp(o(H))` slot-loss step of L26. -/
theorem slotLoss_le_exp_of_capped {cost : ℕ → ℝ} {k₀ : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hcap : ∀ᶠ n : ℕ in atTop, cost n ≤ 2 * (k₀ n : ℝ))
    (hk : Tendsto (fun n => (k₀ n : ℝ) / scale n) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.exp (C * cost n) ≤ Real.exp (η * scale n) := by
  have hdiv : Tendsto (fun n => (2 * C) * ((k₀ n : ℝ) / scale n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hk
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 * C) * ((k₀ n : ℝ) / scale n) < η :=
    hdiv.eventually_lt_const hη
  filter_upwards [hsmall, hcap, scale_grows.eventually_gt_atTop 0] with n hn hc hs
  have hcost : C * cost n ≤ η * scale n := by
    have h1 : C * cost n ≤ C * (2 * (k₀ n : ℝ)) :=
      mul_le_mul_of_nonneg_left hc hC
    have h2 : C * (2 * (k₀ n : ℝ)) =
        ((2 * C) * ((k₀ n : ℝ) / scale n)) * scale n := by
      field_simp [hs.ne']
    rw [h2] at h1
    exact h1.trans (le_of_lt (mul_lt_mul_of_pos_right hn hs))
  rwa [Real.exp_le_exp]

/-- `RandomizedBalancedAllocation`: the rounded private allocation eventually
keeps the total factor count below `2 * k₀`. -/
theorem privateAllocation_eventually_capped
    {a w : ℕ → ℚ} {M : ℚ} {k₀ : ℕ → ℕ} {last : ℕ}
    (hK : Tendsto k₀ atTop atTop)
    (hsmall : Tendsto (fun n => (k₀ n : ℝ) / n) atTop (𝓝 0))
    (ha : ∀ i ≤ last, 0 < a i) (hw : ∀ i ≤ last, 0 < w i) (hM : 0 < M)
    (hmoment : ∑ i ∈ Finset.range (last + 1), a i * w i = M)
    (hcount : (∑ i ∈ Finset.range (last + 1), w i) < 2 * M)
    (front : ℕ → ℝ) (C : ℝ)
    (hgate : ∀ i ≤ last, front i + (∑ j ∈ Finset.Ico i (last + 1), (w j : ℝ)) < C) :
    ∀ᶠ n : ℕ in atTop,
      (∑ i ∈ Finset.range (last + 1),
        Cogentic.RandomizedBalancedAllocation.factorCount
          (Cogentic.RandomizedBalancedAllocation.bitShare last
            (Cogentic.RandomizedBalancedAllocation.privateFraction a w M)
            (Cogentic.RandomizedBalancedAllocation.coordinateBits n) i)
          (Cogentic.RandomizedBalancedAllocation.bandExponent (a i)
            (Cogentic.RandomizedBalancedAllocation.topExponent n (k₀ n)))) <
        2 * k₀ n :=
  (Cogentic.RandomizedBalancedAllocation.private_allocation_preserves_caps
    hK hsmall ha hw hM hmoment hcount front C hgate).2.mono fun _ hn => hn.1

/-- The private-slot probability with the L26 slot loss `exp(-C k₀)` in the band
factor.  Since `k₀ = o(H)`, the loss is absorbed into the exponent slack. -/
theorem privateSlotProbability_isExpLowerBound_of_band_genus_slotLoss
    (I : ∀ n : ℕ, PrivateSupplyInputs n) {Sg Sb Cslot : ℝ} {k₀ : ℕ → ℕ}
    (hk₀ : Tendsto (fun n => (k₀ n : ℝ) / scale n) atTop (𝓝 0))
    (hgenus : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Real.exp (-(Sg + η) * scale n) ≤ (I n).principalGenusFraction)
    (hband : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Real.exp (-(Sb + η) * scale n) * Real.sqrt (n : ℝ) *
          Real.exp (-Cslot * (k₀ n : ℝ)) ≤
        ∏ i : Fin (I n).m, (((I n).P i).card : ℝ))
    : IsExpLowerBoundWithSlope (fun n => (I n).privateSlotProbability) (Sg + Sb) := by
  refine privateSlotProbability_isExpLowerBound_of_band_genus I hgenus ?_
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  filter_upwards [hband (η / 2) hη2,
    eventually_exp_neg_mul_le_exp_neg_of_div_tendsto_zero
      (k := fun n => (k₀ n : ℝ)) (C := Cslot) hk₀ hη2]
    with n hb hslot
  calc
    Real.exp (-(Sb + η) * scale n) * Real.sqrt (n : ℝ)
        = (Real.exp (-(Sb + η / 2) * scale n) * Real.sqrt (n : ℝ)) *
            Real.exp (-(η / 2) * scale n) := by
          have harg : -(Sb + η) * scale n =
              (-(Sb + η / 2) * scale n) + (-(η / 2) * scale n) := by ring
          rw [harg, Real.exp_add]
          ring
    _ ≤ (Real.exp (-(Sb + η / 2) * scale n) * Real.sqrt (n : ℝ)) *
          Real.exp (-Cslot * (k₀ n : ℝ)) :=
      mul_le_mul_of_nonneg_left hslot (by positivity)
    _ = Real.exp (-(Sb + η / 2) * scale n) * Real.sqrt (n : ℝ) *
          Real.exp (-Cslot * (k₀ n : ℝ)) := by ring
    _ ≤ ∏ i : Fin (I n).m, (((I n).P i).card : ℝ) := hb

#print axioms Cogentic.RandomizedEpochPrivate.classBounds_of_criticalLine
#print axioms Cogentic.RandomizedEpochPrivate.splitBand_bias_after_deletion_from_criticalLine
#print axioms Cogentic.RandomizedEpochPrivate.splitBand_card_lower_from_criticalLine
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.goodTuples_card_lower
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.principalGenusFraction_ge_inv_four_g
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.goodLeading_squarefree_and_principal
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.goodLeading_card_le_rankin
#print axioms Cogentic.RandomizedEpochPrivate.PrivateSupplyInputs.privateSlotProbability_lower
#print axioms Cogentic.RandomizedEpochPrivate.PrivateScreeningProfile.floor_le_budget
#print axioms Cogentic.RandomizedEpochPrivate.PrivateScreeningProfile.gate_telescope
#print axioms Cogentic.RandomizedEpochPrivate.PrivateScreeningProfile.positive_remainder
#print axioms Cogentic.RandomizedEpochPrivate.privateAllocation_eventually_capped
#print axioms Cogentic.RandomizedEpochPrivate.slotLoss_le_exp_of_capped
#print axioms Cogentic.RandomizedEpochPrivate.privateSlotProbability_isExpLowerBound
#print axioms Cogentic.RandomizedEpochPrivate.privateSlotProbability_isExpLowerBound_of_band_genus
#print axioms Cogentic.RandomizedEpochPrivate.privateSlotProbability_isExpLowerBound_of_band_genus_slotLoss

end

end Cogentic.RandomizedEpochPrivate
