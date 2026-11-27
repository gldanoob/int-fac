import Cogentic.RandomizedL20_2Decay

set_option linter.style.haveILetI false

/-!
# L20.2: prime-bin character decay on nonempty bins

`Cogentic.RandomizedL20_2Decay` reduces the explicit L20.2 character decay

```
PrimeBinCharacterDecay K c q A B n :
  primeBinRelativeEnvelope K q A B ≤
    exp (-(c D log D)) * (primeBinProducts A B).card
```

to the width condition `PrimeBinEnvelopeWidthCore`, but its reduction assumes
the interval endpoints satisfy `2 ≤ A i` and `A i ≤ B i`.  This file records the
correct hypothesis at the level of the actual bins: *every bin contains at least
one prime*.

Two points are established.

* A nonempty prime bin already supplies the two endpoint facts used in the
  width-to-cardinality step (`2 ≤ B i`, `A i < B i`, and hence
  `log (B i) > 0`).  For `A i < 2` we use the same critical-line theta estimate
  directly, because `theta (A i) = 0` and `B i - A i ≤ B i`; this removes the
  artificial lower endpoint assumption `2 ≤ A i`.
* Conversely, for `K > 0` and positive upper endpoints, the decay forces every
  bin to be nonempty.  This is the support-theoretic boundary isolated by
  `primeBinCharacterDecay_false_of_emptyBin`; the remaining quantitative gap is
  precisely the width condition.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  The primes in each
bin are counted, no cardinality is replaced by zero, and the GRH supply estimate
is used in its original form.
-/

namespace Cogentic.RandomizedL20_2DecayNonempty

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_2Decay
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Elementary consequences of a nonempty prime bin -/

/-- A nonempty prime bin has upper endpoint at least `2`. -/
theorem two_le_of_primeBin_nonempty {A B : ℕ} (h : (primeBin A B).Nonempty) :
    2 ≤ B := by
  obtain ⟨p, hp⟩ := h
  have hp' := Finset.mem_filter.mp hp
  exact hp'.2.two_le.trans (Finset.mem_Ioc.mp hp'.1).2

/-- A nonempty prime bin has `A < B`. -/
theorem lt_of_primeBin_nonempty {A B : ℕ} (h : (primeBin A B).Nonempty) :
    A < B := by
  obtain ⟨p, hp⟩ := h
  have hp' := Finset.mem_filter.mp hp
  exact lt_of_lt_of_le (Finset.mem_Ioc.mp hp'.1).1 (Finset.mem_Ioc.mp hp'.1).2

/-- A nonempty prime bin has upper endpoint greater than one, so its logarithm
is positive. -/
theorem one_lt_of_primeBin_nonempty {A B : ℕ} (h : (primeBin A B).Nonempty) :
    1 < B :=
  lt_of_lt_of_le (by norm_num) (two_le_of_primeBin_nonempty h)

/-- A nonempty prime bin has positive cardinality. -/
theorem card_pos_of_primeBin_nonempty {A B : ℕ} (h : (primeBin A B).Nonempty) :
    0 < (primeBin A B).card :=
  Finset.card_pos.mpr h

/-- Increasing a lower endpoint only removes primes, so the prime bin shrinks. -/
theorem primeBin_subset_of_le {A A' B : ℕ} (hAA' : A ≤ A') :
    primeBin A' B ⊆ primeBin A B := by
  intro p hp
  simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
  exact ⟨⟨lt_of_le_of_lt hAA' hp.1.1, hp.1.2⟩, hp.2⟩

/-- The logarithmic theta sum over a prime bin is the difference of the theta
functions at the two endpoints. -/
theorem sum_log_primeBin_eq {A B : ℕ} (hAB : A ≤ B) :
    (∑ p ∈ primeBin A B, Real.log p) = Chebyshev.theta B - Chebyshev.theta A := by
  have hbin : primeBin A B = Nat.primesLE B \ Nat.primesLE A := by
    ext p
    simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hA, hB⟩, hp⟩
      exact ⟨⟨hB, hp⟩, fun h => (not_le_of_gt hA) h.1⟩
    · rintro ⟨⟨hB, hp⟩, hA⟩
      exact ⟨⟨lt_of_not_ge (fun h => hA ⟨h, hp⟩), hB⟩, hp⟩
  rw [hbin, Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  exact eq_sub_of_add_eq (Finset.sum_sdiff (Nat.primesLE_mono hAB))

/-! ## 2. The GRH supply estimate without the endpoint hypothesis `2 ≤ A` -/

/-- **The prime-supply lower bound for any nonempty bin.**  The existing
estimate is stated for `2 ≤ A`.  For `A < 2` we argue directly from the same
critical-line theta estimate: `theta A = 0`, the error at `B` controls
`theta B`, and `B - A ≤ B` absorbs the missing lower endpoint.  The constant is
`2 c`, matching `primeBin_supply_from_critical_line`. -/
theorem primeBin_supply_nonempty_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ A B : ℕ, A ≤ B → (primeBin A B).Nonempty →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B := by
  obtain ⟨c, hc, hθ⟩ := Window.principal_theta_from_critical_line line
  refine ⟨2 * c, by linarith, ?_⟩
  intro A B hAB hne
  have hB : 2 ≤ B := two_le_of_primeBin_nonempty hne
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  let err : ℝ := c * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B
  have herr_nonneg : 0 ≤ err := by
    unfold err
    positivity
  have hlog : (∑ p ∈ primeBin A B, Real.log p) ≤
      ((primeBin A B).card : ℝ) * Real.log B := by
    calc
      (∑ p ∈ primeBin A B, Real.log p) ≤ ∑ _p ∈ primeBin A B, Real.log B := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpB, hpPrime⟩ := Finset.mem_filter.mp hp
        exact Real.log_le_log (Nat.cast_pos.mpr hpPrime.pos)
          (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpB).2)
      _ = ((primeBin A B).card : ℝ) * Real.log B := by
        simp [nsmul_eq_mul]
  rcases Nat.lt_or_ge A 2 with hA | hA
  · -- `A = 0` or `A = 1`, so `theta A = 0`.
    have hthetaA : Chebyshev.theta (A : ℝ) = 0 := by
      interval_cases A <;> simp
    have hθB : |Chebyshev.theta (B : ℝ) - (B : ℝ)| ≤ err := hθ B B hBr le_rfl
    have hthetaB : (B : ℝ) - err ≤ Chebyshev.theta (B : ℝ) := by
      linarith only [(abs_le.mp hθB).1]
    have hsum := sum_log_primeBin_eq hAB
    rw [hthetaA, sub_zero] at hsum
    have hcard : (B : ℝ) - err ≤ ((primeBin A B).card : ℝ) * Real.log B := by
      rw [hsum] at hlog
      exact hthetaB.trans hlog
    have hAr : (0 : ℝ) ≤ (A : ℝ) := by positivity
    have herr_eq : primeBinSupplyError (2 * c) B = 2 * err := by
      unfold primeBinSupplyError err
      ring
    rw [herr_eq]
    linarith only [hcard, hAr, herr_nonneg]
  · -- The lower endpoint is at least `2`: this is the original estimate.
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
    have hAerr : |Chebyshev.theta (A : ℝ) - (A : ℝ)| ≤ err :=
      (hθ B A hAr hABr).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hABr)
          (mul_nonneg hc (sq_nonneg _)))
    have hBerr : |Chebyshev.theta (B : ℝ) - (B : ℝ)| ≤ err := hθ B B hBr le_rfl
    have hθbin : (B : ℝ) - (A : ℝ) - 2 * err ≤
        Chebyshev.theta (B : ℝ) - Chebyshev.theta (A : ℝ) := by
      linarith only [(abs_le.mp hAerr).2, (abs_le.mp hBerr).1]
    have hsum := sum_log_primeBin_eq hAB
    have hcard : (B : ℝ) - (A : ℝ) - 2 * err ≤
        ((primeBin A B).card : ℝ) * Real.log B := by
      rw [hsum] at hlog
      exact hθbin.trans hlog
    have herr_eq : primeBinSupplyError (2 * c) B = 2 * err := by
      unfold primeBinSupplyError err
      ring
    rwa [herr_eq]

/-! ## 3. The width core for nonempty bins -/

omit [DecidableEq ι] in
/-- **The width condition implies the per-bin cardinality input on nonempty
bins.**  This is `primeBinEnvelopeDecayCore_of_width` with the endpoint
hypotheses `2 ≤ A i` and `A i ≤ B i` replaced by the nonemptiness of the actual
prime bins. -/
theorem primeBinEnvelopeDecayCore_of_width_nonempty
    {K Ks c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ}
    (hsupply : ∀ A B : ℕ, A ≤ B → (primeBin A B).Nonempty →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B)
    (hcard : 0 < Fintype.card ι)
    (hne : ∀ i, (primeBin (A i) (B i)).Nonempty)
    (hwidth : PrimeBinEnvelopeWidthCore K Ks c q A B n) :
    PrimeBinEnvelopeDecayCore K c q A B n := by
  intro i
  have hm : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hlog : 0 < Real.log (B i : ℝ) := by
    apply Real.log_pos
    exact_mod_cast one_lt_of_primeBin_nonempty (hne i)
  have hs := hsupply (A i) (B i)
    (le_of_lt (lt_of_primeBin_nonempty (hne i))) (hne i)
  have hw := hwidth i
  have hle :
      Real.exp (decayExponent c n / (Fintype.card ι)) *
          primeBinEnvelopeFactor K q (B i) * Real.log (B i) ≤
        ((primeBin (A i) (B i)).card : ℝ) * Real.log (B i) := by
    linarith only [hs, hw]
  have hdiv :
      Real.exp (decayExponent c n / (Fintype.card ι)) *
          primeBinEnvelopeFactor K q (B i) ≤
        ((primeBin (A i) (B i)).card : ℝ) := by
    have h' : Real.exp (decayExponent c n / (Fintype.card ι)) *
        primeBinEnvelopeFactor K q (B i) ≤
        (((primeBin (A i) (B i)).card : ℝ) * Real.log (B i)) /
          Real.log (B i) := by
      rw [le_div_iff₀ hlog]
      exact hle
    rwa [mul_div_cancel_right₀ _ hlog.ne'] at h'
  have hpos : 0 < Real.exp (-(decayExponent c n / (Fintype.card ι))) :=
    Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hdiv hpos.le
  have hsimp :
      Real.exp (-(decayExponent c n / (Fintype.card ι))) *
          (Real.exp (decayExponent c n / (Fintype.card ι)) *
            primeBinEnvelopeFactor K q (B i)) =
        primeBinEnvelopeFactor K q (B i) := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rwa [hsimp] at hmul

/-- **Prime-bin character decay from the GRH supply count, the width condition,
and nonemptiness of the bins.** -/
theorem primeBinCharacterDecay_of_width_nonempty
    {K Ks c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ}
    (hK : 0 ≤ K)
    (hsupply : ∀ A B : ℕ, A ≤ B → (primeBin A B).Nonempty →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < Fintype.card ι)
    (hne : ∀ i, (primeBin (A i) (B i)).Nonempty)
    (hwidth : PrimeBinEnvelopeWidthCore K Ks c q A B n) :
    PrimeBinCharacterDecay K c q A B n :=
  primeBinCharacterDecay_of_core hK hdisj hcard
    (primeBinEnvelopeDecayCore_of_width_nonempty hsupply hcard hne hwidth)

/-! ## 4. The reduction from the critical line -/

/-- **`PrimeBinCharacterDecay` from GRH and the width condition, assuming only
that every prime bin is nonempty.**  The constant `Ks` is extracted from
`primeBin_supply_nonempty_from_critical_line`; there is no lower-endpoint
hypothesis. -/
theorem primeBinCharacterDecay_of_criticalLine_nonempty
    (line : DirichletLZerosOnLine) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧
      ∀ {K c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ},
        (hK : 0 ≤ K) →
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hcard : 0 < Fintype.card ι) →
        (hne : ∀ i, (primeBin (A i) (B i)).Nonempty) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        PrimeBinCharacterDecay K c q A B n := by
  obtain ⟨Ks, hKs, hsupply⟩ := primeBin_supply_nonempty_from_critical_line line
  refine ⟨Ks, hKs, ?_⟩
  intro K c q A B n hK hdisj hcard hne hwidth
  exact primeBinCharacterDecay_of_width_nonempty hK hsupply hdisj hcard hne hwidth

/-- **The nonempty-bin decay composed with the GRH product estimate.**  The
character product bound `primeBin_product_from_critical_line` supplies `K`, the
nonempty-bin decay supplies the normalising factor, and `A i ≤ B i` is derived
from nonemptiness instead of assumed.  (The lower endpoint hypothesis
`2 ≤ A i` remains because the product estimate is stated for sharp bins starting
at two.) -/
theorem primeBinTwist_le_of_criticalLine_nonempty
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {c : ℝ} {A B : ι → ℕ} {n : ℕ},
        (hA : ∀ i, 2 ≤ A i) →
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hcard : 0 < Fintype.card ι) →
        (hne : ∀ i, (primeBin (A i) (B i)).Nonempty) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          Real.exp (-(decayExponent c n)) *
            ((primeBinProducts A B).card : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    primeBinProducts_twist_le (primeBin_product_from_critical_line line)
  obtain ⟨Ks, hKs, hdecay⟩ :=
    primeBinCharacterDecay_of_criticalLine_nonempty (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ χ hχ c A B n hA hdisj hcard hne hwidth
  have hAB : ∀ i, A i ≤ B i :=
    fun i => le_of_lt (lt_of_primeBin_nonempty (hne i))
  have hdec := hdecay hK hdisj hcard hne hwidth
  unfold PrimeBinCharacterDecay at hdec
  simpa [decayExponent] using
    (hbound q χ hχ A B hA hAB hdisj).trans hdec

/-! ## 5. Nonemptiness is exactly what the decay forces -/

/-- **The decay forces every bin to be nonempty.**  For `K > 0` and positive
upper endpoints the GRH envelope is strictly positive.  If the decay holds, the
right-hand side is positive as well, so the product set has positive
cardinality; since its cardinality is at most the product of the bin
cardinalities, every bin contains a prime.

Together with `primeBinCharacterDecay_false_of_emptyBin`, this identifies
nonemptiness as the support-theoretic necessary condition for the decay.  It is
not sufficient on its own: a narrow nonempty bin can still have too few primes,
which is exactly the quantitative content of `PrimeBinEnvelopeWidthCore`.
-/
theorem primeBin_nonempty_of_characterDecay
    {K c : ℝ} {q n : ℕ} {A B : ι → ℕ}
    (hK : 0 < K) (hB : ∀ i, 0 < B i)
    (h : PrimeBinCharacterDecay K c q A B n) :
    ∀ i, (primeBin (A i) (B i)).Nonempty := by
  have hfac : ∀ i, 0 < primeBinEnvelopeFactor K q (B i) := by
    intro i
    unfold primeBinEnvelopeFactor
    have hqlog : 0 ≤ Real.log (3 * (q : ℝ) * (B i : ℝ)) := by
      rcases Nat.eq_zero_or_pos q with hq | hq
      · subst q
        simp
      · have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hB1 : (1 : ℝ) ≤ (B i : ℝ) := by exact_mod_cast hB i
        have hx : (1 : ℝ) ≤ 3 * (q : ℝ) * (B i : ℝ) := by nlinarith
        exact Real.log_nonneg hx
    have hlog : 0 < 1 + Real.log (3 * (q : ℝ) * (B i : ℝ)) := by linarith
    have hsqrt : 0 < Real.sqrt (B i : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast hB i)
    have h2K : 0 < 2 * K := mul_pos (by norm_num) hK
    have hsq : 0 < (1 + Real.log (3 * (q : ℝ) * (B i : ℝ))) ^ 2 :=
      sq_pos_of_pos hlog
    exact mul_pos (mul_pos h2K hsq) hsqrt
  have henv : 0 < primeBinRelativeEnvelope K q A B := by
    rw [primeBinRelativeEnvelope_eq_prod]
    exact Finset.prod_pos (fun i _ => hfac i)
  have hcardpos : 0 < (primeBinProducts A B).card := by
    have hrhs : 0 < Real.exp (-c * paperD n * scale n) *
        ((primeBinProducts A B).card : ℝ) := lt_of_lt_of_le henv h
    by_contra hc
    have hc0 : (primeBinProducts A B).card = 0 := Nat.eq_zero_of_not_pos hc
    rw [hc0] at hrhs
    norm_num at hrhs
  have hle : (primeBinProducts A B).card ≤
      ∏ i, (primeBin (A i) (B i)).card := by
    rw [primeBinProducts]
    calc
      (Finset.image (fun p : ι → ℕ => ∏ i, p i)
          (Fintype.piFinset (fun i => primeBin (A i) (B i)))).card
          ≤ (Fintype.piFinset (fun i => primeBin (A i) (B i))).card :=
        Finset.card_image_le
      _ = ∏ i, (primeBin (A i) (B i)).card :=
        Fintype.card_piFinset (fun i => primeBin (A i) (B i))
  intro i
  by_contra hni
  have hc0 : (primeBin (A i) (B i)).card = 0 :=
    Nat.eq_zero_of_not_pos (fun hpos => hni (Finset.card_pos.mp hpos))
  have hprod0 : (∏ j, (primeBin (A j) (B j)).card) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hc0
  have hzero : (primeBinProducts A B).card = 0 := by
    have := hle.trans_eq hprod0
    exact le_antisymm this (Nat.zero_le _)
  omega

/-! ## Axiom audit -/

#print axioms two_le_of_primeBin_nonempty
#print axioms lt_of_primeBin_nonempty
#print axioms one_lt_of_primeBin_nonempty
#print axioms card_pos_of_primeBin_nonempty
#print axioms primeBin_subset_of_le
#print axioms sum_log_primeBin_eq
#print axioms primeBin_supply_nonempty_from_critical_line
#print axioms primeBinEnvelopeDecayCore_of_width_nonempty
#print axioms primeBinCharacterDecay_of_width_nonempty
#print axioms primeBinCharacterDecay_of_criticalLine_nonempty
#print axioms primeBinTwist_le_of_criticalLine_nonempty
#print axioms primeBin_nonempty_of_characterDecay

end

end Cogentic.RandomizedL20_2DecayNonempty
