import Cogentic.RandomizedPadeNormalize
import Cogentic.RandomizedPadeRecurrence

open scoped Polynomial

namespace Cogentic.RandomizedPadeRecurrence

open Polynomial

variable {K : Type*} [Field K]

/-- The smallest length obeying both degree bounds of a fixed Padé pair. -/
noncomputable def padeLength (B R : K[X]) : ℕ := by
  classical
  exact max B.natDegree (if R = 0 then 0 else R.natDegree + 1)

theorem padeLength_le_iff (B R : K[X]) (l : ℕ) :
    padeLength B R ≤ l ↔ B.natDegree ≤ l ∧ R.degree < l := by
  classical
  by_cases hR : R = 0
  · simp [padeLength, hR]
  · simp only [padeLength, if_neg hR, max_le_iff]
    rw [Nat.succ_le_iff, natDegree_lt_iff_degree_lt hR]

/-- A coprime normalized pair determines a monic fitting recurrence of minimum
length. Every competing Padé pair of length at most n is a polynomial multiple
of this pair. -/
theorem minimal_recurrence_of_normalized_pade
    (n : ℕ) (a : ℕ → K) (B R : K[X])
    (hcop : IsCoprime B R) (hB0 : B.eval 0 = 1)
    (hB : B.degree ≤ n) (hR : R.degree < n)
    (hcong : X ^ (2 * n) ∣ B * truncatedMoments (2 * n) a - R) :
    let l := padeLength B R
    l ≤ n ∧ (B.reflect l).Monic ∧ (B.reflect l).natDegree = l ∧
      FitsTruncatedRecurrence (2 * n) l a (B.reflect l) ∧
      ∀ p : K[X], p.Monic → p.natDegree ≤ n →
        FitsTruncatedRecurrence (2 * n) p.natDegree a p → l ≤ p.natDegree := by
  have hl := (padeLength_le_iff B R n).mpr ⟨natDegree_le_iff_degree_le.mpr hB, hR⟩
  obtain ⟨hBl, hRl⟩ := (padeLength_le_iff B R (padeLength B R)).mp le_rfl
  have hB0' : B.coeff 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hB0
  obtain ⟨hm, hd, hfits⟩ := recurrence_of_pade_congruence n (padeLength B R) a
    B R hl hBl hB0' hcong hRl
  refine ⟨hl, hm, hd, hfits, ?_⟩
  intro p hp hpn hpfit
  obtain ⟨B', R', hB'0, hB', _, _, hR', hcong'⟩ :=
    exists_pade_of_recurrence n p.natDegree a p hp rfl hpfit
  have hB'nz : B' ≠ 0 := by
    intro hz
    simp [hz] at hB'0
  obtain ⟨g, hg, hBg, hRg⟩ := Randomized.pade_exists_mul_of_normalized
    hcop hB0 hB'nz (natDegree_le_iff_degree_le.mp (hB'.trans hpn)) hB
    (hR'.trans_le (WithBot.coe_le_coe.mpr hpn)) hR hcong' hcong
  apply (padeLength_le_iff B R p.natDegree).mpr
  have hBdeg : B.degree ≤ B'.degree := by
    rw [hBg, mul_comm]
    exact degree_le_mul_left B hg
  have hRdeg : R.degree ≤ R'.degree := by
    rw [hRg, mul_comm]
    exact degree_le_mul_left R hg
  exact ⟨natDegree_le_iff_degree_le.mpr (hBdeg.trans (natDegree_le_iff_degree_le.mp hB')),
    hRdeg.trans_lt hR'⟩

/-- Any fitting monic recurrence of length at most n produces a normalized
Padé pair and hence a monic fitting recurrence of minimum length. -/
theorem exists_minimal_recurrence_of_recurrence
    (n : ℕ) (a : ℕ → K) (p : K[X])
    (hp : p.Monic) (hpn : p.natDegree ≤ n)
    (hpfit : FitsTruncatedRecurrence (2 * n) p.natDegree a p) :
    ∃ B R : K[X], IsCoprime B R ∧ B.eval 0 = 1 ∧
      (X ^ (2 * n) ∣ B * truncatedMoments (2 * n) a - R) ∧
      let l := padeLength B R
      l ≤ n ∧ (B.reflect l).Monic ∧ (B.reflect l).natDegree = l ∧
        FitsTruncatedRecurrence (2 * n) l a (B.reflect l) ∧
        ∀ p' : K[X], p'.Monic → p'.natDegree ≤ n →
          FitsTruncatedRecurrence (2 * n) p'.natDegree a p' → l ≤ p'.natDegree := by
  classical
  obtain ⟨B, R, hB0, hB, _, _, hR, hdvd⟩ :=
    exists_pade_of_recurrence n p.natDegree a p hp rfl hpfit
  have hB0' : B.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, hB0]
    exact one_ne_zero
  obtain ⟨_, B₀, R₀, _, _, _, hcop, hB₀0, hB₀, hR₀, hdvd₀⟩ :=
    Randomized.pade_exists_normalized hB0' (natDegree_le_iff_degree_le.mp (hB.trans hpn))
      (hR.trans_le (WithBot.coe_le_coe.mpr hpn)) hdvd
  exact ⟨B₀, R₀, hcop, hB₀0, hdvd₀,
    minimal_recurrence_of_normalized_pade n a B₀ R₀ hcop hB₀0 hB₀ hR₀ hdvd₀⟩

#print axioms padeLength_le_iff
#print axioms minimal_recurrence_of_normalized_pade
#print axioms exists_minimal_recurrence_of_recurrence

end Cogentic.RandomizedPadeRecurrence
