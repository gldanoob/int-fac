import Cogentic.RandomizedPadeEuclid
import Cogentic.RandomizedPadeMinimal
import Cogentic.RandomizedPadeOutput

namespace Cogentic.RandomizedPadeRecurrence

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
theorem degree_truncatedMoments_lt (m : ℕ) (a : ℕ → K) :
    (truncatedMoments m a).degree < (m : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  simp [coeff_truncatedMoments, not_lt.mpr hi]

/-- Normalized Euclidean recurrence obtained solely from the first 2n moments. -/
noncomputable def euclideanRecurrence (n : ℕ) (a : ℕ → K) : K[X] :=
  let state := (Randomized.PadeEuclid.solve (truncatedMoments (2*n) a) n
    (degree_truncatedMoments_lt (2*n) a)).val
  let pair := Randomized.padeNormalize state.coefficient state.remainder
  pair.1.reflect (padeLength pair.1 pair.2)

/-- When any monic recurrence of length ≤n fits, the actual Euclidean output
is monic and fits with least possible length among all bounded candidates. -/
theorem euclideanRecurrence_spec (n : ℕ) (a : ℕ → K) (p : K[X])
    (hp : p.Monic) (hpn : p.natDegree ≤ n)
    (hpfit : FitsTruncatedRecurrence (2*n) p.natDegree a p) :
    let g := euclideanRecurrence n a
    g.Monic ∧ g.natDegree ≤ n ∧ FitsTruncatedRecurrence (2*n) g.natDegree a g ∧
      ∀ q : K[X], q.Monic → q.natDegree ≤ n →
        FitsTruncatedRecurrence (2*n) q.natDegree a q → g.natDegree ≤ q.natDegree := by
  obtain ⟨B,R,hcop,hunit,hcong,hmin⟩ :=
    exists_minimal_recurrence_of_recurrence n a p hp hpn hpfit
  let A := truncatedMoments (2*n) a
  let hA := degree_truncatedMoments_lt (2*n) a
  let state := (Randomized.PadeEuclid.solve A n hA).val
  have hs : state.coefficient ≠ 0 ∧ state.coefficient.natDegree ≤ n ∧
      state.remainder.degree < (n : WithBot ℕ) ∧ X^(2*n) ∣ state.coefficient*A-state.remainder :=
    Randomized.PadeEuclid.solve_spec A n hA
  obtain ⟨hlen,hmon,hdegree,hfits,hleast⟩ := hmin
  obtain ⟨hB,hR⟩ := (padeLength_le_iff B R n).mp hlen
  have he := Randomized.padeNormalize_eq_of_valid hcop hunit hs.1
    (natDegree_le_iff_degree_le.mp hs.2.1) (natDegree_le_iff_degree_le.mp hB)
    hs.2.2.1 hR hs.2.2.2 hcong
  have heq : euclideanRecurrence n a = B.reflect (padeLength B R) := by
    unfold euclideanRecurrence
    change (Randomized.padeNormalize state.coefficient state.remainder).1.reflect _ = _
    rw [he]
  dsimp only
  rw [heq,hdegree]
  exact ⟨hmon,hlen,hfits,hleast⟩

#print axioms euclideanRecurrence_spec

end Cogentic.RandomizedPadeRecurrence
