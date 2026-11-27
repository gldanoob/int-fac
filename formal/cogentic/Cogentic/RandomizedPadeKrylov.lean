import Cogentic.RandomizedPadeSolver
import Cogentic.RandomizedKrylovProbe

open scoped Polynomial

namespace Cogentic.RandomizedPadeRecurrence

open Polynomial RandomizedKrylovProbe

variable {K I : Type*} [Field K] [DecidableEq K] [Fintype K] [Fintype I] [DecidableEq I]

/-- Given a degree bound on the vector annihilator and a probe that sees every
factor test, the Euclidean solver on the first 2n moments returns that vector
annihilator. -/
theorem euclideanRecurrence_eq_of_good_krylov_probe
    (M : Module.End K (I → K)) (v u : I → K) (p : K[X]) (n : ℕ)
    (hp : p.Monic) (hpn : p.natDegree ≤ n) (hpann : (aeval M p) v = 0)
    (hprobe : u ∉ missedFactorProbes M v p) :
    euclideanRecurrence n (fun j => dotProbe u ((M ^ j) v)) = p := by
  let a := fun j : ℕ => dotProbe u ((M ^ j) v)
  have hpfit : FitsTruncatedRecurrence (2 * n) p.natDegree a p := by
    intro j _
    exact (shift_probe_eq_sum M v (dotProbe u) p j).symm.trans
      (probe_annihilates_of_vector M v (dotProbe u) p hpann (X ^ j))
  obtain ⟨hg, hgn, hgfit, hgmin⟩ := euclideanRecurrence_spec n a p hp hpn hpfit
  refine minimal_projected_eq_of_good_probe_finite M v u p _ n hp hg hpn hgn hpann hprobe
    (fits_first_n_of_truncated n _ a _ hgn rfl hgfit) ?_
  intro q hq hqn hqfit
  have hqann := probe_annihilates_of_prefix M v (dotProbe u) p q hp hpann (fun j hj => by
    rw [shift_probe_eq_sum]
    exact hqfit j (hj.trans_le hpn))
  let c := q.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hq)
  have hdeg : (q * C c).natDegree = q.natDegree := natDegree_mul_C hc
  have hfit : FitsTruncatedRecurrence (2 * n) (q * C c).natDegree a (q * C c) := by
    intro j _
    rw [← shift_probe_eq_sum M v (dotProbe u) (q * C c) j]
    rw [show X ^ j * (q * C c) = (X ^ j * C c) * q by ac_rfl]
    exact hqann _
  have hmin := hgmin (q * C c) (monic_mul_leadingCoeff_inv hq) (hdeg.trans_le hqn) hfit
  exact hmin.trans_eq hdeg

/-- For a minimal vector annihilator, the fraction of left probes on which the
Euclidean solver can fail is at most the degree divided by the field size. -/
theorem card_bad_euclidean_krylov_probes [Nonempty I]
    (M : Module.End K (I → K)) (v : I → K) (p : K[X]) (n : ℕ)
    (hp : p.Monic) (hpn : p.natDegree ≤ n) (hpann : (aeval M p) v = 0)
    (minimal : ∀ q : K[X], q ≠ 0 → (aeval M q) v = 0 → p.natDegree ≤ q.natDegree) :
    (Finset.univ.filter (fun u : I → K =>
      euclideanRecurrence n (fun j => dotProbe u ((M ^ j) v)) ≠ p)).card *
      Fintype.card K ≤ p.natDegree * Fintype.card (I → K) := by
  apply le_trans _ (card_missed_factor_probes M v p hp minimal)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro u hu
  by_contra hnot
  exact (Finset.mem_filter.mp hu).2
    (euclideanRecurrence_eq_of_good_krylov_probe M v u p n hp hpn hpann hnot)

#print axioms euclideanRecurrence_eq_of_good_krylov_probe
#print axioms card_bad_euclidean_krylov_probes

end Cogentic.RandomizedPadeRecurrence
