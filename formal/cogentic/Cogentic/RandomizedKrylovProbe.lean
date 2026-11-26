import Cogentic.RandomizedProbeCount
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Irreducible-factor tests for a projected Krylov sequence. -/

namespace Cogentic.RandomizedKrylovProbe

open Polynomial UniqueFactorizationMonoid

section Polynomial

variable {K V : Type*} [Field K] [DecidableEq K] [AddCommGroup V] [Module K V]

/-- A projected recurrence annihilates all polynomial shifts of the vector. -/
def ProbeAnnihilates (M : Module.End K V) (v : V) (probe : V →ₗ[K] K) (g : K[X]) : Prop :=
  ∀ r : K[X], probe ((aeval M (r * g)) v) = 0

omit [DecidableEq K] in
/-- The vector annihilator also annihilates the projected sequence. -/
theorem probe_annihilates_of_vector (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (p : K[X]) (hp : (aeval M p) v = 0) : ProbeAnnihilates M v probe p := by
  intro r
  rw [map_mul]
  change probe ((aeval M r) ((aeval M p) v)) = 0
  rw [hp, map_zero, map_zero]

/-- To verify a projected recurrence, it suffices to test the shifts below the
    degree of any monic vector annihilator. -/
theorem probe_annihilates_of_prefix (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (p g : K[X]) (hp : p.Monic) (hpann : (aeval M p) v = 0)
    (hfinite : ∀ j : ℕ, j < p.natDegree → probe ((aeval M (X ^ j * g)) v) = 0) :
    ProbeAnnihilates M v probe g := by
  by_cases hp1 : p = 1
  · have hv : v = 0 := by simpa [hp1] using hpann
    intro r
    simp [hv]
  have hsmall : ∀ s : K[X], s.natDegree < p.natDegree → probe ((aeval M (s * g)) v) = 0 := by
    intro s hs
    conv_lhs => rw [s.as_sum_range_C_mul_X_pow' hs]
    simp only [Finset.sum_mul, map_sum, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [mul_assoc, map_mul, aeval_C]
    change probe (s.coeff j • ((aeval M (X ^ j * g)) v)) = 0
    rw [map_smul, hfinite j (Finset.mem_range.mp hj), smul_zero]
  have hall := probe_annihilates_of_vector M v probe p hpann
  intro r
  conv_lhs => rw [← modByMonic_add_div r p]
  rw [add_mul, map_add, LinearMap.add_apply, map_add,
    hsmall _ (natDegree_modByMonic_lt r hp hp1),
    show (p * (r /ₘ p)) * g = ((r /ₘ p) * g) * p by ac_rfl,
    hall _, add_zero]

omit [DecidableEq K] in
/-- A polynomial shift is the corresponding scalar moment recurrence. -/
theorem shift_probe_eq_sum (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (g : K[X]) (j : ℕ) :
    probe ((aeval M (X ^ j * g)) v) =
      ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * probe ((M ^ (j + i)) v) := by
  have hpoly : X ^ j * g =
      ∑ i ∈ Finset.range (g.natDegree + 1), C (g.coeff i) * X ^ (j + i) := by
    conv_lhs => rw [g.as_sum_range_C_mul_X_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ac_rfl
  rw [hpoly]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, aeval_C]
  change probe (g.coeff i • ((aeval M (X ^ (j + i))) v)) = _
  simp [map_smul, aeval_X_pow, smul_eq_mul]

/-- The first n shifted equations for a projected Krylov recurrence. For
    degree at most n, these equations use only the first 2n scalar moments. -/
def KrylovRecurrenceFits (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (n : ℕ) (g : K[X]) : Prop :=
  ∀ j < n, ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * probe ((M ^ (j + i)) v) = 0

/-- A least-degree monic projected recurrence divides any projected annihilator. -/
theorem minimal_probe_dvd (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (p g : K[X]) (hg : g.Monic) (hpann : ProbeAnnihilates M v probe p)
    (hgann : ProbeAnnihilates M v probe g)
    (minimal : ∀ r : K[X], r ≠ 0 → ProbeAnnihilates M v probe r → g.natDegree ≤ r.natDegree) :
    g ∣ p := by
  by_cases hg1 : g = 1
  · simp [hg1]
  apply (modByMonic_eq_zero_iff_dvd hg).mp
  by_contra hrem
  have hremann : ProbeAnnihilates M v probe (p %ₘ g) := by
    intro r
    rw [modByMonic_eq_sub_mul_div, mul_sub, map_sub, LinearMap.sub_apply, map_sub]
    rw [hpann r, show r * (g * (p /ₘ g)) = (r * (p /ₘ g)) * g by ac_rfl,
      hgann (r * (p /ₘ g)), sub_self]
  exact (not_le_of_gt (natDegree_modByMonic_lt p hg hg1)) (minimal _ hrem hremann)

/-- Testing p divided by each distinct irreducible factor excludes every proper
    monic divisor that could annihilate the projected sequence. -/
theorem eq_of_factor_probes (M : Module.End K V) (v : V) (probe : V →ₗ[K] K)
    (p g : K[X]) (hp : p.Monic) (hg : g.Monic) (hdvd : g ∣ p)
    (hann : ProbeAnnihilates M v probe g)
    (detect : ∀ f ∈ normalizedFactors p, probe ((aeval M (p /ₘ f)) v) ≠ 0) :
    g = p := by
  obtain ⟨d, hd⟩ := hdvd
  have hdm : d.Monic := hg.of_mul_monic_left (hd ▸ hp)
  by_contra hne
  have hdu : ¬IsUnit d := by
    intro h
    exact hne (by simpa [hdm.eq_one_of_isUnit h] using hd.symm)
  obtain ⟨f, hf⟩ := exists_mem_normalizedFactors hdm.ne_zero hdu
  have hfp : f ∈ normalizedFactors p := by
    rw [hd, normalizedFactors_mul hg.ne_zero hdm.ne_zero]
    exact Multiset.mem_add.mpr (Or.inr hf)
  obtain ⟨r, hdr⟩ := dvd_of_mem_normalizedFactors hf
  have hfm := ((Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hfp).2.1
  have hquot : p /ₘ f = r * g := by
    have hprod : p = f * (r * g) := by rw [hd, hdr]; ac_rfl
    rw [hprod, mul_divByMonic_cancel_left _ hfm]
  exact detect f hfp (hquot ▸ hann r)

/-- Minimality of a vector annihilator makes every factor test a nonzero vector. -/
theorem factor_action_ne_zero (M : Module.End K V) (v : V) (p f : K[X])
    (hp : p.Monic) (hf : f ∈ normalizedFactors p)
    (minimal : ∀ r : K[X], r ≠ 0 → (aeval M r) v = 0 → p.natDegree ≤ r.natDegree) :
    (aeval M (p /ₘ f)) v ≠ 0 := by
  have hfactor := (Polynomial.mem_normalizedFactors_iff hp.ne_zero).mp hf
  obtain ⟨q, hq⟩ := hfactor.2.2
  have hq0 : q ≠ 0 := by
    intro hz
    exact hp.ne_zero (by simp [hq, hz])
  intro hz
  rw [hq, mul_divByMonic_cancel_left _ hfactor.2.1] at hz
  have hdeg := minimal q hq0 hz
  rw [hq, natDegree_mul hfactor.1.ne_zero hq0] at hdeg
  have := hfactor.1.natDegree_pos
  omega

omit [DecidableEq K] in
private theorem card_le_sum_natDegree (s : Multiset K[X])
    (h : ∀ f ∈ s, 0 < f.natDegree) :
    s.card ≤ (s.map natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons f s ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have hf := h f (Multiset.mem_cons_self f s)
    have hs := ih (fun g hg => h g (Multiset.mem_cons_of_mem hg))
    omega

/-- There are at most degree-many distinct irreducible tests. -/
theorem card_factor_tests_le_degree (p : K[X]) (hp : p.Monic) :
    (normalizedFactors p).toFinset.card ≤ p.natDegree := by
  have hprod : (normalizedFactors p).prod = p := by
    simpa [hp.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors p
  calc
    (normalizedFactors p).toFinset.card ≤ (normalizedFactors p).card :=
      Multiset.toFinset_card_le _
    _ ≤ ((normalizedFactors p).map natDegree).sum :=
      card_le_sum_natDegree _ (fun f hf => (irreducible_of_normalized_factor f hf).natDegree_pos)
    _ = p.natDegree := by
      rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors _), hprod]

end Polynomial

section Counting

variable {K I : Type*} [Field K] [DecidableEq K] [Fintype K] [Fintype I] [DecidableEq I]

/-- The finite set of probes that miss at least one irreducible-factor test. -/
noncomputable def missedFactorProbes (M : Module.End K (I → K)) (v : I → K) (p : K[X]) :
    Finset (I → K) :=
  (normalizedFactors p).toFinset.biUnion fun f =>
    Finset.univ.filter fun u => ((aeval M (p /ₘ f)) v) ⬝ᵥ u = 0

/-- The count of unsuccessful probes is at most the degree divided by the field size
    times the full sample count, expressed without division. -/
theorem card_missed_factor_probes [Nonempty I]
    (M : Module.End K (I → K)) (v : I → K) (p : K[X]) (hp : p.Monic)
    (minimal : ∀ r : K[X], r ≠ 0 → (aeval M r) v = 0 → p.natDegree ≤ r.natDegree) :
    (missedFactorProbes M v p).card * Fintype.card K ≤
      p.natDegree * Fintype.card (I → K) := by
  have hcount := Cogentic.RandomizedProbeCount.card_bad_probe_union_mul_field_le
    (normalizedFactors p).toFinset (fun f => (aeval M (p /ₘ f)) v)
    (fun f hf => factor_action_ne_zero M v p f hp (Multiset.mem_toFinset.mp hf) minimal)
  exact hcount.trans (Nat.mul_le_mul_right _ (card_factor_tests_le_degree p hp))

/-- The linear functional supplied by a scalar probe vector. -/
def dotProbe (u : I → K) : (I → K) →ₗ[K] K where
  toFun w := w ⬝ᵥ u
  map_add' a b := add_dotProduct a b u
  map_smul' c w := smul_dotProduct c w u

/-- Any probe outside the missed-test set recovers the full vector polynomial
    as its least-degree monic projected recurrence. -/
theorem minimal_projected_eq_of_good_probe
    (M : Module.End K (I → K)) (v u : I → K) (p g : K[X]) (hp : p.Monic)
    (hg : g.Monic) (hpann : (aeval M p) v = 0) (hu : u ∉ missedFactorProbes M v p)
    (hgann : ∀ r : K[X], ((aeval M (r * g)) v) ⬝ᵥ u = 0)
    (minimal : ∀ q : K[X], q ≠ 0 →
      (∀ r : K[X], ((aeval M (r * q)) v) ⬝ᵥ u = 0) → g.natDegree ≤ q.natDegree) :
    g = p := by
  have hdvd := minimal_probe_dvd M v (dotProbe u) p g hg
    (probe_annihilates_of_vector M v (dotProbe u) p hpann) hgann minimal
  refine eq_of_factor_probes M v (dotProbe u) p g hp hg hdvd hgann ?_
  intro f hf hzero
  exact hu (Finset.mem_biUnion.mpr ⟨f, Multiset.mem_toFinset.mpr hf,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩⟩)

/-- Outside the missed-test set, a least-degree monic recurrence of degree at
    most n selected from the first 2n moments equals the vector polynomial. -/
theorem minimal_projected_eq_of_good_probe_finite
    (M : Module.End K (I → K)) (v u : I → K) (p g : K[X]) (n : ℕ)
    (hp : p.Monic) (hg : g.Monic) (hpdeg : p.natDegree ≤ n) (hgdeg : g.natDegree ≤ n)
    (hpann : (aeval M p) v = 0) (hu : u ∉ missedFactorProbes M v p)
    (fit : KrylovRecurrenceFits M v (dotProbe u) n g)
    (minimal : ∀ q : K[X], q ≠ 0 → q.natDegree ≤ n →
      KrylovRecurrenceFits M v (dotProbe u) n q → g.natDegree ≤ q.natDegree) :
    g = p := by
  have hann : ProbeAnnihilates M v (dotProbe u) g :=
    probe_annihilates_of_prefix M v (dotProbe u) p g hp hpann (fun j hj => by
      rw [shift_probe_eq_sum]
      exact fit j (lt_of_lt_of_le hj hpdeg))
  apply minimal_projected_eq_of_good_probe M v u p g hp hg hpann hu hann
  intro q hq hqann
  by_cases hqdeg : q.natDegree ≤ n
  · apply minimal q hq hqdeg
    intro j _
    rw [← shift_probe_eq_sum]
    exact hqann (X ^ j)
  · exact hgdeg.trans (Nat.le_of_lt (Nat.lt_of_not_ge hqdeg))

end Counting

#print axioms minimal_probe_dvd
#print axioms probe_annihilates_of_prefix
#print axioms shift_probe_eq_sum
#print axioms eq_of_factor_probes
#print axioms factor_action_ne_zero
#print axioms card_factor_tests_le_degree
#print axioms card_missed_factor_probes
#print axioms minimal_projected_eq_of_good_probe
#print axioms minimal_projected_eq_of_good_probe_finite

end Cogentic.RandomizedKrylovProbe
