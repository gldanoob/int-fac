import Cogentic.Extraction
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Ideal.Int

/-! Finite valuations of squarefree affine marks, using a local Taylor expansion. -/

open NumberField Polynomial
open scoped BigOperators NumberField Polynomial
namespace Cogentic
variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

private theorem local_eval_cast (v : Valuation K Γ) (f : ℤ[X]) (x : v.integer) :
    (((f.map (Int.castRingHom v.integer)).eval x : v.integer) : K) =
      f.eval₂ (Int.castRingHom K) (x : K) := by
  rw [Polynomial.eval_map]
  have eq : v.integer.subtype.comp (Int.castRingHom v.integer) = Int.castRingHom K := Subsingleton.elim _ _
  simpa only [eq, Subring.subtype_apply] using f.hom_eval₂ (Int.castRingHom v.integer) v.integer.subtype x

private theorem int_local_bound (v : Valuation K Γ) (a : ℤ) : v (a : K) ≤ 1 :=
  show v (((a : v.integer) : K)) ≤ 1 from (a : v.integer).property

/-- When the polynomial value is a unit, the mark has just the common pole offset. -/
theorem affine_valuation_of_unit_value (v : Valuation K Γ) (f : ℤ[X]) (θ : K) (a : ℤ)
    (hroot : f.eval₂ (Int.castRingHom K) θ = 0)
    (hvalue : v ((f.eval a : ℤ) : K) = 1) :
    v ((a : K) - θ) = max 1 (v θ) := by
  by_cases hθ : v θ ≤ 1
  · rw [max_eq_left hθ]
    let t : v.integer := ⟨θ, hθ⟩
    let F := f.map (Int.castRingHom v.integer)
    have ht : F.eval t = 0 := Subtype.coe_injective (by
      change ((F.eval t : v.integer) : K) = 0
      rwa [local_eval_cast])
    have dvd := Polynomial.sub_dvd_eval_sub (a : v.integer) t F
    rw [ht, sub_zero] at dvd
    have hle := (Valuation.integer.integers v).le_of_dvd dvd
    change v ((F.eval (a : v.integer) : v.integer) : K) ≤ v ((a : K) - θ) at hle
    rw [local_eval_cast (v := v)] at hle
    change v (f.eval₂ (Int.castRingHom K) (Int.castRingHom K a)) ≤ _ at hle
    rw [Polynomial.eval₂_at_apply, Int.coe_castRingHom, hvalue] at hle
    exact le_antisymm (v.map_sub_le (int_local_bound v a) hθ) hle
  · exact (v.map_sub_eq_of_lt_right ((int_local_bound v a).trans_lt (lt_of_not_ge hθ))).trans
      (max_eq_right (le_of_not_ge hθ)).symm

/-- At a matching simple residue, the linear Taylor term controls the valuation. -/
theorem affine_valuation_of_simple_hit (v : Valuation K Γ) (f : ℤ[X]) (θ : K) (a : ℤ)
    (hroot : f.eval₂ (Int.castRingHom K) θ = 0)
    (hhit : v ((a : K) - θ) < 1)
    (hder : v ((f.derivative.eval a : ℤ) : K) = 1) :
    v ((a : K) - θ) = v ((f.eval a : ℤ) : K) := by
  have ht : v θ ≤ 1 := by
    have h := v.map_sub_le (int_local_bound v a) hhit.le
    simpa using h
  let t : v.integer := ⟨θ, ht⟩
  let b : v.integer := a
  let F := f.map (Int.castRingHom v.integer)
  obtain ⟨c, hc⟩ := F.exists_mul_sq_add_linear_part_eq_eval_add b (t-b)
  rw [add_sub_cancel] at hc
  have hzero : F.eval t = 0 := Subtype.coe_injective (by
    change ((F.eval t : v.integer) : K) = 0
    rwa [local_eval_cast])
  have eq : F.eval b = (b-t) * (F.derivative.eval b + c*(t-b)) := by
    rw [hzero] at hc
    linear_combination hc
  have hm := congrArg v.integer.subtype eq
  change ((F.eval b : v.integer) : K) = ((b : K) - θ) *
    (((F.derivative.eval b : v.integer) : K) + (c : K) * (θ - (b : K))) at hm
  have hb : (b : K) = (a : K) := rfl
  have heval (g : ℤ[X]) : (((g.map (Int.castRingHom v.integer)).eval b : v.integer) : K) =
      ((g.eval a : ℤ) : K) := by
    rw [local_eval_cast, hb]
    exact Polynomial.eval₂_at_apply (Int.castRingHom K) a
  have der : v ((F.derivative.eval b : v.integer) : K) = 1 := by
    simpa only [F, Polynomial.derivative_map, heval] using hder
  have err : v ((c : K) * (θ - (b : K))) < 1 := by
    rw [map_mul, hb, v.map_sub_swap θ]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' c.property) hhit
  rw [hb] at err
  rw [heval f, hb] at hm
  rw [hm, map_mul, v.map_add_eq_of_lt_left (err.trans_eq der.symm), der, mul_one]


/-- Every finite prime of a number field has a rational prime center. -/
theorem valuation_rational_center [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ z : ℤ, v.valuation K (z : K) < 1 ↔ (p : ℤ) ∣ z := by
  let p := Ideal.absNorm (v.asIdeal.under ℤ)
  let : NeZero v.asIdeal := ⟨v.ne_bot⟩
  refine ⟨p, Nat.absNorm_under_prime _, fun z => ?_⟩
  have h := v.valuation_lt_one_iff_mem (K := K) (z : 𝓞 K)
  simpa only [map_intCast, Int.cast_mem_ideal_iff] using h

/-- At each good prime one residue determines all the nontrivial valuations;
the size of a hit is the valuation of the rational prime itself. -/
theorem affine_prime_row (v : Valuation K Γ) (p : ℕ)
    (center : ∀ z : ℤ, v (z : K) < 1 ↔ (p : ℤ) ∣ z) (f : ℤ[X]) (θ : K)
    (hroot : f.eval₂ (Int.castRingHom K) θ = 0) (r : ℤ) (hr : v ((r : K)-θ) < 1)
    (a : ℤ) (clean : (p : ℤ) ∣ f.eval a →
      ¬(p : ℤ)^2 ∣ f.eval a ∧ ¬(p : ℤ) ∣ f.derivative.eval a) :
    v ((a : K)-θ) = if (p : ℤ) ∣ a-r then v (p : K) else 1 := by
  have unit_of_not_dvd (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : v (z : K) = 1 :=
    le_antisymm (int_local_bound v z) (le_of_not_gt (fun hv => h ((center z).mp hv)))
  have ht : v θ ≤ 1 := by simpa using v.map_sub_le (int_local_bound v r) hr.le
  have hit : v ((a : K)-θ) < 1 ↔ (p : ℤ) ∣ a-r := by
    rw [← center, Int.cast_sub]
    constructor
    · intro ha
      simpa using v.map_sub_lt ha hr
    · intro ha
      have h := v.map_sub_lt ha (show v (θ - (r : K)) < 1 by rwa [v.map_sub_swap])
      simpa using h
  split_ifs with hd
  · have hh := hit.mpr hd
    have divides : (p : ℤ) ∣ f.eval a := by
      by_contra hp
      have h := affine_valuation_of_unit_value v f θ a hroot (unit_of_not_dvd _ hp)
      rw [h, max_eq_left ht] at hh
      exact lt_irrefl _ hh
    obtain ⟨hne, hder⟩ := clean divides
    rw [affine_valuation_of_simple_hit v f θ a hroot hh (unit_of_not_dvd _ hder)]
    obtain ⟨q, hq⟩ := divides
    have hq' : ¬(p : ℤ) ∣ q := by
      intro hq'
      obtain ⟨k, hk⟩ := hq'
      apply hne
      exact ⟨k, by rw [hq, hk, pow_two, mul_assoc]⟩
    rw [hq, Int.cast_mul, map_mul, unit_of_not_dvd q hq', mul_one, Int.cast_natCast]
  · exact le_antisymm (v.map_sub_le (int_local_bound v a) ht)
      (le_of_not_gt (fun hv => hd (hit.mp hv)))


/-- A root of a nonmonic integer polynomial is integral at any prime where
the leading coefficient is a unit, since its product with that coefficient
is globally integral over ℤ. -/
theorem root_bound_of_unit_leading [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (f : ℤ[X]) (θ : K)
    (hroot : f.eval₂ (Int.castRingHom K) θ = 0)
    (hunit : v.valuation K ((f.leadingCoeff : ℤ) : K) = 1) : v.valuation K θ ≤ 1 := by
  have h := (Int.castRingHom K).isIntegralElem_leadingCoeff_mul f θ hroot
  let z : 𝓞 K := ⟨_, h⟩
  have hz := v.valuation_le_one (K := K) z
  change v.valuation K (((f.leadingCoeff : ℤ) : K) * θ) ≤ 1 at hz
  rwa [map_mul, hunit, one_mul] at hz

/-- A complete splitting modulo the rational prime selects a linear factor
in the residue field of every finite prime above it. -/
theorem affine_hit_of_split {ι : Type*} [Fintype ι]
    (v : Valuation K Γ) (p : ℕ) (hp : v (p : K) < 1) (f q : ℤ[X]) (θ : K)
    (root : f.eval₂ (Int.castRingHom K) θ = 0) (bound : v θ ≤ 1)
    (r : ι → ℤ) (hc : v ((f.leadingCoeff : ℤ) : K) = 1)
    (hsplit : f = Polynomial.C f.leadingCoeff * ∏ i, (Polynomial.X - Polynomial.C (r i)) +
      Polynomial.C (p : ℤ) * q) :
    ∃ i, v ((r i : K)-θ) < 1 := by
  classical
  by_contra! ha
  have one (i) : v (θ - (r i : K)) = 1 := by
    rw [v.map_sub_swap]
    exact le_antisymm (v.map_sub_le (int_local_bound v _) bound) (ha i)
  let E := Polynomial.eval₂RingHom (Int.castRingHom K) θ
  have root' : E f = 0 := root
  have h := congrArg E hsplit
  have eC (z : ℤ) : E (Polynomial.C z) = (z : K) := Polynomial.eval₂_C ..
  have eX : E Polynomial.X = θ := Polynomial.eval₂_X ..
  simp only [root', map_add, map_mul, map_prod, map_sub, eX, eC, Int.cast_natCast] at h
  have vq : v (E q) ≤ 1 := by
    let t : v.integer := ⟨θ, bound⟩
    rw [show E q = (((q.map (Int.castRingHom v.integer)).eval t : v.integer) : K) from
      (local_eval_cast v q t).symm]
    exact ((q.map (Int.castRingHom v.integer)).eval t).property
  have H : v (((f.leadingCoeff : ℤ) : K) * ∏ i, (θ - (r i : K))) = v ((p : K)*E q) := by
    rw [eq_neg_of_add_eq_zero_left h.symm, v.map_neg]
  simp only [map_mul, map_prod, hc, one, Finset.prod_const_one, one_mul] at H
  exact (not_lt_of_ge H.le) ((mul_le_of_le_one_right' vq).trans_lt hp)


private theorem lift_split_congruence (p : ℕ) (f h : ℤ[X])
    (cong : f.map (Int.castRingHom (ZMod p)) = h.map (Int.castRingHom (ZMod p))) :
    ∃ q : ℤ[X], f = h + Polynomial.C (p : ℤ) * q := by
  have zero : (f-h).map (Int.castRingHom (ZMod p)) = 0 := by rw [Polynomial.map_sub, cong, sub_self]
  have dvd : Polynomial.C (p : ℤ) ∣ f-h := by
    apply (Polynomial.C_dvd_iff_dvd_coeff ..).mpr
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.coeff_zero] using
      congrArg (fun g : (ZMod p)[X] => g.coeff i) zero
  obtain ⟨q,hq⟩ := dvd
  exact ⟨q, by rw [← hq]; ring⟩


private theorem prod_zpow_sum {ι : Type*} [Fintype ι] (g : Γ) (hg : g ≠ 0) (b : ι → ℤ) :
    (∏ i, g ^ b i) = g ^ ∑ i, b i := by
  classical
  suffices ∀ s : Finset ι, (∏ i ∈ s, g ^ b i) = g ^ ∑ i ∈ s, b i from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hg]

/-- Rational incidence equations suffice for genuine field units. The target
factorization is only needed for a nonzero target exponent. A height-one prime
selects a rational residue whenever it hits a mark. Its ramification index
multiplies the whole equation and need not be computed. -/
theorem unit_from_clean_affine_relations [NumberField K] {ι : Type*} [Fintype ι]
    (f : ℤ[X]) (θ : K) (root : f.eval₂ (Int.castRingHom K) θ = 0)
    (a : ι → ℤ) (mark_ne : ∀ i, (a i : K)-θ ≠ 0) (c : ι → ℤ) (balance : ∑ i, c i = 0)
    (ℓ E : ℕ) (hℓ : ℓ.Prime)
    (clean : ∀ (p : ℕ), p.Prime → ∀ i, (p : ℤ) ∣ f.eval (a i) →
      ¬(p : ℤ)^2 ∣ f.eval (a i) ∧ ¬(p : ℤ) ∣ f.derivative.eval (a i))
    (rows : ∀ (p : ℕ), p.Prime → ∀ r : ℤ, (p : ℤ) ∣ f.eval r →
      ∑ i, (if (p : ℤ) ∣ a i-r then c i else 0) = if p = ℓ then -(E : ℤ) else 0)
    (target_split : E ≠ 0 → (¬(ℓ : ℤ) ∣ f.leadingCoeff) ∧ ∃ (n : ℕ) (residues : Fin n → ℤ),
      f.map (Int.castRingHom (ZMod ℓ)) =
        (Polynomial.C f.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (residues j))).map
          (Int.castRingHom (ZMod ℓ))) :
    ∃ u : (𝓞 K)ˣ, (u : K) = (ℓ : K)^E * ∏ i, ((a i : K)-θ)^(c i) := by
  classical
  have ell_ne : (ℓ : K) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  apply unit_of_finite_valuations _ (mul_ne_zero (pow_ne_zero E ell_ne)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (mark_ne i))))
  intro v
  let w := v.valuation K
  obtain ⟨p, hp, center⟩ := valuation_rational_center v
  have unit_of_not_dvd (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : w (z : K) = 1 :=
    le_antisymm (int_local_bound w z) (le_of_not_gt (fun hv => h ((center z).mp hv)))
  have wp : w (p : K) < 1 := by simpa only [Int.cast_natCast] using (center p).mpr (dvd_refl _)
  have pnz : w (p : K) ≠ 0 := (map_ne_zero w).mpr (by exact_mod_cast hp.ne_zero)
  have wother (hne : p ≠ ℓ) : w (ℓ : K) = 1 := by
    have hn : ¬ (p : ℤ) ∣ (ℓ : ℤ) := by
      rw [Int.natCast_dvd_natCast, Nat.prime_dvd_prime_iff_eq hp hℓ]
      exact hne
    simpa only [Int.cast_natCast] using unit_of_not_dvd ℓ hn
  change w _ = 1
  rw [map_mul, map_pow, map_prod]
  simp only [map_zpow₀]
  by_cases exists_hit : ∃ r : ℤ, w ((r : K)-θ) < 1
  · obtain ⟨r, hr⟩ := exists_hit
    have hfv : (p : ℤ) ∣ f.eval r := by
      by_contra hv
      have bad := affine_valuation_of_unit_value w f θ r root (unit_of_not_dvd _ hv)
      exact (not_lt_of_ge ((le_max_left ..).trans bad.symm.le)) hr
    have row (i) : w ((a i : K)-θ) ^ c i =
        w (p : K) ^ (if (p : ℤ) ∣ a i-r then c i else 0) := by
      rw [affine_prime_row w p center f θ root r hr (a i) (clean p hp i)]
      split_ifs <;> simp
    simp only [row, prod_zpow_sum _ pnz, rows p hp r hfv]
    by_cases eq : p = ℓ
    · subst p
      simpa [← zpow_natCast] using mul_inv_cancel₀ (zpow_ne_zero (E : ℤ) pnz)
    · simp [eq, wother eq]
  · have inactive : w (ℓ : K)^E = 1 := by
      by_cases e : E = 0
      · simp [e]
      by_cases eq : p = ℓ
      · subst p
        obtain ⟨hunit, n, rs, hs⟩ := target_split e
        have unit := unit_of_not_dvd f.leadingCoeff hunit
        have bound := root_bound_of_unit_leading v f θ root unit
        obtain ⟨q, hq⟩ := lift_split_congruence _ _ _ hs
        obtain ⟨j, hj⟩ := affine_hit_of_split w ℓ wp f q θ root bound rs unit hq
        exact (exists_hit ⟨_, hj⟩).elim
      · simp [wother eq]
    have same (i) : w ((a i : K)-θ) = max 1 (w θ) := by
      by_cases hθ : w θ ≤ 1
      · rw [max_eq_left hθ]
        exact le_antisymm (w.map_sub_le (int_local_bound w _) hθ)
          (le_of_not_gt (fun hv => exists_hit ⟨a i, hv⟩))
      · exact (w.map_sub_eq_of_lt_right ((int_local_bound w _).trans_lt (lt_of_not_ge hθ))).trans
          (max_eq_right (le_of_not_ge hθ)).symm
    have nn : max 1 (w θ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left ..))
    simp only [same, inactive, prod_zpow_sum _ nn, balance, zpow_zero, one_mul]

/-- The prescribed distinct target roots, in number at least the integer
degree, force the complete residue factorization needed by the extractor. -/
theorem target_factorization_of_distinct_roots (ℓ : ℕ) (hp : ℓ.Prime) (f : ℤ[X])
    (leading : ¬(ℓ : ℤ) ∣ f.leadingCoeff) {n : ℕ} (r : Fin n → ℤ)
    (degree : f.natDegree ≤ n) (distinct : Function.Injective (fun i => (r i : ZMod ℓ)))
    (roots : ∀ i, (ℓ : ℤ) ∣ f.eval (r i)) :
    f.map (Int.castRingHom (ZMod ℓ)) =
      (C f.leadingCoeff * ∏ i, (X - C (r i))).map (Int.castRingHom (ZMod ℓ)) := by
  classical
  let : Fact ℓ.Prime := ⟨hp⟩
  let μ := Int.castRingHom (ZMod ℓ)
  let P := f.map μ
  have nz : μ f.leadingCoeff ≠ 0 := fun hz => leading ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hz)
  have hlead : P.leadingCoeff = μ f.leadingCoeff := leadingCoeff_map_of_leadingCoeff_ne_zero μ nz
  let g (i : Fin n) : (ZMod ℓ)[X] := X - C (r i : ZMod ℓ)
  have dvd : ∏ i, g i ∣ P := by
    refine Finset.prod_dvd_of_coprime (fun i _ j _ ne => ?_) fun i _ => ?_
    · exact pairwise_coprime_X_sub_C (fun _ _ h => h) (fun h => ne (distinct h))
    · apply dvd_iff_isRoot.mpr
      change (f.map μ).eval (μ (r i)) = 0
      rw [eval_map_apply]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (roots i)
  have monic : (∏ i, g i).Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have deg : P.natDegree ≤ (∏ i, g i).natDegree := by
    have eq := natDegree_finsetProd_X_sub_C_eq_card Finset.univ (fun i => (r i : ZMod ℓ))
    change (∏ i, g i).natDegree = _ at eq
    rw [eq, Finset.card_univ, Fintype.card_fin]
    exact (natDegree_map_le (f := μ) (p := f)).trans degree
  have result := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le monic dvd deg
  rw [hlead] at result
  simpa only [P, μ, g, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom] using result

/-- Rows for clean residues touched by at least one sampled mark and the target
residues suffice. All other rows have empty support. -/
theorem all_rows_of_finite_incidence {ι τ : Type*} [Fintype ι]
    (f : ℤ[X]) (a : ι → ℤ) (c : ι → ℤ) (ℓ E : ℕ)
    (prime : τ → ℕ) (residue : τ → ℤ)
    (row : ∀ j, ∑ i, (if (prime j : ℤ) ∣ a i-residue j then c i else 0) =
      if prime j = ℓ then -(E : ℤ) else 0)
    (covers : ∀ (p : ℕ), p.Prime → ∀ r : ℤ, (p : ℤ) ∣ f.eval r →
      (p = ℓ ∧ E ≠ 0 ∨ ∃ i, (p : ℤ) ∣ a i-r) →
      ∃ j, prime j = p ∧ (p : ℤ) ∣ residue j-r) :
    ∀ (p : ℕ), p.Prime → ∀ r : ℤ, (p : ℤ) ∣ f.eval r →
      ∑ i, (if (p : ℤ) ∣ a i-r then c i else 0) = if p = ℓ then -(E : ℤ) else 0 := by
  classical
  intro p hp r hr
  by_cases active : p = ℓ ∧ E ≠ 0 ∨ ∃ i, (p : ℤ) ∣ a i-r
  · obtain ⟨j, hj, hres⟩ := covers p hp r hr active
    have same (i) : (p : ℤ) ∣ a i-residue j ↔ (p : ℤ) ∣ a i-r := by
      constructor
      · intro h
        simpa using dvd_add h hres
      · intro h
        simpa using dvd_sub h hres
    simpa only [hj, same] using row j
  · have none (i) : ¬ (p : ℤ) ∣ a i-r := fun h => active (.inr ⟨i,h⟩)
    simp only [if_neg (none _), Finset.sum_const_zero]
    split_ifs with eq
    · have : E = 0 := not_not.mp (fun ne => active (.inl ⟨eq, ne⟩))
      simp [this]
    · rfl

/-- The conditions on a single field's clean affine marks and the integer
rows that record their prime divisors. The two fields may share a matrix. -/
structure AffineMarkRows {ι τ : Type*} (f : ℤ[X]) (a : ι → ℤ) (V : Matrix τ ι ℤ) : Prop where
  clean : ∀ (p : ℕ), p.Prime → ∀ i, (p : ℤ) ∣ f.eval (a i) →
    ¬(p : ℤ)^2 ∣ f.eval (a i) ∧ ¬(p : ℤ) ∣ f.derivative.eval (a i)
  represented : ∀ (p : ℕ), p.Prime → ∀ j, (p : ℤ) ∣ f.eval (a j) →
    ∃ k, ∀ i, V k i = if (p : ℤ) ∣ a i - a j then 1 else 0

theorem AffineMarkRows.nonzero_marks {K ι τ : Type*} [Field K] [CharZero K]
    {f : ℤ[X]} {a : ι → ℤ} {V : Matrix τ ι ℤ} (marks : AffineMarkRows f a V)
    (θ : K) (root : f.eval₂ (Int.castRingHom K) θ = 0) (j : ι) : (a j : K) - θ ≠ 0 := by
  intro hz
  rw [← sub_eq_zero.mp hz] at root
  change f.eval₂ (Int.castRingHom K) (Int.castRingHom K (a j)) = 0 at root
  rw [eval₂_at_apply, Int.coe_castRingHom] at root
  have vanish : f.eval (a j) = 0 := by
    exact_mod_cast (show ((f.eval (a j) : ℤ) : K) = 0 from root)
  have h := marks.clean 2 Nat.prime_two j (vanish ▸ dvd_zero 2)
  exact h.1 (vanish ▸ dvd_zero _)

/-- A null vector of the actual augmented integer matrix gives a neutral
field unit. This discharges the finite-place hypothesis of the Gram/minor
theorem using just the clean mark checks and recorded integer incidence rows. -/
theorem AffineMarkRows.neutral_unit {K ι τ : Type*} [Field K] [NumberField K] [Fintype ι]
    {f : ℤ[X]} {a : ι → ℤ} {V : Matrix τ ι ℤ} (marks : AffineMarkRows f a V)
    (θ : K) (root : f.eval₂ (Int.castRingHom K) θ = 0) (top : τ) (intercept : ∀ j, V top j = 1)
    (c : ι → ℤ) (null : ∀ k, ∑ j, V k j * c j = 0) :
    ∃ u : (𝓞 K)ˣ, (u : K) = ∏ j, ((a j : K)-θ)^(c j) := by
  classical
  have sz : ∑ j, c j = 0 := by simpa [intercept] using null top
  suffices h : ∀ (p : ℕ), p.Prime → ∀ r : ℤ, (p : ℤ) ∣ f.eval r →
      ∑ i, (if (p : ℤ) ∣ a i-r then c i else 0) = 0 by
    simpa using unit_from_clean_affine_relations f θ root a (marks.nonzero_marks θ root) c sz
      2 0 Nat.prime_two marks.clean (by simpa using h) (by simp)
  intro p hp r hr
  by_cases hit : ∃ j, (p : ℤ) ∣ a j-r
  · obtain ⟨j, hj⟩ := hit
    have div : (p : ℤ) ∣ f.eval (a j) := by
      simpa using dvd_add (dvd_trans hj (sub_dvd_eval_sub (a j) r f)) hr
    obtain ⟨k, hk⟩ := marks.represented p hp j div
    have equiv (i) : (p : ℤ) ∣ a i-a j ↔ (p : ℤ) ∣ a i-r := by
      constructor
      · intro t; simpa using dvd_add t hj
      · intro t; simpa using dvd_sub t hj
    simpa only [hk, equiv, ite_mul, one_mul, zero_mul] using null k
  · exact Finset.sum_eq_zero (fun i _ => if_neg (fun hi => hit ⟨i, hi⟩))


/-- Index for the independent unit coordinates of the two fields. -/
abbrev UnitRankRows (K₁ K₂ : Type*) [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂] :=
  Fin (NumberField.Units.rank K₁) ⊕ Fin (NumberField.Units.rank K₂)

/-- From the actual positive Gram and the clean rational mark matrix in both
fields, select genuine neutral units with nonzero determinant in the paired
Dirichlet basis. No field-unit witnesses or lattice basis are inputs. -/
theorem clean_affine_unit_minor {K₁ K₂ α β κ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype α] [Fintype β] [Fintype κ] [Fintype ι]
    (σ₁ : α → K₁ →+* ℝ) (σ₂ : β → K₂ →+* ℝ) (a : κ → ℤ) (V : Matrix ι κ ℤ)
    (f₁ f₂ : ℤ[X]) (θ₁ : K₁) (θ₂ : K₂)
    (root₁ : f₁.eval₂ (Int.castRingHom K₁) θ₁ = 0)
    (root₂ : f₂.eval₂ (Int.castRingHom K₂) θ₂ = 0)
    (rows₁ : AffineMarkRows f₁ a V) (rows₂ : AffineMarkRows f₂ a V)
    (top : ι) (intercept : ∀ j, V top j = 1) (A : ℝ) (hA : 0 < A)
    (H : Matrix (UnitRankRows K₁ K₂) (α ⊕ β) ℝ)
    (scale : ι → ℝ) (hs : ∀ i, scale i ≠ 0) (W : Matrix κ κ ℝ)
    (cert : let U := H * markLogs σ₁ σ₂ (fun j => (a j : K₁)-θ₁) (fun j => (a j : K₂)-θ₂) A
            let M := jointRows V scale U
            (M * W * M.transpose).PosDef) :
    ∃ (z : UnitRankRows K₁ K₂ → κ → ℤ)
      (u₁ : UnitRankRows K₁ K₂ → (𝓞 K₁)ˣ) (u₂ : UnitRankRows K₁ K₂ → (𝓞 K₂)ˣ),
      (∀ k i, ∑ j, V i j * z k j = 0) ∧
      (∀ k, (u₁ k : K₁) = ∏ j, ((a j : K₁)-θ₁)^(z k j)) ∧
      (∀ k, (u₂ k : K₂) = ∏ j, ((a j : K₂)-θ₂)^(z k j)) ∧
      ((pairedUnitBasis K₁ K₂).toMatrix (fun k => (unitClass (u₁ k), unitClass (u₂ k)))).det ≠ 0 := by
  apply unit_minor_from_positive_gram σ₁ σ₂ _ _ (rows₁.nonzero_marks θ₁ root₁)
    (rows₂.nonzero_marks θ₂ root₂) A hA H V top intercept scale hs W (pairedUnitBasis K₁ K₂) cert
  intro z null
  obtain ⟨u₁,h₁⟩ := rows₁.neutral_unit θ₁ root₁ top intercept z null
  obtain ⟨u₂,h₂⟩ := rows₂.neutral_unit θ₂ root₂ top intercept z null
  exact ⟨u₁,u₂,h₁,h₂⟩

end Cogentic
