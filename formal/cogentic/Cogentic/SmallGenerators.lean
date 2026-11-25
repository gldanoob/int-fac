import Cogentic.Primality
import Cogentic.CharacterEstimate
import Mathlib.GroupTheory.FiniteAbelian.Duality

namespace Cogentic

open Formalism.MainNotions.GlobalTheoryTheory

private theorem subgroup_character {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (proper : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ ∀ a ∈ H, χ (a : ZMod q) = 1 := by
  classical
  obtain ⟨a,ha⟩ : ∃ a : (ZMod q)ˣ, a ∉ H := by
    by_contra! h; exact proper (top_unique (fun x _ => h x))
  let π := QuotientGroup.mk' H
  have nontriv : π a ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff _).mp h)
  have expo : NeZero ((Monoid.exponent ((ZMod q)ˣ ⧸ H) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := ((ZMod q)ˣ ⧸ H))⟩
  obtain ⟨f,hf⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ nontriv
  let χ : DirichletCharacter ℂ q := MulChar.ofUnitHom (f.comp π)
  refine ⟨χ, ?_, ?_⟩
  · intro h
    apply hf
    apply Units.ext
    have he := DFunLike.congr_fun h (a : ZMod q)
    simpa [χ, MulChar.ofUnitHom_coe] using he
  · intro b hb
    have eq : π b = 1 := (QuotientGroup.eq_one_iff _).mpr hb
    simp [χ, eq]

/-- If every integer up to X is invisible to a nonprincipal character on units,
    its uncentered prime-power sum agrees with the principal character term by term. -/
theorem generators_of_psi_gap {q X : ℕ} [NeZero q] {err : ℝ} (gap : 2*err < X)
    (bound : ∀ χ : DirichletCharacter ℂ q, ‖psi0 χ (X : ℝ)‖ ≤ err) :
    generatesUnits q (List.range' 1 X) := by
  classical
  let H := Subgroup.closure {u : (ZMod q)ˣ | ∃ g ∈ List.range' 1 X, (u : ZMod q) = g}
  by_contra proper
  obtain ⟨χ,nonprincipal,trivialOn⟩ := subgroup_character H proper
  have agree (j : ℕ) (lo : 1 ≤ j) (hi : j ≤ X) :
      χ (j : ZMod q) = (1 : DirichletCharacter ℂ q) (j : ZMod q) := by
    by_cases unit : IsUnit (j : ZMod q)
    · let u := unit.unit
      have hmem : u ∈ H := Subgroup.subset_closure
        ⟨j,List.mem_range'_1.mpr ⟨lo, by omega⟩,unit.unit_spec⟩
      simpa only [u, IsUnit.unit_spec, MulChar.one_apply unit] using trivialOn u hmem
    · rw [χ.map_nonunit unit, MulChar.map_nonunit _ unit]
  have difference : psi0 χ (X : ℝ) - psi0 (1 : DirichletCharacter ℂ q) (X : ℝ) = (X : ℂ) := by
    simp only [psi0, Nat.floor_natCast, if_neg nonprincipal, if_true, sub_zero]
    have same : (∑ j ∈ Finset.Icc 1 X, (abelian₂ j : ℂ) * χ (j : ZMod q)) =
        ∑ j ∈ Finset.Icc 1 X, (abelian₂ j : ℂ) * (1 : DirichletCharacter ℂ q) (j : ZMod q) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [agree j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2]
    rw [same]; push_cast; ring
  have contradiction := (norm_sub_le (psi0 χ X) (psi0 (1 : DirichletCharacter ℂ q) X)).trans
    (add_le_add (bound χ) (bound 1))
  rw [difference] at contradiction
  simp only [Complex.norm_natCast] at contradiction
  linarith

/-- An integer polynomial cutoff for subgroup generation from a uniform centered ψ estimate. -/
def polyCutoff (k bits : ℕ) : ℕ := (1000*(k+bits+1))^6

theorem polyCutoff_gap {C : ℝ} (hc : 0 ≤ C) {k q bits : ℕ} (ck : C ≤ k)
    (positive : 0 < q) (fits : q < 2^bits) :
    let X : ℝ := polyCutoff k bits
    2 ≤ X ∧ 2*(C*Real.sqrt X*(1+Real.log (3*q*X))^2) < X := by
  let T : ℝ := 1000*((k:ℝ)+bits+1)
  have tk : 200*C < T := by dsimp [T]; have := Nat.cast_nonneg (α := ℝ) bits; linarith
  have kb := Nat.cast_nonneg (α := ℝ) k
  have bb := Nat.cast_nonneg (α := ℝ) bits
  have tb : (bits:ℝ) ≤ T := by dsimp [T]; linarith
  have t1 : 2 ≤ T := by dsimp [T]; linarith
  have tp : 0 < T := by linarith
  have qp : 0 < (q:ℝ) := by exact_mod_cast positive
  have qfits : (q:ℝ) < (2:ℝ)^bits := by exact_mod_cast fits
  have logq : Real.log q ≤ bits := by
    have h := Real.log_le_log qp qfits.le
    rw [Real.log_pow] at h
    have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    exact h.trans (by simpa using mul_le_mul_of_nonneg_left log2 bb)
  have logt := Real.log_le_sub_one_of_pos tp
  have log3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  have dBound : 1 + Real.log (3*(q:ℝ)*T^6) ≤ 9*T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) qp.ne', Real.log_pow]
    norm_num
    linarith
  have xbig : 2 ≤ T^6 := by nlinarith [show (2:ℝ)^6 ≤ T^6 from pow_le_pow_left₀ (by norm_num) t1 6]
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast positive
  have dpos : 0 ≤ 1 + Real.log (3*(q:ℝ)*T^6) := by
    have arg : 1 ≤ 3*(q:ℝ)*T^6 := by nlinarith [mul_le_mul q1 xbig (by norm_num) (by positivity : (0:ℝ)≤q)]
    linarith [Real.log_nonneg arg]
  have xeq : (polyCutoff k bits : ℝ) = T^6 := by simp [polyCutoff,T]
  rw [xeq]
  refine ⟨xbig, ?_⟩
  have sqrtX : Real.sqrt (T^6) = T^3 := by
    rw [show T^6 = (T^3)^2 by ring, Real.sqrt_sq (by positivity)]
  rw [sqrtX]
  calc
    _ ≤ 2*(C*T^3*(9*T)^2) := by gcongr
    _ = (162*C)*T^5 := by ring
    _ < T*T^5 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ = _ := by ring

/-- This interface consumes the all-moduli, all-character estimate at natural endpoints. -/
theorem polynomial_bases_generate {C : ℝ} (hc : 0 ≤ C) {k : ℕ} (ck : C ≤ k)
    (bound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
      ‖psi0 χ x‖ ≤ C*Real.sqrt x*(1+Real.log (3*q*x))^2)
    {q bits : ℕ} [NeZero q] (fits : q < 2^bits) :
    generatesUnits q (List.range' 1 (polyCutoff k bits)) := by
  have ⟨big,gap⟩ := polyCutoff_gap hc ck (Nat.pos_of_ne_zero (NeZero.ne q)) fits
  exact generators_of_psi_gap gap (fun χ => bound q χ _ big)

/-- One fixed constant serves every modulus and bit length. -/
theorem polynomial_generators_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ k : ℕ, ∀ (q bits : ℕ) [NeZero q], q < 2^bits →
      generatesUnits q (List.range' 1 (polyCutoff k bits)) := by
  obtain ⟨C,hc,bound⟩ := Window.uniform_psi_from_critical_line line
  obtain ⟨k,hk⟩ := exists_nat_ge C
  exact ⟨k, fun _ _ _ fits => polynomial_bases_generate hc hk bound fits⟩

theorem prime_and_split_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ k : ℕ, ∀ (n bits : ℕ) [NeZero n], n < 2^bits →
      let gs := List.range' 1 (polyCutoff k bits)
      (primeCheck n gs = true ↔ n.Prime) ∧
      ∀ (m p q : ℕ) [Fact p.Prime] [Fact q.Prime], 2 ≤ n → 2 ≤ m →
        2 < p → 2 < q → p ≠ q → p ∣ n → q ∣ n → p-1 ∣ m → q-1 ∣ m →
        TwoThirdsFinish.splitWithExponent n m gs ≠ none := by
  obtain ⟨k,hk⟩ := polynomial_generators_from_critical_line line
  refine ⟨k, fun n bits _ fits => ⟨primeCheck_correct _ _ (hk n bits fits),?_⟩⟩
  intro m p q _ _ hn hm hp hq neq pn qn pm qm
  exact saturated_splitter hn hm hp hq neq pn qn pm qm _ (hk n bits fits)

theorem polynomial_primeCheck_budget (k : ℕ) {n bits : ℕ} (hn : 2 ≤ n) (fits : n < 2^bits) :
    primalityListBudget n (List.range' 1 (polyCutoff k bits)) ≤ polyCutoff k bits * (7*bits+1) := by
  simpa using primality_list_budget hn fits (List.range' 1 (polyCutoff k bits))

end Cogentic

#print axioms Cogentic.polynomial_bases_generate
#print axioms Cogentic.prime_and_split_from_critical_line
