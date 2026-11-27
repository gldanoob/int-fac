import Cogentic.RandomizedPrimeProductGridFourier
import Cogentic.RandomizedVectorPerron

namespace Cogentic.Randomized

open scoped BigOperators Classical
open Complex Finset MeasureTheory

variable {m B : ℕ} [NeZero m] [NeZero B] [NeZero (m * B)]

/-- A row and an additive Fourier frequency in the prime-product grid. -/
abbrev GridCoordinate (m B : ℕ) := (ZMod m)ˣ × AddChar (ZMod B) ℂ

private noncomputable def rowKernel (cop : m.Coprime B) (i : GridCoordinate m B)
    (a : (ZMod B)ˣ) : ℂ :=
  i.2 ((gridPhaseEquiv cop i.1).symm a) -
    (∑ b : (ZMod B)ˣ, i.2 ((gridPhaseEquiv cop i.1).symm b)) / Fintype.card (ZMod B)ˣ

omit [NeZero m] [NeZero (m * B)] in
private theorem rowKernel_norm_le (cop : m.Coprime B) (i : GridCoordinate m B)
    (a : (ZMod B)ˣ) : ‖rowKernel cop i a‖ ≤ 2 := by
  have hc : (0 : ℝ) < Fintype.card (ZMod B)ˣ := Nat.cast_pos.mpr Fintype.card_pos
  have hn : ‖(∑ b : (ZMod B)ˣ, i.2 ((gridPhaseEquiv cop i.1).symm b))‖ ≤
      (Fintype.card (ZMod B)ˣ : ℝ) := by
    simpa only [AddChar.norm_apply, sum_const, card_univ, nsmul_eq_mul, mul_one] using
      (norm_sum_le (s := (univ : Finset (ZMod B)ˣ))
        (fun b => i.2 ((gridPhaseEquiv cop i.1).symm b)))
  unfold rowKernel
  apply (norm_sub_le _ _).trans
  rw [AddChar.norm_apply, norm_div, Complex.norm_natCast]
  have h := (div_le_one hc).2 hn
  linarith

private noncomputable def extendUnitColumns {q : ℕ} (f : (ZMod q)ˣ → ℂ) (a : ZMod q) : ℂ :=
  if ha : IsUnit a then f ha.unit else 0

omit [NeZero m] [NeZero (m * B)] in
private theorem gridFourier_eq_unit_sum (cop : m.Coprime B)
    (f : (ZMod (m * B))ˣ → ℂ) (i : GridCoordinate m B) :
    gridFourier cop f i.1 i.2 =
      ∑ a : (ZMod B)ˣ, f ((gridUnitCRT cop).symm (i.1, a)) * rowKernel cop i a := by
  let row (a : (ZMod B)ˣ) := f ((gridUnitCRT cop).symm (i.1, a))
  let μ := (∑ a, row a) / (Fintype.card (ZMod B)ˣ : ℂ)
  let e := gridPhaseEquiv cop i.1
  let g (x : ZMod B) := extendUnitColumns (fun a => row a - μ) x * i.2 (e.symm x)
  have hzero (a : ZMod B) (ha : ¬ IsUnit a) : g a = 0 := by simp [g, extendUnitColumns, ha]
  let emb : (ZMod B)ˣ ↪ ZMod B := ⟨Units.val, Units.val_injective⟩
  have hmem (a : ZMod B) : a ∈ univ.map emb ↔ IsUnit a := by
    rw [mem_map]
    constructor
    · rintro ⟨u, _, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, mem_univ _, hu⟩
  calc
    _ = ∑ v : ZMod B, g (e v) := by
      unfold gridFourier RandomizedTwoFactorFourier.transform
      apply sum_congr rfl
      intro v _
      dsimp only [g]
      rw [Equiv.symm_apply_apply]
      unfold gridCenteredRow
      rfl
    _ = ∑ a : ZMod B, g a := e.bijective.sum_comp g
    _ = ∑ a ∈ univ.map emb, g a := by
      symm
      exact sum_subset (subset_univ _) fun a _ ha => hzero a (fun h => ha ((hmem a).2 h))
    _ = ∑ a : (ZMod B)ˣ, (row a - μ) * i.2 (e.symm a) := by
      rw [sum_map]
      apply sum_congr rfl
      intro a _
      simp [emb, g, extendUnitColumns]
    _ = _ := by
      change (∑ a : (ZMod B)ˣ, (row a - μ) * i.2 (e.symm a)) =
        ∑ a : (ZMod B)ˣ, row a *
          (i.2 (e.symm a) - (∑ b : (ZMod B)ˣ, i.2 (e.symm b)) / Fintype.card (ZMod B)ˣ)
      simp only [sub_mul, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul, μ]
      ring

private noncomputable def gridCoefficient (cop : m.Coprime B) (i : GridCoordinate m B) (n : ℕ) : ℂ :=
  ∑ a : (ZMod B)ˣ, if ((gridUnitCRT cop).symm (i.1, a) : ZMod (m * B)) = n then
    rowKernel cop i a else 0

private theorem gridFourier_classMass_eq_sum (cop : m.Coprime B) (P : Finset ℕ)
    (w : ℕ → ℂ) (i : GridCoordinate m B) :
    gridFourier cop (Window.classMass P w) i.1 i.2 = ∑ n ∈ P, gridCoefficient cop i n * w n := by
  rw [gridFourier_eq_unit_sum]
  simp only [Window.classMass, sum_mul, gridCoefficient]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp [mul_comm]

private noncomputable def gridRowMass (cop : m.Coprime B) (P : Finset ℕ) (r : (ZMod m)ˣ) : ℝ :=
  ∑ n ∈ P, ∑ a : (ZMod B)ˣ, if ((gridUnitCRT cop).symm (r, a) : ZMod (m * B)) = n then 1 else 0

omit [NeZero m] [NeZero (m * B)] in
private theorem gridRowMass_nonneg (cop : m.Coprime B) (P : Finset ℕ) (r : (ZMod m)ˣ) :
    0 ≤ gridRowMass cop P r :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> positivity

private theorem sum_gridRowMass_le (cop : m.Coprime B) (P : Finset ℕ) :
    ∑ r, gridRowMass cop P r ≤ P.card := by
  have hn (n : ℕ) :
      (∑ u : (ZMod (m * B))ˣ, if (u : ZMod (m * B)) = n then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : IsUnit (n : ZMod (m * B))
    · rw [sum_eq_single h.unit]
      · simp
      · intro a _ ha
        exact if_neg (fun he => ha (Units.ext (he.trans h.unit_spec.symm)))
      · simp
    · rw [sum_eq_zero]
      · norm_num
      · intro u _
        have hu : (u : ZMod (m * B)) ≠ n := by
          intro he
          exact h (he ▸ u.isUnit)
        simp [hu]
  unfold gridRowMass
  rw [sum_comm]
  calc
    _ ≤ ∑ _n ∈ P, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      refine le_of_eq_of_le ?_ (hn n)
      calc
        _ = ∑ p : (ZMod m)ˣ × (ZMod B)ˣ,
            if ((gridUnitCRT cop).symm p : ZMod (m * B)) = n then (1 : ℝ) else 0 :=
          (Fintype.sum_prod_type' (fun r a =>
            if ((gridUnitCRT cop).symm (r, a) : ZMod (m * B)) = n then (1 : ℝ) else 0)).symm
        _ = _ := (gridUnitCRT cop).symm.toEquiv.bijective.sum_comp
          (fun u => if (u : ZMod (m * B)) = n then (1 : ℝ) else 0)
    _ = _ := by simp [nsmul_eq_mul]

private theorem gridCoefficient_mass_le (cop : m.Coprime B) (P : Finset ℕ) (i : GridCoordinate m B) :
    ∑ n ∈ P, ‖gridCoefficient cop i n‖ ≤ 2 * gridRowMass cop P i.1 := by
  unfold gridCoefficient gridRowMass
  rw [mul_sum]
  apply sum_le_sum
  intro n _
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  split_ifs with h
  · simpa using rowKernel_norm_le cop i a
  · simp

private theorem gridRowError_norm_le (cop : m.Coprime B) (P : Finset ℕ) {d : ℝ} (hd : 0 ≤ d) :
    ‖(WithLp.toLp 2 (fun i : GridCoordinate m B => d * gridRowMass cop P i.1) :
        EuclideanSpace ℝ (GridCoordinate m B))‖ ≤ Real.sqrt B * (d * P.card) := by
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (∑ i : GridCoordinate m B, ‖d * gridRowMass cop P i.1‖^2) ≤ _
  simp only [GridCoordinate, Fintype.sum_prod_type, sum_const, card_univ, AddChar.card_eq, ZMod.card,
    nsmul_eq_mul, Real.norm_eq_abs, sq_abs, ← mul_sum]
  rw [← Real.sqrt_sq (mul_nonneg hd (Nat.cast_nonneg P.card)),
    ← Real.sqrt_mul (Nat.cast_nonneg B)]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ (∑ r, d * gridRowMass cop P r)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun r _ => mul_nonneg hd (gridRowMass_nonneg cop P r))
    _ ≤ _ := by
      rw [← mul_sum]
      exact pow_le_pow_left₀ (mul_nonneg hd (sum_nonneg fun r _ => gridRowMass_nonneg cop P r))
        (mul_le_mul_of_nonneg_left (sum_gridRowMass_le cop P) hd) 2


/-- The row Fourier coefficient of the integer prefix of the actual support. -/
noncomputable def gridPrefixFourier (cop : m.Coprime B) (P : Finset ℕ)
    (j : ℕ) (i : GridCoordinate m B) : ℂ :=
  gridFourier cop (Window.classMass (P.filter (· ≤ j)) (fun _ => 1)) i.1 i.2

/-- A common Mellin energy bound controls the coordinatewise maxima over
half-integer cutoffs. The truncation error is charged to each full row mass. -/
theorem gridPrefixFourier_sup_norm_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (cop : m.Coprime B) (X : ℝ) (P C : Finset ℕ) (hC : C.Nonempty) (M : ℝ),
        2 ≤ X → Real.exp 1 ≤ X → 0 ≤ M →
        (∀ j ∈ C, X ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X) →
        (∀ n ∈ P, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
        (∀ t ∈ Set.Icc (-(X^3)) (X^3),
          ∑ r : (ZMod m)ˣ, ∑ χ : AddChar (ZMod B) ℂ,
            ‖gridFourier cop (Window.classMass P
              (fun n => ((n : ℂ)^perronLine (1 / Real.log X) t)⁻¹)) r χ‖^2 ≤ M^2) →
        ‖(WithLp.toLp 2 (fun i : GridCoordinate m B =>
          C.sup' hC (fun j => ‖gridPrefixFourier cop P j i‖)) : EuclideanSpace ℝ (GridCoordinate m B))‖ ≤
          (4 * Real.exp 2 / Real.pi) * (M * Real.log X) + Real.sqrt B * ((2 * K / X^2) * P.card) := by
  obtain ⟨K, hK, trunc⟩ := product_perron_prefix_error
  refine ⟨K, hK, ?_⟩
  intro cop X P C hC M hX heX hM hcut hP henergy
  let c := 1 / Real.log X
  let T := X^3
  let s := perronLine c
  let kernel (t : ℝ) := (1 / (2 * Real.pi) : ℂ) * (s t)⁻¹
  let μ := volume.restrict (Set.Ioc (-T) T)
  let D (t : ℝ) : EuclideanSpace ℂ (GridCoordinate m B) :=
    WithLp.toLp 2 fun i => productDirichletPolynomial P (gridCoefficient cop i) (s t)
  let error : EuclideanSpace ℝ (GridCoordinate m B) :=
    WithLp.toLp 2 fun i => (2 * K / X^2) * gridRowMass cop P i.1
  have hX₀ : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX₀).2 heX
  have hL₀ : 0 < Real.log X := by linarith
  have hc : 0 < c := one_div_pos.2 hL₀
  have hT : c ≤ T :=
    ((div_le_one hL₀).2 hL).trans (one_le_pow₀ (by linarith))
  have hTle : -T ≤ T := by linarith
  have hs (t : ℝ) : (s t).re = c := by simp [s, perronLine]
  have hpow (j : ℕ) (hj : j ∈ C) : ((j : ℝ) + 1 / 2)^c ≤ Real.exp 2 := by
    have hx : 0 < (j : ℝ) + 1 / 2 := hX₀.trans_le (hcut j hj).1
    have hx2 : (j : ℝ) + 1 / 2 ≤ X^2 :=
      (hcut j hj).2.trans (by nlinarith [mul_nonneg hX₀.le (sub_nonneg.2 hX)])
    have hl := Real.log_le_log hx hx2
    rw [Real.log_pow, Nat.cast_ofNat] at hl
    rw [Real.rpow_def_of_pos hx, Real.exp_le_exp]
    change Real.log ((j : ℝ) + 1 / 2) * (1 / Real.log X) ≤ 2
    rwa [mul_one_div, div_le_iff₀ hL₀]
  have hd (t : ℝ) (i : GridCoordinate m B) :
      D t i = gridFourier cop (Window.classMass P (fun n => ((n : ℂ)^s t)⁻¹)) i.1 i.2 := by
    rw [gridFourier_classMass_eq_sum]
    simp [D, productDirichletPolynomial, div_eq_mul_inv]
  have hDn (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖D t‖ ≤ M := by
    rw [EuclideanSpace.norm_eq]
    change Real.sqrt (∑ i : GridCoordinate m B, ‖D t i‖^2) ≤ M
    rw [← Real.sqrt_sq hM]
    apply Real.sqrt_le_sqrt
    simpa only [GridCoordinate, Fintype.sum_prod_type, hd] using henergy t ht
  have hline : Continuous s := by
    change Continuous (fun t : ℝ => (c : ℂ) + t * I)
    fun_prop
  have hiCont : Continuous fun t => (s t)⁻¹ :=
    hline.inv₀ (fun t h => hc.ne' (by simpa [hs t] using congrArg Complex.re h))
  have hkCont : Continuous kernel := hiCont.const_mul _
  have hDcoord (i : GridCoordinate m B) : Continuous fun t => D t i := by
    change Continuous fun t => productDirichletPolynomial P (gridCoefficient cop i) (s t)
    unfold productDirichletPolynomial
    refine continuous_finsetSum _ ?_
    intro n hn
    have hn₀ : (0 : ℝ) < n := hX₀.trans_le (hP n hn).1
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn₀.ne'
    exact continuous_const.div (hline.const_cpow (Or.inl hnC))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
  have hDcont : Continuous D := (PiLp.continuous_toLp 2 _).comp (continuous_pi hDcoord)
  have hgCont : Continuous (fun t => (Real.exp 2 * ‖kernel t‖) •
      (WithLp.toLp 2 (fun i => ‖D t i‖) : EuclideanSpace ℝ (GridCoordinate m B))) :=
    (hkCont.norm.const_mul _).smul
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (hDcoord i).norm)))
  have herr (j : ℕ) (hj : j ∈ C) (i : GridCoordinate m B) :
      ‖gridPrefixFourier cop P j i -
        ∫ t, ((((j : ℝ) + 1 / 2 : ℝ) : ℂ)^s t * kernel t) * D t i ∂μ‖ ≤ error i := by
    have hInt : (∫ t, ((((j : ℝ) + 1 / 2 : ℝ) : ℂ)^s t * kernel t) * D t i ∂μ) =
        productPerronIntegral P (gridCoefficient cop i) ((j : ℝ) + 1 / 2) c T := by
      change (∫ t in Set.Ioc (-T) T, _) = _
      rw [← intervalIntegral.integral_of_le hTle]
      unfold productPerronIntegral
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change _ = (1 / (2 * Real.pi) : ℂ) *
        (productDirichletPolynomial P (gridCoefficient cop i) (s t) *
          (((j : ℝ) + 1 / 2 : ℝ) : ℂ)^s t / s t)
      dsimp only [D, kernel]
      simp only [div_eq_mul_inv]
      ring
    rw [hInt, gridPrefixFourier, gridFourier_classMass_eq_sum, norm_sub_rev]
    simp only [mul_one]
    refine (trunc X P (gridCoefficient cop i) j hX (hcut j hj).1 (hcut j hj).2 hP).trans ?_
    calc
      _ ≤ (K / X^2) * (2 * gridRowMass cop P i.1) :=
        mul_le_mul_of_nonneg_left (gridCoefficient_mass_le cop P i) (by positivity)
      _ = error i := by change _ = (2 * K / X^2) * gridRowMass cop P i.1; ring
  have hv := l2_halfInteger_perron_sup_le (μ := μ) C hC (gridPrefixFourier cop P)
    D s kernel error (Real.exp_pos 2).le hs hpow (hgCont.intervalIntegrable (-T) T).1 herr
  refine hv.trans (add_le_add ?_ (gridRowError_norm_le cop P (by positivity)))
  change (∫ t in Set.Ioc (-T) T, (Real.exp 2 * ‖kernel t‖) * ‖D t‖) ≤ _
  rw [← intervalIntegral.integral_of_le hTle]
  have hcont := (hkCont.norm.const_mul (Real.exp 2)).mul hDcont.norm
  have hcont' : Continuous (fun t => (Real.exp 2 * ‖kernel t‖) * M) :=
    (hkCont.norm.const_mul (Real.exp 2)).mul continuous_const
  have hkNorm (t : ℝ) : ‖kernel t‖ = (1 / (2 * Real.pi)) * ‖(s t)⁻¹‖ := by
    dsimp only [kernel]
    rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  have hheight : 1 + Real.log (T / c) ≤ 4 * Real.log X := by
    have heq : T / c = X^3 * Real.log X := by simp [T, c, div_eq_mul_inv]
    rw [heq, Real.log_mul (pow_ne_zero _ hX₀.ne') hL₀.ne', Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos hL₀]
  calc
    _ ≤ ∫ t in (-T)..T, (Real.exp 2 * ‖kernel t‖) * M :=
      intervalIntegral.integral_mono_on hTle (hcont.intervalIntegrable _ _)
        (hcont'.intervalIntegrable _ _) (fun t ht =>
          mul_le_mul_of_nonneg_left (hDn t ht) (by positivity))
    _ = (Real.exp 2 * M / (2 * Real.pi)) * ∫ t in (-T)..T, ‖(s t)⁻¹‖ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hkNorm]
      ring
    _ ≤ (Real.exp 2 * M / (2 * Real.pi)) * (2 * (1 + Real.log (T / c))) :=
      mul_le_mul_of_nonneg_left (product_perron_vertical_l1 hc hT) (by positivity)
    _ ≤ (Real.exp 2 * M / (2 * Real.pi)) * (2 * (4 * Real.log X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hheight (by norm_num)) (by positivity)
    _ = _ := by ring

#print axioms gridPrefixFourier_sup_norm_le


/-- For disjoint prime bins, Dirichlet GRH bounds the Euclidean norm of the
sharp-prefix maxima over all reduced rows and all additive frequencies. -/
theorem primeBinProducts_gridPrefix_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (cop : m.Coprime B) (X : ℝ) (cutoffs : Finset ℕ) (hne : cutoffs.Nonempty)
        {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ι → ℕ),
        2 ≤ X → Real.exp 1 ≤ X →
        (∀ j ∈ cutoffs, X ≤ (j : ℝ) + 1 / 2 ∧ (j : ℝ) + 1 / 2 ≤ 2 * X) →
        (∀ n ∈ primeBinProducts A U, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) →
        (∀ i, 2 ≤ U i) → (∀ i, A i ≤ U i) →
        (Pairwise fun i j ↦ Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j))) →
        ‖(WithLp.toLp 2 (fun i : GridCoordinate m B => cutoffs.sup' hne
          (fun j => ‖gridPrefixFourier cop (primeBinProducts A U) j i‖)) :
              EuclideanSpace ℝ (GridCoordinate m B))‖ ≤
          Real.sqrt B * ((4 * Real.exp 2 / Real.pi) *
            ((∏ i, C * Real.sqrt (U i) * (1 + Real.log ((m * B : ℕ) *
              ((U i : ℝ) + X^3 + 2)))^3) * Real.log X) +
            (2 * K / X^2) * (primeBinProducts A U).card) := by
  obtain ⟨C, hC, hEnergy⟩ := primeBinProducts_gridFourier_energy_from_critical_line line
  obtain ⟨K, hK, hPrefix⟩ := gridPrefixFourier_sup_norm_le (m := m) (B := B)
  refine ⟨C, K, hC, hK, ?_⟩
  intro cop X cutoffs hne ι _ _ A U hX heX hcut hP hU hAU hdisj
  let P := primeBinProducts A U
  let H (t : ℝ) (i : ι) := C * Real.sqrt (U i) *
    (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + t + 2)))^3
  let M := Real.sqrt B * ∏ i, H (X^3) i
  have hq : (1 : ℝ) ≤ (m * B : ℕ) := by exact_mod_cast (NeZero.one_le : 1 ≤ m * B)
  have harg (t : ℝ) (ht : 0 ≤ t) (i : ι) :
      1 ≤ (m * B : ℕ) * ((U i : ℝ) + t + 2) := by
    apply one_le_mul_of_one_le_of_one_le hq
    linarith [Nat.cast_nonneg (α := ℝ) (U i)]
  have hH (t : ℝ) (ht : 0 ≤ t) (i : ι) : 0 ≤ H t i := by
    have hl := Real.log_nonneg (harg t ht i)
    dsimp [H]
    positivity
  have hX₀ : 0 ≤ X := by linarith
  have hM : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _)
    (prod_nonneg fun i _ => hH _ (by positivity) i)
  have hσ : 0 ≤ 1 / Real.log X := one_div_nonneg.mpr (Real.log_nonneg (by linarith))
  have hbound := hPrefix cop X P cutoffs hne M hX heX hM hcut hP
  refine (hbound ?_).trans_eq ?_
  · intro t ht
    have ht' : |t| ≤ X^3 := abs_le.mpr ht
    have hHle (i : ι) : H |t| i ≤ H (X^3) i := by
      have hl := Real.log_le_log (zero_lt_one.trans_le (harg _ (abs_nonneg t) i))
        (mul_le_mul_of_nonneg_left (show (U i : ℝ) + |t| + 2 ≤ (U i : ℝ) + X^3 + 2 by linarith)
          (by positivity : (0 : ℝ) ≤ (m * B : ℕ)))
      have hl₀ := Real.log_nonneg (harg _ (abs_nonneg t) i)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 3) (by positivity)
    have hprod : (∏ i, H |t| i) ≤ ∏ i, H (X^3) i := prod_le_prod (fun i _ => hH _ (abs_nonneg t) i) (fun i _ => hHle i)
    have hknown := hEnergy m B cop A U hU hAU hdisj (1 / Real.log X) t hσ
    change _ ≤ (B : ℝ) * (∏ i, H |t| i)^2 at hknown
    refine hknown.trans ?_
    dsimp only [M]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (prod_nonneg fun i _ => hH _ (abs_nonneg t) i) hprod 2) (by positivity)
  · dsimp only [M, H, P]
    ring

open Lean Elab Command in
run_cmd
  for ax in ← collectAxioms ``primeBinProducts_gridPrefix_from_critical_line do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "The sharp grid prefix theorem depends on unexpected axiom {ax}"

#print axioms primeBinProducts_gridPrefix_from_critical_line

end Cogentic.Randomized
