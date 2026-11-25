import Cogentic.ArchSolve
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.LinearAlgebra.Countable

/-! Supremum-norm separation and the covolume of the totally real unit lattice. -/

open NumberField InfinitePlace MeasureTheory
open scoped BigOperators NumberField Matrix

namespace Cogentic

/-- A non-sign integral unit in a totally real field has a real place at
which its logarithmic absolute value is at least half the logarithm of two. -/
theorem totally_real_unit_log_gap {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (u : (𝓞 K)ˣ) (nontriv : ¬ ((u : K) = 1 ∨ (u : K) = -1)) :
    ∃ w : InfinitePlace K, Real.log 2 / 2 ≤ Real.log (w (u : K)) := by
  classical
  let a : 𝓞 K := (u : 𝓞 K)^2-1
  have aeq : (a : K) = (u : K)^2-1 := by simp [a]
  have nz : a ≠ 0 := by
    intro h
    apply nontriv
    apply sq_eq_one_iff.mp
    have z : (a : K) = 0 := by rw [h]; rfl
    exact sub_eq_zero.mp (aeq ▸ z)
  have exists_place : ∃ w : InfinitePlace K, 1 ≤ w (a : K) := by
    by_contra! fail
    have h : 1 ≤ (NumberField.Units.dirichletUnitTheorem.w₀ : InfinitePlace K) (a : K) :=
      InfinitePlace.one_le_of_lt_one nz (fun {w} _ => fail w)
    exact (not_lt_of_ge h) (fail _)
  obtain ⟨w,large⟩ := exists_place
  let σ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have absValue (z : K) : w z = |σ z| := by
    rw [← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w), Real.norm_eq_abs]
  rw [aeq, absValue, map_sub, map_pow, map_one] at large
  have nonzero : σ (u : K) ≠ 0 := (map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u)
  have square : 2 ≤ (w (u : K))^2 := by
    rw [absValue, sq_abs]
    rcases le_abs.mp large with pos | neg
    · linarith
    · nlinarith [sq_pos_of_ne_zero nonzero]
  have log := Real.log_le_log (by norm_num : (0:ℝ)<2) square
  rw [Real.log_pow] at log
  norm_num only [Nat.cast_ofNat] at log
  exact ⟨w,by linarith⟩

/-- A discrete full lattice with no nonzero vector in the open sup ball of
radius r has covolume at least r raised to the number of coordinates. -/
theorem covolume_ge_gap_pow {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (r : ℝ) (hr : 0 < r)
    (gap : ∀ x : L, x ≠ 0 → r ≤ ‖(x : ι → ℝ)‖) :
    r^(Fintype.card ι) ≤ ZLattice.covolume L := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have fund : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  have bounded : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have vol : volume F = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact (ENNReal.ofReal_toReal bounded).symm
  by_contra! small
  have h : volume F * 2 ^ Module.finrank ℝ (ι → ℝ) < volume (Metric.ball (0 : ι → ℝ) r) := by
    rw [vol, Module.finrank_pi, Real.volume_pi_ball _ hr, mul_pow]
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2),
      ← ENNReal.ofReal_mul (ZLattice.covolume_pos L volume).le, mul_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (mul_nonneg (pow_nonneg zero_le_two _) (ZLattice.covolume_pos L volume).le)).mpr
      (mul_lt_mul_of_pos_left small (by positivity))
  let : Countable L.toAddSubgroup := (show Countable L from Finsupp.Countable.of_moduleFinite (R := ℤ))
  have fd : IsAddFundamentalDomain L.toAddSubgroup F volume := fund
  obtain ⟨x,nz,inside⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fd
    (s := Metric.ball (0 : ι → ℝ) r) (fun x hx => by simpa [Metric.mem_ball] using hx)
    (convex_ball 0 r) h
  exact (not_lt_of_ge (gap x nz)) (by simpa [Metric.mem_ball] using inside)


/-- An explicit regulator lower bound for every totally real number field.
Deleting the distinguished place costs at most the number of infinite places. -/
theorem totally_real_regulator_lower (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    ((Real.log 2/2)/(Fintype.card (InfinitePlace K) : ℝ)) ^ (NumberField.Units.rank K) ≤
      NumberField.Units.regulator K := by
  classical
  let d : ℝ := Fintype.card (InfinitePlace K)
  let g := (Real.log 2/2)/d
  have dp : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have gp : 0 < g := div_pos (by positivity) dp
  have gaps (y : NumberField.Units.unitLattice K) (nz : y ≠ 0) :
      g ≤ ‖(y : NumberField.Units.dirichletUnitTheorem.logSpace K)‖ := by
    obtain ⟨z,_,eq⟩ := y.prop
    let u : (𝓞 K)ˣ := z.toMul
    have coord : NumberField.Units.logEmbedding K (Additive.ofMul u) = y.val := eq
    have nontriv : ¬ ((u : K) = 1 ∨ (u : K) = -1) := by
      intro sign
      apply nz
      apply Subtype.ext
      rw [← coord]
      funext w
      have negOne : w.val (-1 : K) = 1 := by rw [← norm_embedding_eq, map_neg, map_one, norm_neg, norm_one]
      rcases sign with h | h <;> simp [NumberField.Units.dirichletUnitTheorem.logEmbedding_component, h, negOne]
    obtain ⟨w,hw⟩ := totally_real_unit_log_gap u nontriv
    have bound := NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le
      (x := u) (norm_nonneg _) le_rfl w
    rw [coord] at bound
    apply (div_le_iff₀ dp).mpr
    rw [mul_comm]
    exact hw.trans ((le_abs_self _).trans bound)
  have result := covolume_ge_gap_pow (NumberField.Units.unitLattice K) g gp gaps
  have card := Fintype.card_congr (NumberField.Units.equivFinRank K)
  rw [Fintype.card_fin] at card
  simpa only [← card, NumberField.Units.regulator] using result


/-- The exact normalized Helmert row used by the executable projection, with
valid indices 1 through d−1. -/
noncomputable def helmertCoordinate (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range j, x i) - (j : ℝ)*x j) / Real.sqrt ((j : ℝ)*(j+1))

/-- A polynomial norm-loss bound for the actual Helmert rows. The recurrence
uses differences from the initial coordinate and then uses the zero-sum equation. -/
theorem helmert_controls_sup (d : ℕ) (x : ℕ → ℝ) (M : ℝ) (hm : 0 ≤ M)
    (centered : ∑ i ∈ Finset.range d, x i = 0)
    (small : ∀ j, 0 < j → j < d → |helmertCoordinate x j| ≤ M) :
    ∀ j < d, |x j| ≤ 2*d*((d+1)*M) := by
  let B : ℝ := (d+1)*M
  have bp : 0 ≤ B := by dsimp [B]; positivity
  have diff (j : ℕ) (hj : 0 < j) (lt : j < d) : |(∑ i ∈ Finset.range j, x i) - j*x j| ≤ B := by
    have jp : (0:ℝ) < j := by exact_mod_cast hj
    have sp : 0 < Real.sqrt ((j:ℝ)*(j+1)) := by positivity
    have upper : Real.sqrt ((j:ℝ)*(j+1)) ≤ d+1 := by
      rw [Real.sqrt_le_left (by positivity)]
      have jd : (j:ℝ) ≤ d := by exact_mod_cast lt.le
      nlinarith [mul_self_le_mul_self jp.le jd]
    have row := small j hj lt
    simp only [helmertCoordinate, abs_div, abs_of_pos sp] at row
    exact ((div_le_iff₀ sp).mp row).trans (by simpa [B,mul_comm] using mul_le_mul_of_nonneg_left upper hm)
  have dev (j : ℕ) (lt : j < d) : |x j-x 0| ≤ j*B := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases j0 : j = 0
      · simp [j0]
      have jp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero j0
      have prefixBound : |∑ i ∈ Finset.range j, (x i-x 0)| ≤ (j : ℝ)*((j-1 : ℕ)*B) := by
        calc
          _ ≤ ∑ i ∈ Finset.range j, |x i-x 0| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range j, ((j-1 : ℕ):ℝ)*B := Finset.sum_le_sum fun i hi =>
            (ih i (Finset.mem_range.mp hi) ((Finset.mem_range.mp hi).trans lt)).trans
              (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_pred_of_lt (Finset.mem_range.mp hi)) bp)
          _ = _ := by simp
      have htmp := abs_sub (∑ i ∈ Finset.range j, (x i-x 0))
        ((∑ i ∈ Finset.range j, x i) - j*x j)
      have z : (∑ i ∈ Finset.range j, (x i-x 0)) -
          ((∑ i ∈ Finset.range j, x i) - j*x j) = j*(x j-x 0) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [z,abs_mul,abs_of_pos jp] at htmp
      have prev : ((j-1 : ℕ):ℝ) = (j : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [prev] at prefixBound
      apply le_of_mul_le_mul_left _ jp
      have bound := htmp.trans (add_le_add prefixBound (diff j (by omega) lt))
      nlinarith only [bound, mul_nonneg (sub_nonneg.mpr (show (1:ℝ) ≤ j by exact_mod_cast Nat.pos_of_ne_zero j0)) bp]
  intro j lt
  have dp : (0:ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt lt)
  have total : |∑ i ∈ Finset.range d, (x i-x 0)| ≤ d*(d*B) := by
    calc
      _ ≤ ∑ i ∈ Finset.range d, |x i-x 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range d, (d:ℝ)*B := Finset.sum_le_sum fun i hi =>
        (dev i (Finset.mem_range.mp hi)).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.mem_range.mp hi).le) bp)
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, centered, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    zero_sub,abs_neg,abs_mul,abs_of_pos dp] at total
  have base := le_of_mul_le_mul_left total dp
  have step := (dev j lt).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast lt.le : (j:ℝ) ≤ d) bp)
  have hh := abs_add_le (x j-x 0) (x 0)
  rw [sub_add_cancel] at hh
  change _ ≤ 2*d*B
  linarith


/-- A full real observation of an integer lattice with a certified gap has
a determinant bounded away from zero in every integer basis. -/
theorem observed_lattice_det_gap {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (base : Module.Basis ι ℤ L) (obs : L →ₗ[ℤ] (ι → ℝ))
    (full : Submodule.span ℝ (Set.range obs) = ⊤) (r : ℝ) (hr : 0 < r)
    (gap : ∀ z, obs z ≠ 0 → r ≤ ‖obs z‖) :
    r ^ Fintype.card ι ≤ |(Matrix.of (fun i j => obs (base j) i)).det| := by
  classical
  let v := fun j => obs (base j)
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply top_unique
    rw [← full]
    apply Submodule.span_le.mpr
    rintro _ ⟨z,rfl⟩
    rw [← base.sum_repr z, map_sum]
    apply Submodule.sum_mem
    intro j _
    have mem : v j ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨j,rfl⟩
    have sm := (Submodule.span ℝ (Set.range v)).smul_mem ((base.repr z j : ℤ) : ℝ) mem
    convert sm using 1
    calc
      _ = (base.repr z j) • obs (base j) := obs.map_smul _ _
      _ = _ := by ext i; simp [v,zsmul_eq_mul]
  have hi : LinearIndependent ℝ v := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, finrank_top,
      Module.finrank_pi]
  let b := basisOfPiSpaceOfLinearIndependent hi
  let G := Submodule.span ℤ (Set.range b)
  have sub : G ≤ LinearMap.range obs := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨base j,by simp [b,v]⟩
  have sep (x : G) (nz : x ≠ 0) : r ≤ ‖(x : ι → ℝ)‖ := by
    obtain ⟨z,eq⟩ := sub x.property
    rw [← eq]
    apply gap
    intro bad
    exact nz (Subtype.ext (eq.symm.trans bad))
  have lower := covolume_ge_gap_pow G r hr sep
  rw [ZLattice.covolume_eq_measure_fundamentalDomain G volume (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.volume_real_fundamentalDomain] at lower
  apply le_trans lower
  have matrix : Matrix.of (⇑b) = (Matrix.of (fun i j => obs (base j) i))ᵀ := by
    ext i j
    simp [b,v]
  rw [matrix, Matrix.det_transpose]

/-- The determinant of an observed minor is the lattice-basis determinant
times its integer index. This bounds both the numerical margin and the
denominator used by rational reconstruction. -/
theorem observed_minor_index_bound {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup L] [Module ℤ L] (base : Module.Basis ι ℤ L) (obs : L →ₗ[ℤ] (ι → ℝ))
    (full : Submodule.span ℝ (Set.range obs) = ⊤) (r : ℝ) (hr : 0 < r)
    (gap : ∀ z, obs z ≠ 0 → r ≤ ‖obs z‖) (v : ι → L) :
    r ^ Fintype.card ι * |((base.toMatrix v).det : ℝ)| ≤
      |(Matrix.of (fun i j => obs (v j) i)).det| := by
  classical
  let O := Matrix.of (fun i j => obs (base j) i)
  have factor : Matrix.of (fun i j => obs (v j) i) = O * ((Int.castRingHom ℝ).mapMatrix (base.toMatrix v)) := by
    ext i j
    change obs (v j) i = ∑ k, obs (base k) i * ((base.repr (v j) k : ℤ) : ℝ)
    have h := congrArg obs (base.sum_repr (v j))
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, mul_comm] using (congrFun h i).symm
  rw [factor,Matrix.det_mul, ← RingHom.map_det, abs_mul]
  apply mul_le_mul_of_nonneg_right (observed_lattice_det_gap base obs full r hr gap) (abs_nonneg _)


/-- Logs of an integral unit in a specified ordering of all real places. -/
noncomputable def orderedUnitLogs {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (places : Fin d ≃ InfinitePlace K) (u : (𝓞 K)ˣ) (j : ℕ) : ℝ :=
  if h : j < d then Real.log (places ⟨j,h⟩ (u : K)) else 0

/-- For every nonsign unit, any simultaneous upper bound for its normalized
Helmert coordinates exceeds this explicit inverse-polynomial gap. -/
theorem totally_real_helmert_gap {K : Type*} [Field K] [NumberField K] [IsTotallyReal K] {d : ℕ}
    (places : Fin d ≃ InfinitePlace K) (u : (𝓞 K)ˣ)
    (nontriv : ¬ ((u : K) = 1 ∨ (u : K) = -1)) (M : ℝ) (hm : 0 ≤ M)
    (bound : ∀ j, 0 < j → j < d → |helmertCoordinate (orderedUnitLogs places u) j| ≤ M) :
    Real.log 2 / (4*d*(d+1)) ≤ M := by
  classical
  have centered : ∑ j ∈ Finset.range d, orderedUnitLogs places u j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [orderedUnitLogs,Fin.is_lt,dif_pos,Fin.eta]
    rw [places.sum_comp (fun w => Real.log (w (u : K)))]
    simpa using NumberField.Units.sum_mult_mul_log u
  obtain ⟨w,hw⟩ := totally_real_unit_log_gap u nontriv
  let i := places.symm w
  have he : orderedUnitLogs places u i.val = Real.log (w (u : K)) := by simp [orderedUnitLogs,i]
  have high := hw.trans ((le_abs_self _).trans (he ▸ helmert_controls_sup d _ M hm centered bound i.val i.isLt))
  have dp : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private theorem unitClass_of_sign {K : Type*} [Field K] [NumberField K] (a : (𝓞 K)ˣ)
      (sign : (a : K) = 1 ∨ (a : K) = -1) : unitClass a = 0 := by
    change QuotientGroup.mk a = (1 : (𝓞 K)ˣ ⧸ NumberField.Units.torsion K)
    apply (QuotientGroup.eq_one_iff a).mpr
    apply (CommGroup.mem_torsion a).mpr
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨2,by decide,?_⟩
    apply Units.ext
    apply RingOfIntegers.ext
    change (a : K)^2 = 1
    exact sq_eq_one_iff.mpr sign

/-- If an observed paired unit respects the two ordered Helmert blocks, its
nonzero log vectors have a uniform gap in the actual projected coordinates. -/
theorem paired_helmert_observation_gap {K₁ K₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂] [Fintype ι] {d : ℕ}
    (p₁ : Fin d ≃ InfinitePlace K₁) (p₂ : Fin d ≃ InfinitePlace K₂)
    (obs : UnitClass K₁ × UnitClass K₂ →ₗ[ℤ] (ι → ℝ))
    (left right : Fin (d-1) → ι)
    (rows₁ : ∀ u v (j : Fin (d-1)), obs (unitClass u, unitClass v) (left j) =
      helmertCoordinate (orderedUnitLogs p₁ u) (j.val+1))
    (rows₂ : ∀ u v (j : Fin (d-1)), obs (unitClass u, unitClass v) (right j) =
      helmertCoordinate (orderedUnitLogs p₂ v) (j.val+1)) :
    ∀ z, z ≠ 0 → Real.log 2 / (4*d*(d+1)) ≤ ‖obs z‖ := by
  classical
  intro z hz
  obtain ⟨u,hu⟩ := QuotientGroup.mk_surjective (z.1.toMul)
  obtain ⟨v,hv⟩ := QuotientGroup.mk_surjective (z.2.toMul)
  have hzu : unitClass u = z.1 := congrArg Additive.ofMul hu
  have hzv : unitClass v = z.2 := congrArg Additive.ofMul hv
  have coord : (unitClass u, unitClass v) = z := Prod.ext hzu hzv
  have side : ¬ ((u : K₁)=1 ∨ (u : K₁) = -1) ∨ ¬ ((v : K₂)=1 ∨ (v : K₂) = -1) := by
    by_contra! h
    apply hz
    exact coord.symm.trans (Prod.ext (unitClass_of_sign u h.1) (unitClass_of_sign v h.2))
  rcases side with h|h
  · apply totally_real_helmert_gap p₁ u h _ (norm_nonneg _)
    intro j pos lt
    let i : Fin (d-1) := ⟨j-1,by omega⟩
    have q : i.val+1=j := by dsimp [i]; omega
    rw [← q, ← rows₁ u v i,coord,← Real.norm_eq_abs]
    exact norm_le_pi_norm _ _
  · apply totally_real_helmert_gap p₂ v h _ (norm_nonneg _)
    intro j pos lt
    let i : Fin (d-1) := ⟨j-1,by omega⟩
    have q : i.val+1=j := by dsimp [i]; omega
    rw [← q, ← rows₂ u v i,coord,← Real.norm_eq_abs]
    exact norm_le_pi_norm _ _

/-- Permutation expansion bounds a real determinant using only the largest
absolute entry. -/
theorem real_det_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ)
    (T : ℝ) (bound : ∀ i j, |U i j| ≤ T) :
    |U.det| ≤ (Fintype.card ι).factorial * T^(Fintype.card ι) := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, U (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm ι, T^(Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro σ _
      have one : |(Equiv.Perm.sign σ : ℤ)| = 1 := Int.isUnit_iff_abs_eq.mp (Equiv.Perm.sign σ).isUnit
      rw [abs_mul, ← Int.cast_abs, one, Int.cast_one, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ _i : ι, T := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => bound _ _)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]


private noncomputable def padProjection {d : ℕ} {ι : Type*} (pick : Fin d → ι) (j : ℕ) :
    (ι → ℝ) →ₗ[ℝ] ℝ := if h : j < d then LinearMap.proj (pick ⟨j,h⟩) else 0

private noncomputable def helmertForm {d : ℕ} {ι : Type*} (pick : Fin d → ι) (j : ℕ) :
    (ι → ℝ) →ₗ[ℝ] ℝ :=
  (Real.sqrt ((j:ℝ)*(j+1)))⁻¹ •
    ((∑ k ∈ Finset.range j, padProjection pick k) - (j:ℝ) • padProjection pick j)

private theorem helmertForm_apply {d : ℕ} {ι : Type*} (pick : Fin d → ι) (j : ℕ) (x : ι → ℝ) :
    helmertForm pick j x = helmertCoordinate (fun k => if h : k < d then x (pick ⟨k,h⟩) else 0) j := by
  have ev (k : ℕ) : padProjection pick k x = if h : k<d then x (pick ⟨k,h⟩) else 0 := by
    by_cases h : k<d <;> simp [padProjection,h]
  simp only [helmertForm, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply, ev,
    smul_eq_mul, helmertCoordinate,div_eq_inv_mul]

/-- The exact real matrix for both normalized Helmert blocks in an arbitrary
row ordering. Its columns use the same left-then-right raw embedding rows
as the marked Gram and relation descent. -/
noncomputable def pairedHelmertMatrix {d : ℕ} {ν : Type*}
    (code : ν → Fin (d-1) ⊕ Fin (d-1)) : Matrix ν (Fin d ⊕ Fin d) ℝ :=
  LinearMap.toMatrix' (LinearMap.pi (fun k => (code k).elim
    (fun j => helmertForm Sum.inl (j.val+1)) (fun j => helmertForm Sum.inr (j.val+1))))

/-- Real matrix application uses exactly the normalized Helmert formula on
the selected block, extended by zero outside its physical coordinates. -/
theorem pairedHelmertMatrix_apply {d : ℕ} {ν : Type*} (code : ν → Fin (d-1) ⊕ Fin (d-1))
    (x : Fin d ⊕ Fin d → ℝ) (k : ν) :
    (pairedHelmertMatrix code *ᵥ x) k = (code k).elim
      (fun j => helmertCoordinate (fun i => if h : i<d then x (Sum.inl ⟨i,h⟩) else 0) (j.val+1))
      (fun j => helmertCoordinate (fun i => if h : i<d then x (Sum.inr ⟨i,h⟩) else 0) (j.val+1)) := by
  rw [pairedHelmertMatrix,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply]
  cases code k <;> apply helmertForm_apply

/-- Adding one constant on each field's embedding block does not change its
Helmert projection. In particular this removes the target-power correction. -/
theorem pairedHelmertMatrix_constant {d : ℕ} {ν : Type*} (code : ν → Fin (d-1) ⊕ Fin (d-1))
    (c₁ c₂ : ℝ) :
    pairedHelmertMatrix code *ᵥ (Sum.elim (fun _ => c₁) (fun _ => c₂)) = 0 := by
  have common (c : ℝ) (j : Fin (d-1)) :
      helmertCoordinate (fun i : ℕ => if i<d then c else 0) (j.val+1) = 0 := by
    have jt := j.isLt
    have lt : j.val+1 < d := by omega
    have eq : ∑ i ∈ Finset.range (j.val+1), (if i<d then c else 0) =
        ∑ _i ∈ Finset.range (j.val+1), c :=
      Finset.sum_congr rfl (fun i h => if_pos ((Finset.mem_range.mp h).trans lt))
    simp [helmertCoordinate,eq,lt]
  funext k
  rw [pairedHelmertMatrix_apply]
  cases h : code k <;> simpa using common _ _

noncomputable def orderedRealEmbeddings {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    {d : ℕ} (p : Fin d ≃ InfinitePlace K) (i : Fin d) : K →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (p i))

private theorem orderedRealEmbeddings_abs {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    {d : ℕ} (p : Fin d ≃ InfinitePlace K) (i : Fin d) (a : K) : |orderedRealEmbeddings p i a| = p i a := by
  rw [← Real.norm_eq_abs]
  exact InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal (p i)) a

/-- The exact observation matrix used in the preceding determinant bounds
realizes the normalized Helmert formula at every ordered place. -/
theorem pairedHelmertMatrix_observation {K₁ K₂ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂] {d : ℕ}
    (p₁ : Fin d ≃ InfinitePlace K₁) (p₂ : Fin d ≃ InfinitePlace K₂) (code : ν → Fin (d-1) ⊕ Fin (d-1))
    (u : (𝓞 K₁)ˣ) (v : (𝓞 K₂)ˣ) (k : ν) :
    observeUnitPair (orderedRealEmbeddings p₁) (orderedRealEmbeddings p₂) (pairedHelmertMatrix code)
      (unitClass u, unitClass v) k = (code k).elim
        (fun j => helmertCoordinate (orderedUnitLogs p₁ u) (j.val+1))
        (fun j => helmertCoordinate (orderedUnitLogs p₂ v) (j.val+1)) := by
  rw [observeUnitPair_apply, pairedHelmertMatrix,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply]
  cases h : code k with
  | inl j => simp [helmertForm_apply,orderedRealEmbeddings_abs]; rfl
  | inr j => simp [helmertForm_apply,orderedRealEmbeddings_abs]; rfl

/-- A gap on every nonzero class makes the observation injective with
discrete image. Equal integer and ambient dimensions then force real span. -/
theorem observation_span_of_class_gap {ι L : Type*} [Fintype ι]
    [AddCommGroup L] [Module ℤ L] (b : Module.Basis ι ℤ L)
    (obs : L →ₗ[ℤ] (ι → ℝ)) (r : ℝ) (hr : 0 < r)
    (gap : ∀ z, z ≠ 0 → r ≤ ‖obs z‖) : Submodule.span ℝ (Set.range obs) = ⊤ := by
  classical
  have inj : Function.Injective obs := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    by_contra nz
    have small := gap z nz
    rw [hz,norm_zero] at small
    exact hr.not_ge small
  have disc : DiscreteTopology (LinearMap.range obs) := by
    refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball (0 : ι → ℝ) r, Metric.isOpen_ball,?_⟩
    ext y
    rw [Set.mem_preimage,mem_ball_zero_iff,Set.mem_singleton_iff]
    constructor
    · intro small
      obtain ⟨z,eq⟩ := y.property
      by_cases zero : z=0
      · apply Subtype.ext
        simpa [zero] using eq.symm
      · exact ((small.not_ge (eq ▸ gap z zero))).elim
    · rintro rfl
      simpa using hr
  have spanZ : Submodule.span ℤ (Set.range obs) = LinearMap.range obs :=
    Submodule.span_eq (LinearMap.range obs)
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range obs)) := spanZ ▸ disc
  apply Submodule.eq_top_of_finrank_eq
  change Set.finrank ℝ (Set.range obs) = _
  rw [Real.finrank_eq_int_finrank_of_discrete hd,Set.finrank,spanZ,LinearMap.finrank_range_of_inj inj,
    Module.finrank_eq_card_basis b,Module.finrank_pi]

/-- Determinant margin and integer reconstruction cap for any nonzero unit
minor in the exact two-field normalized projection. -/
theorem paired_helmert_minor_bounds {K₁ K₂ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂]
    [Fintype ν] [DecidableEq ν] {d : ℕ}
    (p₁ : Fin d ≃ InfinitePlace K₁) (p₂ : Fin d ≃ InfinitePlace K₂)
    (code : ν ≃ Fin (d-1) ⊕ Fin (d-1)) (b : Module.Basis ν ℤ (UnitClass K₁ × UnitClass K₂))
    (v : ν → UnitClass K₁ × UnitClass K₂) (nz : (b.toMatrix v).det ≠ 0)
    (T : ℝ) :
    let obs := observeUnitPair (orderedRealEmbeddings p₁) (orderedRealEmbeddings p₂) (pairedHelmertMatrix code)
    let U := Matrix.of (fun i j => obs (v j) i)
    let gap := Real.log 2 / (4*d*(d+1))
    (∀ i j, |U i j| ≤ T) →
    gap ^ Fintype.card ν ≤ |U.det| ∧
      |((b.toMatrix v).det : ℝ)| ≤ (Fintype.card ν).factorial * T ^ Fintype.card ν / gap ^ Fintype.card ν := by
  classical
  intro obs U gap bound
  have dp : 0 < d := (p₁.symm (Classical.arbitrary _)).isLt.trans_le' (Nat.zero_le _)
  have gp : 0 < gap := by dsimp [gap]; positivity
  have sep := paired_helmert_observation_gap p₁ p₂ obs (fun j => code.symm (Sum.inl j))
    (fun j => code.symm (Sum.inr j))
    (fun u v j => by simpa [obs] using pairedHelmertMatrix_observation p₁ p₂ code u v (code.symm (Sum.inl j)))
    (fun u v j => by simpa [obs] using pairedHelmertMatrix_observation p₁ p₂ code u v (code.symm (Sum.inr j)))
  have full := observation_span_of_class_gap b obs gap gp sep
  have lo := observed_minor_index_bound b obs full gap gp (fun z hz => sep z (fun h => hz (h ▸ obs.map_zero))) v
  have one : (1:ℝ) ≤ |((b.toMatrix v).det : ℝ)| := by exact_mod_cast Int.one_le_abs nz
  constructor
  · exact (le_mul_of_one_le_right (pow_nonneg gp.le _) one).trans lo
  · apply (le_div_iff₀ (pow_pos gp _)).mpr
    rw [mul_comm]
    exact lo.trans (real_det_entry_bound U T bound)

end Cogentic
