import Cogentic.ConstructionTarget
import Cogentic.EliminationUnits
import Cogentic.UnitGap

/-! The corrected target field units produced by actual integer elimination. -/

open NumberField Polynomial
open scoped BigOperators Matrix NumberField Polynomial
namespace Cogentic
open Marking

private theorem reduced_value {p : ℕ} (f : ℤ[X]) (r : ℤ) :
    f.eval₂ (Int.castRingHom (ZMod p)) (r : ZMod p) = ((f.eval r : ℤ) : ZMod p) :=
  Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod p)) r

private theorem residue_dvd_iff {p : ℕ} [NeZero p] (a : ℕ) (r : ℤ) :
    a%p = (r : ZMod p).val ↔ (p : ℤ) ∣ (a : ℤ)-r := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_natCast,sub_eq_zero,
    ← (ZMod.val_injective p).eq_iff,ZMod.val_natCast]

/-- All finite valuations of the actual particular solution vanish on the
left after multiplying by the target power, and on the right without it. -/
theorem computed_particular_unit {s : Input} {rel : Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : stageOne s = some rel) (solved : Elimination.stageTwo rel = some out) (side : Bool)
    {K : Type*} [Field K] [NumberField K] (θ : K)
    (root : (polynomial (s.coeffs side)).eval₂ (Int.castRingHom K) θ = 0)
    (targetClean : ∀ row ∈ s.rows, row.q = s.target → row ∈ s.clean) :
    let f := polynomial (s.coeffs side)
    let E := if side then 0 else out.scale
    (E ≠ 0 → (¬(s.target : ℤ) ∣ f.leadingCoeff) ∧ ∃ (n : ℕ) (rs : Fin n → ℤ),
      f.map (Int.castRingHom (ZMod s.target)) =
        (C f.leadingCoeff * ∏ j, (X-C (rs j))).map (Int.castRingHom (ZMod s.target))) →
    ∃ u : (𝓞 K)ˣ, (u : K) = (s.target : K)^E * ∏ j, ((rel.marks.get j : K)-θ)^(out.particular.get j) := by
  classical
  intro f E factor
  let a (j : Fin rel.marks.length) : ℤ := rel.marks.get j
  let c := out.particular.get
  have marks := stageOne_affine_rows marked side
  have ⟨_,inBase,targetEq,same,_⟩ := rows_and_guards marked
  have prime := (mem_base.mp inBase).2.1
  have solvedRows := (Elimination.stageTwo_verified solved).2.1
  have sz : ∑ j, c j = 0 := by
    simpa [c,Relations.matrix,Relations.rhs] using solvedRows 0
  suffices hs : ∀ (p : ℕ), p.Prime → ∀ r : ℤ, (p : ℤ) ∣ f.eval r →
      ∑ i, (if (p : ℤ) ∣ a i-r then c i else 0) = if p = s.target then -(E : ℤ) else 0 by
    simpa only [a,c,Int.cast_natCast] using unit_from_clean_affine_relations f θ root a
      (marks.nonzero_marks θ root) c sz s.target E prime marks.clean hs factor
  intro p pp r fr
  let : NeZero p := ⟨pp.ne_zero⟩
  let res := (r : ZMod p).val
  let row := Row.mk side p res
  by_cases active : (p=s.target ∧ E ≠ 0) ∨ ∃ j, (p : ℤ) ∣ a j-r
  · have listed : row ∈ s.clean := by
      rcases active with ⟨atTarget,_⟩|⟨j,hj⟩
      · apply targetClean row _ atTarget
        apply mem_rows.mpr
        refine ⟨(show p ∈ s.base by rwa [atTarget]),ZMod.val_lt _,?_⟩
        change f.eval₂ _ ((r : ZMod p).val : ZMod p) = 0
        rw [ZMod.natCast_zmod_val,reduced_value]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr fr
      · have div : (p:ℤ) ∣ f.eval (a j) := by
          simpa using dvd_add (dvd_trans hj (sub_dvd_eval_sub (a j) r f)) fr
        have mem := (stageOne_mark_primes marked side).2 p pp j div
        have hr : rel.marks.get j % p = res := (residue_dvd_iff _ r).mpr hj
        simpa only [row,hr] using mem
    have inRel : row ∈ rel.rows := same ▸ listed
    obtain ⟨idx,eq⟩ := List.mem_iff_get.mp inRel
    have this := solvedRows idx.succ
    change (∑ j, (if rel.marks.get j % (rel.rows.get idx).q = (rel.rows.get idx).r then (1:ℤ) else 0)*c j) =
      -((out.scale:ℕ):ℤ)*(if !(rel.rows.get idx).second && (rel.rows.get idx).q == rel.target then 1 else 0) at this
    rw [eq,targetEq] at this
    simp only [row,res,residue_dvd_iff,ite_mul,one_mul,zero_mul] at this
    cases side <;> by_cases e : p=s.target <;> simpa [E,a,e] using this
  · have none (j) : ¬ (p : ℤ) ∣ a j-r := fun h => active (.inr ⟨j,h⟩)
    simp only [if_neg (none _), Finset.sum_const_zero]
    by_cases e : p=s.target
    · have zero : E=0 := by by_contra nz; exact active (.inl ⟨e,nz⟩)
      simp [e,zero]
    · simp [e]

/-- A reduction possessing as many distinct roots as the integer degree
supplies both the good leading coefficient and a complete residue factorization. -/
private theorem split_from_reduced_roots (f : ℤ[X]) (ell : ℕ) (hp : ell.Prime) (degree : 0 < f.natDegree) :
    letI : Fact ell.Prime := ⟨hp⟩
    let F := f.map (Int.castRingHom (ZMod ell))
    F.roots.card = f.natDegree → F.roots.Nodup →
    (¬ (ell : ℤ) ∣ f.leadingCoeff) ∧ ∃ (m : ℕ) (rs : Fin m → ℤ),
      F = (C f.leadingCoeff * ∏ j, (X-C (rs j))).map (Int.castRingHom (ZMod ell)) := by
  classical
  let : Fact ell.Prime := ⟨hp⟩
  intro F card nodup
  have nz : F ≠ 0 := fun h => by rw [h,roots_zero,Multiset.card_zero] at card; omega
  have deq : F.natDegree = f.natDegree := natDegree_map_le.antisymm (card ▸ F.card_roots')
  have leading : (f.leadingCoeff : ZMod ell) ≠ 0 := by
    have eq : (f.leadingCoeff : ZMod ell) = F.leadingCoeff := by
      rw [leadingCoeff,leadingCoeff,deq]
      exact (coeff_map (p:=f) (Int.castRingHom (ZMod ell)) _).symm
    exact eq ▸ leadingCoeff_ne_zero.mpr nz
  have good : ¬ (ell:ℤ) ∣ f.leadingCoeff := fun h => leading ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr h)
  let xs := F.roots.toList
  let rs (i : Fin xs.length) : ℤ := (xs.get i).val
  have rcast (i : Fin xs.length) : (rs i : ZMod ell) = xs.get i := by simp [rs]
  refine ⟨good,xs.length,rs,target_factorization_of_distinct_roots ell hp f good rs ?_ ?_ ?_⟩
  · simp [xs,card]
  · intro i j e
    change (rs i : ZMod ell) = (rs j : ZMod ell) at e
    rw [rcast,rcast] at e
    have un : xs.Nodup := by change ((xs : Multiset (ZMod ell))).Nodup; simpa [xs] using nodup
    exact un.get_inj_iff.mp e
  · intro i
    have member := xs.get_mem i
    have hit : F.IsRoot (xs.get i) := (mem_roots nz).mp (Multiset.mem_toList.mp member)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    rw [← reduced_value,rcast]
    exact (Polynomial.eval_map ..).symm.trans hit

/-- The CRT target splitting and all finite-row checks are supplied by the
actual construction and executable stages. The resulting target units use
the same particular coefficient vector in both number fields. -/
theorem constructed_particular_units {N ell u₀ u₁ v₀ v₁ : ℕ}
    (large : 3 ≤ Fixed.d (N.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1)))
    {rel : Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : stageOne (TryPair.fixedInput N ell (Construction.construct N ell u₀ u₁ v₀ v₁)) = some rel)
    (solved : Elimination.stageTwo rel = some out) {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] (θ₁ : K₁) (θ₂ : K₂) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell u₀ u₁ v₀ v₁)
    (polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0 →
    (polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0 →
    (∃ u : (𝓞 K₁)ˣ, (u : K₁) = (ell : K₁)^out.scale *
      ∏ j, ((rel.marks.get j : K₁)-θ₁)^(out.particular.get j)) ∧
    (∃ v : (𝓞 K₂)ˣ, (v : K₂) = ∏ j, ((rel.marks.get j : K₂)-θ₂)^(out.particular.get j)) := by
  intro s root₁ root₂
  have prime := (mem_dyadicTargets.mp target).1
  let : Fact ell.Prime := ⟨prime⟩
  have cleaned := Construction.target_rows_clean large target u₀ u₁ v₀ v₁
  have clean : ∀ row ∈ s.rows, row.q = s.target → row ∈ s.clean := fun r h e => (cleaned r h e).2
  have degree := (Construction.constructed_rational_fields large target u₀ u₁ v₀ v₁).1.1
  have roots := Construction.target_roots large target u₀ u₁ v₀ v₁
  change (polynomial s.first).natDegree = Fixed.d (N.log2+1) at degree
  have inf := split_from_reduced_roots (polynomial s.first) ell prime
    (by rw [degree]; omega) (roots.1.trans degree.symm) roots.2.1
  constructor
  · exact computed_particular_unit marked solved false θ₁ root₁ clean (fun _ => inf)
  · simpa using computed_particular_unit marked solved true θ₂ root₂ clean (by simp)


/-- The multiplier ell^E in the left field contributes the same raw
logarithm at every embedding. Its Helmert projection vanishes exactly. -/
theorem corrected_target_observation {K₁ K₂ κ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype κ] {d : ℕ}
    (σ₁ : Fin d → K₁ →+* ℝ) (σ₂ : Fin d → K₂ →+* ℝ)
    (code : ν → Fin (d-1) ⊕ Fin (d-1)) (a₁ : κ → K₁) (a₂ : κ → K₂)
    (ha₁ : ∀ j, a₁ j ≠ 0) (ha₂ : ∀ j, a₂ j ≠ 0) (A : ℝ) (hA : 0 < A)
    (c : κ → ℤ) (sz : ∑ j, c j = 0) (ell E : ℕ) (ep : 0 < ell)
    (u : (𝓞 K₁)ˣ) (v : (𝓞 K₂)ˣ) (hu : (u : K₁) = (ell:K₁)^E*∏ j, (a₁ j)^(c j))
    (hv : (v : K₂) = ∏ j, (a₂ j)^(c j)) :
    observeUnitPair σ₁ σ₂ (pairedHelmertMatrix code) (unitClass u,unitClass v) =
      (pairedHelmertMatrix code * markLogs σ₁ σ₂ a₁ a₂ A) *ᵥ (fun j => (c j : ℝ)) := by
  classical
  let z := Sum.elim (fun _ : Fin d => (E:ℝ)*Real.log ell) (fun _ : Fin d => (0:ℝ))
  let M := markLogs σ₁ σ₂ a₁ a₂ A
  have prodNe : (∏ j, (a₁ j)^(c j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (ha₁ j))
  have el : (0:ℝ) < ell := by exact_mod_cast ep
  have raw : Sum.elim (fun i => Real.log |σ₁ i (u : K₁)|) (fun i => Real.log |σ₂ i (v : K₂)|) =
      z + M *ᵥ (fun j => (c j : ℝ)) := by
    funext k
    rcases k with i|i
    · have logs := normalized_log_relation (σ₁ i) a₁ ha₁ A hA c sz
      change Real.log |σ₁ i (u : K₁)| = (E:ℝ)*Real.log ell + _
      rw [hu,map_mul,map_pow,map_natCast,abs_mul,abs_pow,abs_of_nonneg el.le,
        Real.log_mul (pow_ne_zero _ el.ne') (abs_ne_zero.mpr ((_root_.map_ne_zero (σ₁ i)).mpr prodNe)),Real.log_pow]
      exact congrArg (fun y => (E:ℝ)*Real.log ell + y) logs.symm
    · change Real.log |σ₂ i (v : K₂)| = 0 + _
      rw [hv,zero_add]
      exact (normalized_log_relation (σ₂ i) a₂ ha₂ A hA c sz).symm
  rw [observeUnitPair_apply,raw,Matrix.mulVec_add,pairedHelmertMatrix_constant,zero_add,Matrix.mulVec_mulVec]

/-- The corrected target pair is observed by the exact normalized marked
matrix on the particular vector returned by the executable second stage. -/
theorem constructed_target_observation {N ell u₀ u₁ v₀ v₁ : ℕ}
    (large : 3 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1)))
    {rel : Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : stageOne (TryPair.fixedInput N ell (Construction.construct N ell u₀ u₁ v₀ v₁)) = some rel)
    (solved : Elimination.stageTwo rel = some out) {K₁ K₂ ν : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] (θ₁ : K₁) (θ₂ : K₂)
    (σ₁ : Fin (Fixed.d (N.log2+1)) → K₁ →+* ℝ) (σ₂ : Fin (Fixed.d (N.log2+1)) → K₂ →+* ℝ)
    (code : ν → Fin (Fixed.d (N.log2+1)-1) ⊕ Fin (Fixed.d (N.log2+1)-1)) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell u₀ u₁ v₀ v₁)
    let a₁ := fun j : Fin rel.marks.length => (rel.marks.get j : K₁)-θ₁
    let a₂ := fun j : Fin rel.marks.length => (rel.marks.get j : K₂)-θ₂
    (polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0 →
    (polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0 →
    ∃ (u : (𝓞 K₁)ˣ) (v : (𝓞 K₂)ˣ),
      (u : K₁) = (ell : K₁)^out.scale * ∏ j, (a₁ j)^(out.particular.get j) ∧
      (v : K₂) = ∏ j, (a₂ j)^(out.particular.get j) ∧
      observeUnitPair σ₁ σ₂ (pairedHelmertMatrix code) (unitClass u,unitClass v) =
        (pairedHelmertMatrix code * markLogs σ₁ σ₂ a₁ a₂ (Fixed.A (N.log2+1))) *ᵥ
          (fun j => (out.particular.get j : ℝ)) := by
  intro s a₁ a₂ r₁ r₂
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := constructed_particular_units large target marked solved θ₁ θ₂ r₁ r₂
  refine ⟨u,v,hu,hv,corrected_target_observation σ₁ σ₂ code a₁ a₂ ?_ ?_ _ ?_ out.particular.get ?_
    ell out.scale (mem_dyadicTargets.mp target).1.pos u v hu hv⟩
  · intro j
    simpa only [a₁,Int.cast_natCast] using (stageOne_affine_rows marked false).nonzero_marks θ₁ r₁ j
  · intro j
    simpa only [a₂,Int.cast_natCast] using (stageOne_affine_rows marked true).nonzero_marks θ₂ r₂ j
  · unfold Fixed.A; positivity
  · simpa [Relations.matrix,Relations.rhs] using (Elimination.stageTwo_verified solved).2.1 0

end Cogentic
