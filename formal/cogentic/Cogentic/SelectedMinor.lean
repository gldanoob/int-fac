import Cogentic.UnitMinor
import Cogentic.Concrete

/-! Transfer of a genuine selected minor to the increasing list searched by
the deterministic candidate routine. -/

open NumberField
open scoped Matrix BigOperators NumberField
namespace Cogentic

/-- Consecutive left and right Helmert rows, in the exact order used by
Concrete.markColumns. -/
def concreteRowCode (d : ℕ) : Fin (2*d-2) ≃ Fin (d-1) ⊕ Fin (d-1) :=
  (finCongr (show 2*d-2 = (d-1)+(d-1) by omega)).trans finSumFinEquiv.symm

theorem concreteRowCode_elim {α : Type*} (d : ℕ) (f : Bool → ℕ → α) (i : Fin (2*d-2)) :
    ((concreteRowCode d) i).elim (fun j => f false (j.val+1)) (fun j => f true (j.val+1)) =
      f (decide (d-1 ≤ i.val)) (i.val%(d-1)+1) := by
  cases h : concreteRowCode d i with
  | inl j =>
    have e := (concreteRowCode d).eq_symm_apply.mpr h
    have val : i.val = j.val := congrArg Fin.val e
    simp [val,Nat.not_le_of_lt j.isLt,Nat.mod_eq_of_lt j.isLt]
  | inr j =>
    have e := (concreteRowCode d).eq_symm_apply.mpr h
    have val : i.val = d-1+j.val := congrArg Fin.val e
    simp [val,Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt]

/-- The canonical paired Dirichlet basis with the concrete archimedean row
index type. Its ordering is independent of the selected columns. -/
noncomputable def concreteUnitBasis {K₁ K₂ : Type*} [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    {d : ℕ} (p₁ : Fin d ≃ InfinitePlace K₁) (p₂ : Fin d ≃ InfinitePlace K₂) :
    Module.Basis (Fin (2*d-2)) ℤ (UnitClass K₁ × UnitClass K₂) :=
  (pairedUnitBasis K₁ K₂).reindex
    (((orderedUnitRank p₁).sumCongr (orderedUnitRank p₂)).trans (concreteRowCode d).symm)

/-- An arbitrary injection into the free columns has an increasing sublist
of the numbered columns and an explicit equivalence with its original index. -/
theorem selection_to_sublist {dim free : ℕ} (pick : Fin dim → Fin free) (injective : Function.Injective pick) :
    ∃ idx : List (Fin free), idx.Sublist (List.finRange free) ∧
    ∃ size : idx.length = dim, ∃ e : Fin dim ≃ Fin dim,
      ∀ j, ((Vector.ofFn idx.get).cast size).get j = pick (e j) := by
  classical
  let idx := (List.finRange free).filter (fun j => decide (∃ i, pick i=j))
  have mem (j : Fin free) : j ∈ idx ↔ ∃ i, pick i=j := by simp [idx]
  let loc (i : Fin dim) : Fin idx.length :=
    ⟨idx.idxOf (pick i),List.idxOf_lt_length_iff.mpr ((mem _).mpr ⟨i,rfl⟩)⟩
  have atLoc (i) : idx.get (loc i) = pick i := List.idxOf_get _
  have bij : Function.Bijective loc := by
    constructor
    · intro i j h
      apply injective
      rw [← atLoc i,← atLoc j,h]
    · intro j
      obtain ⟨i,eq⟩ := (mem _).mp (idx.get_mem j)
      exact ⟨i,((List.nodup_finRange free).filter _).get_inj_iff.mp ((atLoc i).trans eq)⟩
  let map := Equiv.ofBijective loc bij
  have len : idx.length = dim := by simpa using Fintype.card_congr map.symm
  let e := (finCongr len.symm).trans map.symm
  refine ⟨idx,List.filter_sublist,len,e,?_⟩
  intro j
  have eq := atLoc (e j)
  have aligned : loc (e j) = Fin.cast len.symm j := map.apply_symm_apply _
  rw [aligned] at eq
  rw [Vector.get_cast]
  simpa only [Vector.get_eq_getElem,Vector.getElem_ofFn] using eq

private theorem free_lt_marks {rel : Marking.Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (solved : Elimination.stageTwo rel = some out) (pos : 0 < out.free) : out.free < rel.marks.length := by
  classical
  have dirs := (Elimination.stageTwo_verified solved).2.2.1
  have inj : Function.Injective out.position := by
    intro i j eq
    by_contra neq
    have e := congrArg (fun a => (out.directions.get i).get a) eq
    rw [(dirs i).2.2,(dirs i).2.2,if_pos rfl,if_neg (Ne.symm neq)] at e
    exact (Int.natCast_ne_zero.mpr (dirs i).1.ne') e
  have le : out.free ≤ rel.marks.length := by simpa using Fintype.card_le_of_injective _ inj
  apply lt_of_le_of_ne le
  intro same
  have sur := (Fintype.bijective_iff_injective_and_card out.position).mpr ⟨inj,by simpa using same⟩
  let map := Equiv.ofBijective out.position sur
  let k : Fin out.free := ⟨0,pos⟩
  have null : ∑ j, (out.directions.get k).get j = 0 := by
    simpa [Marking.Relations.matrix] using (dirs k).2.1 0
  rw [← map.sum_comp (fun j => (out.directions.get k).get j)] at null
  change ∑ j, (out.directions.get k).get (out.position j) = 0 at null
  simp only [(dirs k).2.2,Finset.sum_ite_eq',Finset.mem_univ,if_true] at null
  exact (Int.natCast_ne_zero.mpr (dirs k).1.ne') null

/-- On a successful first and second stage, full archimedean kernel span
supplies an actual increasing enumerated minor, both free-dimension guards,
and the associated genuine paired unit products and exact observations. -/
theorem computed_sorted_unit_minor {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂]
    {s : Marking.Input} {rel : Marking.Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : Marking.stageOne s = some rel) (solved : Elimination.stageTwo rel = some out)
    (p₁ : Fin s.degree ≃ InfinitePlace K₁) (p₂ : Fin s.degree ≃ InfinitePlace K₂)
    (θ₁ : K₁) (θ₂ : K₂)
    (root₁ : (Marking.polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0)
    (root₂ : (Marking.polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0) :
    let n := 2*s.degree-2
    let a₁ := fun j : Fin rel.marks.length => (rel.marks.get j : K₁)-θ₁
    let a₂ := fun j : Fin rel.marks.length => (rel.marks.get j : K₂)-θ₂
    let σ₁ := orderedRealEmbeddings p₁
    let σ₂ := orderedRealEmbeddings p₂
    let H := pairedHelmertMatrix (concreteRowCode s.degree)
    let M := H * markLogs σ₁ σ₂ a₁ a₂ s.A
    let basis := concreteUnitBasis p₁ p₂
    Submodule.span ℝ {y : Fin n → ℝ | ∃ z : Fin rel.marks.length → ℤ,
      (∀ i, ∑ j, rel.matrix i j*z j=0) ∧ y = M *ᵥ (fun j => (z j : ℝ))} = ⊤ →
    (out.free < rel.marks.length ∧ n ≤ out.free) ∧
    ∃ idx : List (Fin out.free), idx.Sublist (List.finRange out.free) ∧
      ∃ len : idx.length = n, let selected := (Vector.ofFn idx.get).cast len
      ∃ (u : Fin n → (𝓞 K₁)ˣ) (v : Fin n → (𝓞 K₂)ˣ),
        (∀ k, (u k : K₁) = ∏ j, (a₁ j)^((out.directions.get (selected.get k)).get j)) ∧
        (∀ k, (v k : K₂) = ∏ j, (a₂ j)^((out.directions.get (selected.get k)).get j)) ∧
        (basis.toMatrix (fun k => (unitClass (u k),unitClass (v k)))).det ≠ 0 ∧
        ∀ k, observeUnitPair σ₁ σ₂ H (unitClass (u k),unitClass (v k)) =
          M *ᵥ (fun j => ((out.directions.get (selected.get k)).get j : ℝ)) := by
  classical
  intro n a₁ a₂ σ₁ σ₂ H M basis sp
  obtain ⟨_,_,degree,_,ap,_⟩ := (Marking.rows_and_guards marked).1
  have hA : 0 < (s.A:ℝ) := by exact_mod_cast (show 0 < s.A by omega)
  have rows₁ := stageOne_affine_rows marked false
  have rows₂ := stageOne_affine_rows marked true
  have dirs := (Elimination.stageTwo_verified solved).2.2.1
  let D := fun k j => (out.directions.get k).get j
  have span := stageTwo_observation_span solved M sp
  obtain ⟨pick,u,v,hu,hv,nz⟩ := select_clean_unit_columns_in_basis basis σ₁ σ₂
    (fun j : Fin rel.marks.length => (rel.marks.get j : ℤ)) rel.matrix _ _ θ₁ θ₂ root₁ root₂ rows₁ rows₂
    0 (fun _ => rfl) _ hA H D (fun i => (dirs i).2.1) (by simpa only [Int.cast_natCast] using span)
  have hp (k) : (u k : K₁) = ∏ j, (a₁ j)^(D (pick k) j) := by simpa only [a₁,Int.cast_natCast] using hu k
  have hq (k) : (v k : K₂) = ∏ j, (a₂ j)^(D (pick k) j) := by simpa only [a₂,Int.cast_natCast] using hv k
  let cls := fun k => (unitClass (u k),unitClass (v k))
  have inj : Function.Injective pick := by
    intro i j e
    by_contra ne
    have ueq : u i = u j := NumberField.Units.coe_injective _ ((hp i).trans (e ▸ (hp j).symm))
    have veq : v i = v j := NumberField.Units.coe_injective _ ((hq i).trans (e ▸ (hq j).symm))
    exact nz (Matrix.det_zero_of_column_eq ne (fun k => by simp [Module.Basis.toMatrix_apply,ueq,veq]))
  have le : n ≤ out.free := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective pick inj
  have np : 0 < n := by dsimp [n]; omega
  obtain ⟨idx,sub,len,e,atIndex⟩ := selection_to_sublist pick inj
  refine ⟨⟨free_lt_marks solved (np.trans_le le),le⟩,idx,sub,len,?_⟩
  intro selected
  refine ⟨u ∘ e,v ∘ e,?_,?_,?_,?_⟩
  · intro k; rw [atIndex]; exact hp (e k)
  · intro k; rw [atIndex]; exact hq (e k)
  · have perm : basis.toMatrix (fun k => (unitClass ((u ∘ e) k),unitClass ((v ∘ e) k))) =
        (basis.toMatrix cls).submatrix (Equiv.refl _) e := rfl
    rw [perm]
    intro zero
    have eq := Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl _) e (basis.toMatrix cls)
    rw [zero,abs_zero] at eq
    exact nz (abs_eq_zero.mp eq.symm)
  · intro k
    rw [atIndex]
    have bal : ∑ j, D (pick (e k)) j = 0 := by
      simpa [D,Marking.Relations.matrix] using (dirs (pick (e k))).2.1 0
    apply observed_unit_relations σ₁ σ₂ a₁ a₂ _ _ _ hA H _ bal _ _ (hp _) (hq _)
    · intro j; simpa only [a₁,Int.cast_natCast] using rows₁.nonzero_marks θ₁ root₁ j
    · intro j; simpa only [a₂,Int.cast_natCast] using rows₂.nonzero_marks θ₂ root₂ j

end Cogentic
