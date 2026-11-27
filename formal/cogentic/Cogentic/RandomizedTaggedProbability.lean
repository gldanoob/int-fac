import Cogentic.RandomizedTaggedSolver

namespace Cogentic.RandomizedTaggedDependency

open Cogentic.RandomizedGramMinor Cogentic.RandomizedGramRank

private noncomputable def failures {A : Type*} [Fintype A] (fails : A → Prop) : Finset A := by
  classical
  exact Finset.univ.filter fails

private theorem mem_failures {A : Type*} [Fintype A] {p : A → Prop} {x : A} :
    x ∈ failures p ↔ p x := by
  classical
  simp [failures]

private theorem card_failures_prod_le {A B : Type*} [Fintype A] [Fintype B]
    (fails : A → B → Prop) (bad : A → Prop) (q a b : ℕ)
    (hbad : (failures bad).card * q ≤ a * Fintype.card A)
    (hgood : ∀ x, ¬bad x → (failures (fails x)).card * q ≤ b * Fintype.card B) :
    (failures (fun p : A × B => fails p.1 p.2)).card * q ≤
      (a+b) * Fintype.card (A × B) := by
  classical
  let badPairs := (failures bad).product (Finset.univ : Finset B)
  let goodPairs := (failures (fun x => ¬bad x)).biUnion (fun x =>
    (failures (fails x)).map ⟨fun y => (x,y), fun _ _ h => congrArg Prod.snd h⟩)
  have hsubset : failures (fun p : A × B => fails p.1 p.2) ⊆ badPairs ∪ goodPairs := by
    rintro ⟨x,y⟩ h
    by_cases hx : bad x
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨mem_failures.mpr hx, Finset.mem_univ _⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x, mem_failures.mpr hx,
        Finset.mem_map.mpr ⟨y, mem_failures.mpr ((mem_failures (p := fun p : A × B => fails p.1 p.2)).mp h), rfl⟩⟩
  have hb : badPairs.card * q ≤ a * Fintype.card A * Fintype.card B := by
    simpa [badPairs, Finset.card_product, mul_right_comm] using
      Nat.mul_le_mul_right (Fintype.card B) hbad
  have hg : goodPairs.card * q ≤ b * Fintype.card A * Fintype.card B := by
    calc
      goodPairs.card*q ≤ (∑ x ∈ failures (fun x => ¬bad x), (failures (fails x)).card)*q := by
        apply Nat.mul_le_mul_right
        simpa [goodPairs] using (Finset.card_biUnion_le (s := failures (fun x => ¬bad x))
          (t := fun x => (failures (fails x)).map
            ⟨fun y => (x,y), fun _ _ h => congrArg Prod.snd h⟩))
      _ ≤ ∑ _x ∈ failures (fun x => ¬bad x), b * Fintype.card B := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun x hx => hgood x ((mem_failures (p := fun x => ¬bad x)).mp hx)
      _ ≤ b * Fintype.card A * Fintype.card B := by
        rw [Finset.sum_const, nsmul_eq_mul]
        calc
          (failures (fun x => ¬bad x)).card * (b * Fintype.card B) ≤
              Fintype.card A * (b * Fintype.card B) :=
            Nat.mul_le_mul_right _ (Finset.card_le_univ _)
          _ = _ := by ac_rfl
  calc
    _ ≤ (badPairs.card + goodPairs.card) * q :=
      Nat.mul_le_mul_right _ ((Finset.card_le_card hsubset).trans (Finset.card_union_le _ _))
    _ ≤ a * Fintype.card A * Fintype.card B + b * Fintype.card A * Fintype.card B := by
      rw [Nat.add_mul]
      exact Nat.add_le_add hb hg
    _ = _ := by rw [Fintype.card_prod, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]

variable {K Row Col Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K]
  [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
  [DecidableEq K] [Fintype K]

/-- A trial independently samples all the diagonal weights, the start and the left probe. -/
abbrev TaggedTrial (K Col : Type*) (N : ℕ) :=
  (Fin N → K) × (Col → K) × (Col → K)

/-- Failing trials of the actual tagged Euclidean solver. -/
noncomputable def badTaggedTrials {N : ℕ} (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) : Finset (TaggedTrial K Col N) :=
  failures fun t => ¬TaggedSolverSucceeds M H b
    (fun i => t.1 (numbering (Sum.inl i))) (fun j => t.1 (numbering (Sum.inr j))) t.2.1 t.2.2

/-- Conditional on a tagged binary dependency, the fraction of failed independent
trials is at most `(2 * rank + 1 + n) / |K|`, written after cross-multiplication.
The rank is that of the lifted constraint matrix and `n` is the column count. -/
theorem card_bad_tagged_trials_mul_field_le [Fintype Tag] {N : ℕ}
    (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K)
    (htag : ∃ w : Col → ZMod 2, M.mulVec w = 0 ∧ H.mulVec w ≠ 0) :
    (badTaggedTrials numbering M H b).card * Fintype.card K ≤
      (2 * (M.map (algebraMap (ZMod 2) K)).rank + 1 + Fintype.card Col) *
        Fintype.card (TaggedTrial K Col N) := by
  classical
  let A := M.map (algebraMap (ZMod 2) K)
  let q := Fintype.card K
  let n := Fintype.card Col
  let diagRow := fun (t : Fin N → K) i => t (numbering (Sum.inl i))
  let diagCol := fun (t : Fin N → K) j => t (numbering (Sum.inr j))
  let badDiag := fun t => (scaledGram A (diagRow t) (diagCol t)).charpoly.coeff (n-A.rank) = 0
  have : Nonempty Col := by
    obtain ⟨w, _, hw⟩ := htag
    have hne : w ≠ 0 := by
      intro hz
      exact hw (by simp [hz])
    obtain ⟨j, _⟩ := Function.ne_iff.mp hne
    exact ⟨j⟩
  have hdiag : (failures badDiag).card*q ≤ 2*A.rank*Fintype.card (Fin N → K) := by
    obtain ⟨I, J, e, hr, hdet⟩ := exists_rank_minor A
    have h := vanishing_fraction_le A I J e hdet numbering (Finset.univ : Finset K)
    rw [hr, Fintype.piFinset_univ, Finset.card_univ] at h
    have h' : ((failures badDiag).card : ℚ≥0) / (q : ℚ≥0)^N ≤
        (↑(2*A.rank) : ℚ≥0) / (q : ℚ≥0) := by
      unfold failures
      simpa only [badDiag, diagRow, diagCol, n, q, Finset.filter_congr_decidable] using h
    have hq : 0 < (q : ℚ≥0) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card K)
    have hmul := (div_le_div_iff₀ (pow_pos hq _) hq).mp h'
    rw [Fintype.card_fun, Fintype.card_fin]
    exact_mod_cast hmul
  unfold badTaggedTrials
  rw [add_assoc]
  refine card_failures_prod_le
    (fun t (xu : (Col → K) × (Col → K)) =>
      ¬TaggedSolverSucceeds M H b (diagRow t) (diagCol t) xu.1 xu.2)
    badDiag q (2*A.rank) (1+n) hdiag ?_
  intro t ht
  let S := taggedOperator M (diagRow t) (diagCol t)
  have hker : S.ker = A.mulVecLin.ker := (scaledGram_rank_and_ker A (diagRow t) (diagCol t) ht).2
  have hcomp : IsCompl S.ker S.range := by
    rw [hker]
    exact scaledGram_isCompl A (diagRow t) (diagCol t) ht
  let badStart := fun x => x ∈ badTaggedStarts S H hcomp
  have htagS : ∃ z ∈ S.ker, (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0 := by
    rw [hker]
    exact exists_tagged_extension_kernel M H htag
  have hb : (failures badStart).card*q ≤ 1 * Fintype.card (Col → K) := by
    have heq : failures badStart = badTaggedStarts S H hcomp := by
      ext x
      exact mem_failures
    rw [heq, one_mul]
    calc
      _ ≤ q^(n-1)*q := Nat.mul_le_mul_right q (card_bad_tagged_starts S H hcomp htagS)
      _ = _ := by
        rw [← pow_succ, Nat.sub_add_cancel (show 0 < n from Fintype.card_pos), Fintype.card_fun]
  refine card_failures_prod_le
    (fun x u => ¬TaggedSolverSucceeds M H b (diagRow t) (diagCol t) x u) badStart q 1 n hb ?_
  intro x hx
  obtain ⟨z, hz, w, hw, hsum, htz⟩ := tagged_start_components S H hcomp x hx
  have heq : failures (fun u => ¬TaggedSolverSucceeds M H b (diagRow t) (diagCol t) x u) =
      badTaggedSolverProbes M H b (diagRow t) (diagCol t) x := by
    ext u
    rw [mem_failures, badTaggedSolverProbes, Finset.mem_filter]
    simp
  rw [heq]
  exact card_bad_tagged_solver_probes M H b (diagRow t) (diagCol t) ht x z w hsum
    (hker ▸ hz) hw htz

/-- Uniform independent trials fail with probability at most
`(2 * M.rank + 1 + n) / |K|`, where the rank is over the binary field. -/
theorem bad_tagged_trials_fraction_le [Fintype Tag] {N : ℕ}
    (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K)
    (htag : ∃ w : Col → ZMod 2, M.mulVec w = 0 ∧ H.mulVec w ≠ 0) :
    ((badTaggedTrials numbering M H b).card : ℚ≥0) / Fintype.card (TaggedTrial K Col N) ≤
      (↑(2*M.rank + 1 + Fintype.card Col) : ℚ≥0) / Fintype.card K := by
  let f := algebraMap (ZMod 2) K
  let A := M.map f
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : A.rank ≤ M.rank := by
    obtain ⟨I, J, e, hr, hdet⟩ := exists_rank_minor A
    have hdet' : (selectedMinor M I J e).det ≠ 0 := by
      intro hz
      apply hdet
      change (f.mapMatrix (selectedMinor M I J e)).det = 0
      rw [← f.map_det, hz, map_zero]
    have hm := M.rank_submatrix_le (fun j : J => (e j : Row)) (Subtype.val : J → Col)
    change (selectedMinor M I J e).rank ≤ M.rank at hm
    rwa [Matrix.rank_of_det_ne_zero hdet', Fintype.card_coe, hr] at hm
  have hbound := card_bad_tagged_trials_mul_field_le numbering M H b htag
  have hbound' : (badTaggedTrials numbering M H b).card * Fintype.card K ≤
      (2*M.rank + 1 + Fintype.card Col) * Fintype.card (TaggedTrial K Col N) :=
    hbound.trans (by gcongr)
  have hq : 0 < (Fintype.card K : ℚ≥0) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card K)
  have ht : 0 < (Fintype.card (TaggedTrial K Col N) : ℚ≥0) := by
    have : Nonempty (TaggedTrial K Col N) := ⟨(0,0,0)⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (TaggedTrial K Col N))
  apply (div_le_div_iff₀ ht hq).mpr
  exact_mod_cast hbound'

end Cogentic.RandomizedTaggedDependency
