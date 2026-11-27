import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

variable {ι κ Ω K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The designated vector lies outside the span of the other vectors. -/
def LeaveOneOutMiss (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (v : ι → V) (i : ι) : Prop :=
  v i ∉ Submodule.span K (v '' (Set.univ \ {i}))

/-- A vector that can be deleted only at the cost of losing span is
independent of all other vectors with that property. -/
theorem linearIndepOn_leaveOneOutMiss (v : ι → V) :
    LinearIndepOn K v {i | LeaveOneOutMiss K v i} := by
  apply linearIndepOn_iff_notMem_span.mpr
  intro i hi hmem
  exact hi ((Submodule.span_mono (Set.image_mono (Set.sdiff_subset_sdiff_left (Set.subset_univ _)))) hmem)

/-- A family in a vector space of dimension `d` has at most `d` indices
whose vector is outside the span of all the other vectors. -/
theorem card_leaveOneOutMiss_le_finrank [Fintype ι] [Module.Finite K V] (v : ι → V) :
    (by classical exact (univ.filter (LeaveOneOutMiss K v)).card) ≤ Module.finrank K V := by
  classical
  have hind : LinearIndepOn K v ↑(univ.filter (LeaveOneOutMiss K v)) := by
    simpa only [coe_filter, mem_univ, true_and] using linearIndepOn_leaveOneOutMiss (K := K) v
  have hcard := hind.fintype_card_le_finrank
  change Fintype.card ↥(univ.filter (LeaveOneOutMiss K v)) ≤ _ at hcard
  simpa only [Fintype.card_coe] using hcard

private theorem leaveOneOutMiss_comp_equiv (v : ι → V) (e : κ ≃ ι) (i : κ) :
    LeaveOneOutMiss K (v ∘ e) i ↔ LeaveOneOutMiss K v (e i) := by
  have himage : (v ∘ e) '' (Set.univ \ {i}) = v '' (Set.univ \ {e i}) := by
    ext y
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and,
      Function.comp_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, fun h ↦ hj (e.injective h), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e.symm j, fun h ↦ hj (by simpa using congrArg e h), by simp⟩
  unfold LeaveOneOutMiss
  rw [himage]
  rfl

/-- Tuples for which the designated draw misses the span of all other draws. -/
noncomputable def missedSpanTuples (K : Type*) {ι Ω V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (row : Ω → V) (i : ι) : Finset (ι → Ω) := by
  classical
  exact univ.filter (fun draw ↦ LeaveOneOutMiss K (row ∘ draw) i)

/-- Counting all independent uniform sample tuples gives the probability
bound after cross multiplication. The designated coordinate is arbitrary. -/
theorem uniform_leaveOneOutMiss_count_le [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [Module.Finite K V] (row : Ω → V) (i : ι) :
    (missedSpanTuples K row i).card * Fintype.card ι ≤
      Module.finrank K V * Fintype.card (ι → Ω) := by
  classical
  let miss (draw : ι → Ω) (j : ι) : ℕ := if LeaveOneOutMiss K (row ∘ draw) j then 1 else 0
  have hsymm (j : ι) : (∑ draw, miss draw i) = ∑ draw, miss draw j := by
    let e := Equiv.swap j i
    let E := Equiv.arrowCongr e.symm (Equiv.refl Ω)
    apply Fintype.sum_equiv E
    intro draw
    have hcomp : row ∘ E draw = (row ∘ draw) ∘ e := by rfl
    have hei : e j = i := Equiv.swap_apply_left j i
    unfold miss
    rw [hcomp, leaveOneOutMiss_comp_equiv, hei]
  have hpointwise (draw : ι → Ω) : ∑ j, miss draw j ≤ Module.finrank K V := by
    simpa only [miss, Finset.sum_boole, Nat.cast_id] using
      card_leaveOneOutMiss_le_finrank (K := K) (row ∘ draw)
  have hcount : (missedSpanTuples K row i).card = ∑ draw, miss draw i := by
    simp [missedSpanTuples, miss]
  calc
    _ = ∑ _j : ι, ∑ draw, miss draw i := by simp [hcount, Nat.mul_comm]
    _ = ∑ j, ∑ draw, miss draw j := sum_congr rfl fun j _ ↦ hsymm j
    _ = ∑ draw, ∑ j, miss draw j := sum_comm
    _ ≤ ∑ _draw : ι → Ω, Module.finrank K V := sum_le_sum fun draw _ ↦ hpointwise draw
    _ = _ := by simp [Nat.mul_comm]

/-- The probability that an independent uniform draw misses the span of the
other draws is at most the dimension divided by the total number of draws. -/
theorem uniform_leaveOneOutMiss_probability_le [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [Nonempty Ω] [Module.Finite K V] (row : Ω → V) (i : ι) :
    ((missedSpanTuples K row i).card : ℝ) / Fintype.card (ι → Ω) ≤
      (Module.finrank K V : ℝ) / Fintype.card ι := by
  let _ : Nonempty ι := ⟨i⟩
  have hi : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdraw : 0 < (Fintype.card (ι → Ω) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_div_iff₀ hdraw hi).2
  exact_mod_cast uniform_leaveOneOutMiss_count_le (K := K) row i

end Cogentic.Randomized
