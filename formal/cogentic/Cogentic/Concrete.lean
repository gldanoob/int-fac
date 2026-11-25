import Cogentic.RootLogs
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds

namespace Cogentic.Concrete
open Marking ArchNumerics RootLogs TwoThirdsSearch

private def rootVector (s : Input) (side : Bool) (bits : ℕ) :=
  Vector.ofFnM (fun j : Fin s.degree => isolate s side j bits)

private def markVector {d : ℕ} (A a low bits : ℕ) (roots : Vector ℚ d) :=
  roots.mapM (fun t => markLog A a t low bits)

/-- Integer numerator of a nearest multiple of two to the minus bits. -/
def numerator (q : ℚ) (bits : ℕ) : ℤ := ⌊q*(2:ℚ)^bits+1/2⌋

private def projection {d : ℕ} (q : Vector ℚ d) (j : ℕ) (bits : ℕ) : ℚ :=
  let h := approxSqrt 1 (j*(j+1)) bits
  let total := (Finset.range j).sum (fun k => q.toArray[k]?.getD 0)
  h*(total - j*q.toArray[j]?.getD 0)

def markColumns (s : Input) (rel : Relations) :
    Option (Vector (Vector ℚ (2*s.degree-2)) rel.marks.length) := do
  let P := TryPair.localBits s rel
  let roots₁ ← rootVector s false (2*P)
  let roots₂ ← rootVector s true (2*P)
  (Vector.ofFn rel.marks.get).mapM fun a => do
    let left ← markVector s.A a s.L₀ (2*P+16) roots₁
    let right ← markVector s.A a s.L₀ (2*P+16) roots₂
    return Vector.ofFn fun row : Fin (2*s.degree-2) =>
      let count := s.degree-1
      let j := row.val%count+1
      roundDyadic (projection (if row.val < count then left else right) j (2*P+16)) (3*P/2)

private def observation {marks dim : ℕ} (cols : Vector (Vector ℚ dim) marks)
    (coeffs : Vector ℤ marks) (bits : ℕ) : Vector ℤ dim :=
  Vector.ofFn fun row =>
    numerator (Finset.univ.sum fun i : Fin marks => (coeffs.get i:ℚ)*(cols.get i).get row) bits

/-- Solve the integer-scaled square system for the selected free columns.
    A singular or inconsistent rounded matrix is discarded. -/
def solveColumns {dim free : ℕ} (rhs : Vector ℤ dim) (columns : Vector (Vector ℤ dim) free)
    (indices : List (Fin free)) : Option (Fin dim → ℚ) := do
  if h : indices.length = dim then
    let selected := (Vector.ofFn indices.get).cast h
    let rows := List.ofFn fun row : Fin dim =>
      Elimination.Row.mk (Vector.ofFn (fun j : Fin dim => (columns.get (selected.get j)).get row)) (-(rhs.get row))
    let family ← Elimination.solve dim rows
    if family.free = 0 then return family.point else none
  else none

def selections (dim free : ℕ) := (List.finRange free).sublistsLen dim

theorem selection_count (dim free : ℕ) :
    (selections dim free).length = free.choose dim ∧ (selections dim free).length ≤ free^dim := by
  simp only [selections,List.length_sublistsLen,List.length_finRange]
  exact ⟨trivial,Nat.choose_le_pow ..⟩

private theorem retained_size {s : Input} {rel : Relations} (ok : stageOne s = some rel) :
    rel.marks.length ≤ s.A := by
  simp only [stageOne] at ok
  split at ok <;> cases ok
  refine (List.length_filter_le ..).trans ?_
  change ((s.marks.toFinset.filter _).sort).length ≤ s.A
  rw [Finset.length_sort]
  have sub : s.marks.toFinset.filter (fun a =>
      1 ≤ a ∧ a ≤ s.A ∧ (((a:ℤ)-s.m).natAbs).Coprime s.n) ⊆ Finset.Icc 1 s.A := by
    intro a h
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp h).2.1,(Finset.mem_filter.mp h).2.2.1⟩
  simpa using Finset.card_le_card sub

/-- Cost of the extra exhaustive column choice, including rejection paths
    past the free-dimension guard, expressed in the same binary scale. -/
theorem per_candidate_minor_count {n g : ℕ} {pair : TryPair.PairData} {rel : Relations}
    (ok : stageOne (TryPair.fixedInput n g pair) = some rel) {free : ℕ}
    (guard : free < rel.marks.length) :
    let b := n.log2+1
    (selections (2*Fixed.d b-2) free).length ≤ 2^(20000*Fixed.v b) := by
  let b := n.log2+1
  have bound : free ≤ Fixed.A b := guard.le.trans (retained_size ok)
  have pos : 0 < Fixed.A b := by dsimp [Fixed.A]; positivity
  calc
    _ ≤ free^(2*Fixed.d b-2) := (selection_count ..).2
    _ ≤ (Fixed.A b)^(2*Fixed.d b-2) := Nat.pow_le_pow_left bound _
    _ ≤ (Fixed.A b)^(2*Fixed.d b) := Nat.pow_le_pow_right pos (by omega)
    _ = _ := by unfold Fixed.A Fixed.v; rw [← Nat.pow_mul]; congr 1; ring

/-- Test the modular certificate on each proposed minor before accepting it.
    This permits exhaustive column selection even when another rounded
    minor is singular or yields spurious rational reconstruction data. -/
def verifiedColumns {dim free : ℕ} (n target Q e bits : ℕ) (rhs : Vector ℤ dim)
    (columns : Vector (Vector ℤ dim) free) (indices : List (Fin free)) : Option (Fin dim → ℚ) := do
  let x ← solveColumns rhs columns indices
  if (verify n target (reconstructedProposal x Q e bits)).isSome then return x else none

def arch : TryPair.Archimedean := fun s rel lattice => do
  let cols ← markColumns s rel
  let P := TryPair.localBits s rel
  let rhs := observation cols lattice.particular P
  let obs := lattice.directions.map (fun direction => observation cols direction P)
  let cap := min P (Fixed.precision (s.n.log2+1))
  (selections (2*s.degree-2) lattice.free).findSome? (verifiedColumns s.n s.target
    (TryPair.denominatorCap s rel) lattice.scale cap rhs obs)

def candidate := TryPair.attempt Construction.construct arch

/-- The outer candidate-count bound times the maximum number of inner
    column choices still has a two-thirds exponent. -/
theorem search_with_minor_choices (k : ℕ) (hk : 0 < k) :
    ∃ b₀, ∀ b ≥ b₀, ∀ n (hn : 2 ≤ n),
      (collect hn (searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n))
        (dyadicTargets (Fixed.beta b)).sort).2 * 2^(20000*Fixed.v b) ≤
        2^(420000*Fixed.v b+Fixed.v b/k) := by
  obtain ⟨b₀,outer⟩ := Fixed.search_calls_leading k hk
  refine ⟨b₀,fun b hb n hn => ?_⟩
  apply (Nat.mul_le_mul_right _ (outer b hb n hn (candidate n))).trans_eq
  rw [← Nat.pow_add]
  congr 1
  omega

theorem subset_search_complete {dim free n target Q e bits : ℕ}
    {rhs : Vector ℤ dim} {columns : Vector (Vector ℤ dim) free} {idx : List (Fin free)}
    (sub : idx.Sublist (List.finRange free)) (length : idx.length = dim)
    (hit : verifiedColumns n target Q e bits rhs columns idx ≠ none) :
    (selections dim free).findSome? (verifiedColumns n target Q e bits rhs columns) ≠ none := by
  intro missing
  exact hit (List.findSome?_eq_none_iff.mp missing idx (List.mem_sublistsLen.mpr ⟨sub,length⟩))

/-- Every choice within the four loops now uses a fully specified deterministic
    program. The only coverage premise says it actually succeeds for each
    necessary target prime on all sufficiently large surviving inputs. -/
theorem factor_of_box_coverage (line : DirichletLZerosOnLine)
    (covered : ∃ n₀ : ℕ, ∀ n ≥ n₀, (Fixed.parameters candidate n).Covers n) :
    ∃ (threshold k : ℕ) (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n)
      (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2 ≤ n), threshold ≤ n → (schedules n hn).parameters = Fixed.parameters candidate n ∧
        (schedules n hn).candidates = (dyadicTargets (Fixed.beta (n.log2+1))).sort) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (charge : ℕ → ℕ) (cap : ℕ),
        (∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) →
        let tree := TwoThirdsFactor.factor (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        tree.work charge ≤ (2*n.log2-1)*cap :=
  Fixed.fixed_factorization line candidate covered

end Cogentic.Concrete
