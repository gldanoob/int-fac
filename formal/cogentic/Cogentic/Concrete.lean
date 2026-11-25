import Cogentic.RootLogs
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds

namespace Cogentic.Concrete
open Marking ArchNumerics RootLogs TwoThirdsSearch

private def rootVector (s : Input) (side : Bool) (bits : ℕ) :=
  Vector.ofFnM (fun j : Fin s.degree => isolate s side j bits)

private def markVector {d : ℕ} (A a low bits : ℕ) (roots : Vector ℚ d) :=
  Vector.ofFnM (fun j : Fin d => markLog A a (roots.get j) low bits)

/-- Integer numerator of a nearest multiple of two to the minus bits. -/
def numerator (q : ℚ) (bits : ℕ) : ℤ := ⌊q*(2:ℚ)^bits+1/2⌋

def projection {d : ℕ} (q : Vector ℚ d) (j : ℕ) (bits : ℕ) : ℚ :=
  let h := approxSqrt 1 (j*(j+1)) bits
  let total := (Finset.range j).sum (fun k => q.toArray[k]?.getD 0)
  h*(total - j*q.toArray[j]?.getD 0)

def markColumns (s : Input) (rel : Relations) :
    Option (Vector (Vector ℚ (2*s.degree-2)) rel.marks.length) := do
  let P := TryPair.localBits s rel
  let roots₁ ← rootVector s false (2*P)
  let roots₂ ← rootVector s true (2*P)
  Vector.ofFnM fun i : Fin rel.marks.length => do
    let a := rel.marks.get i
    let left ← markVector s.A a s.L₀ (2*P+16) roots₁
    let right ← markVector s.A a s.L₀ (2*P+16) roots₂
    return Vector.ofFn fun row : Fin (2*s.degree-2) =>
      let count := s.degree-1
      let j := row.val%count+1
      roundDyadic (projection (if row.val < count then left else right) j (2*P+16)) (3*P/2)

private theorem ofFnM_values {n : ℕ} {α : Type*} {f : Fin n → Option α} (g : Fin n → α)
    (eq : ∀ i, f i = some (g i)) : Vector.ofFnM f = some (Vector.ofFn g) := by
  have same : f = fun i => pure (g i) := funext eq
  rw [same,Vector.ofFnM_pure]
  rfl

/-- Identify every rounded entry produced by the executable marking columns
from its per-root bisections and per-mark logarithms. -/
theorem markColumns_values (s : Input) (rel : Relations)
    (root : Bool → Fin s.degree → ℚ) (v : Fin rel.marks.length → Bool → Fin s.degree → ℚ)
    (roots : ∀ side j, isolate s side j (2*TryPair.localBits s rel) = some (root side j))
    (logs : ∀ i side j, markLog s.A (rel.marks.get i) (root side j) s.L₀
        (2*TryPair.localBits s rel+16) = some (v i side j)) :
    let P := TryPair.localBits s rel
    markColumns s rel = some (Vector.ofFn (fun i => Vector.ofFn (fun row : Fin (2*s.degree-2) =>
      let count := s.degree-1
      let side : Bool := decide (count ≤ row.val)
      roundDyadic (projection (Vector.ofFn (v i side)) (row.val%count+1) (2*P+16)) (3*P/2)))) := by
  dsimp only
  have h (side) := ofFnM_values _ (roots side)
  unfold markColumns rootVector
  dsimp only
  simp only [h]
  apply ofFnM_values
  intro i
  have l (side) : markVector s.A (rel.marks.get i) s.L₀ (2*TryPair.localBits s rel+16)
        (Vector.ofFn (root side)) = some (Vector.ofFn (v i side)) := by
    apply ofFnM_values
    intro j; simpa [Vector.get_eq_getElem] using logs i side j
  rw [l false,l true]
  apply congrArg some
  apply congrArg Vector.ofFn
  funext row
  by_cases first : row.val < s.degree-1
  · simp [first, Nat.not_le_of_lt first]
  · simp [first,Nat.le_of_not_gt first]

def observation {marks dim : ℕ} (cols : Vector (Vector ℚ dim) marks)
    (coeffs : Vector ℤ marks) (bits : ℕ) : Vector ℤ dim :=
  Vector.ofFn fun row =>
    numerator (Finset.univ.sum fun i : Fin marks => (coeffs.get i:ℚ)*(cols.get i).get row) bits

/-- The free-coordinate check is equivalent to uniqueness of the rational
    solution of the rounded integer system. -/
def uniqueSolution {n : ℕ} (rows : List (Elimination.Row n)) : Option (Fin n → ℚ) :=
  match Elimination.solve n rows with
  | some f => if f.free = 0 then some f.point else none
  | none => none

theorem uniqueSolution_iff {n : ℕ} (rows : List (Elimination.Row n)) (x : Fin n → ℚ) :
    uniqueSolution rows = some x ↔ Elimination.Holds rows x ∧
      ∀ y, Elimination.Holds rows y → y = x := by
  classical
  have correct := Elimination.solve_correct n rows
  cases eq : Elimination.solve n rows with
  | none =>
    rw [eq] at correct
    simp [uniqueSolution,eq,correct x]
  | some f =>
    rw [eq] at correct
    obtain ⟨sound,exh⟩ := correct
    have root := (sound (fun _ => 0)).1
    have get := (sound (fun _ => 0)).2
    change Elimination.Holds rows f.point at root
    simp only [uniqueSolution,eq]
    constructor
    · intro h
      split at h
      next z =>
        cases h
        refine ⟨root,fun y hy => ?_⟩
        have empty (i : Fin f.free) : False := by have := i.isLt; omega
        have same : f.read y = (fun _ => 0) := funext fun i => (empty i).elim
        exact (exh y hy).symm.trans (congrArg f.values same)
      next z => cases h
    · rintro ⟨hx,uniq⟩
      have truth := uniq f.point root
      have z : f.free = 0 := by
        by_contra nz
        let i : Fin f.free := ⟨0,Nat.pos_of_ne_zero nz⟩
        have a := sound (fun _ => 1)
        have s := (uniq _ a.1).trans truth.symm
        have ev := congrFun (congrArg f.read s) i
        rw [a.2] at ev
        change 1 = f.read (f.values (fun _ => 0)) i at ev
        rw [get] at ev
        norm_num at ev
      simp [z,truth]

def minorRows {dim free : ℕ} (rhs : Vector ℤ dim) (columns : Vector (Vector ℤ dim) free)
    (choice : Vector (Fin free) dim) : List (Elimination.Row dim) :=
  List.ofFn fun row : Fin dim =>
    ⟨Vector.ofFn (fun j : Fin dim => (columns.get (choice.get j)).get row), -(rhs.get row)⟩

def minorMatrix {dim free : ℕ} (columns : Vector (Vector ℤ dim) free)
    (choice : Vector (Fin free) dim) : Matrix (Fin dim) (Fin dim) ℚ :=
  fun i j => ((columns.get (choice.get j)).get i:ℚ)

theorem minorRows_iff {dim free : ℕ} (rhs : Vector ℤ dim) (columns : Vector (Vector ℤ dim) free)
    (choice : Vector (Fin free) dim) (x : Fin dim → ℚ) :
    Elimination.Holds (minorRows rhs columns choice) x ↔
      (minorMatrix columns choice).mulVec x = fun i => -(rhs.get i:ℚ) := by
  simp only [Elimination.Holds,minorRows,List.mem_ofFn,forall_exists_index,
    forall_apply_eq_imp_iff,Elimination.Row.Holds,Elimination.Row.eval,funext_iff,
    Matrix.mulVec,dotProduct,minorMatrix,Int.cast_neg,Vector.get_eq_getElem,Vector.getElem_ofFn]

/-- Solve the integer-scaled square system for the selected free columns.
    A singular or inconsistent rounded matrix is discarded. -/
def solveColumns {dim free : ℕ} (rhs : Vector ℤ dim) (columns : Vector (Vector ℤ dim) free)
    (indices : List (Fin free)) : Option (Fin dim → ℚ) := do
  if h : indices.length = dim then
    let selected := (Vector.ofFn indices.get).cast h
    uniqueSolution (minorRows rhs columns selected)
  else none

theorem solveColumns_of_det_ne_zero {dim free : ℕ} (rhs : Vector ℤ dim)
    (columns : Vector (Vector ℤ dim) free) (idx : List (Fin free)) (size : idx.length = dim) :
    let choice := (Vector.ofFn idx.get).cast size
    let M := minorMatrix columns choice
    M.det ≠ 0 → ∃ y, solveColumns rhs columns idx = some y ∧ M.mulVec y = fun i => -(rhs.get i:ℚ) := by
  let choice := (Vector.ofFn idx.get).cast size
  let M := minorMatrix columns choice
  let b : Fin dim → ℚ := fun i => -(rhs.get i:ℚ)
  change M.det ≠ 0 → ∃ y, _ ∧ M.mulVec y = b
  intro det
  let y := M⁻¹.mulVec b
  have sol : M.mulVec y = b := by
    dsimp [y]; rw [Matrix.mulVec_mulVec,M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr det),Matrix.one_mulVec]
  refine ⟨y,?_,sol⟩
  simp only [solveColumns,dif_pos size]
  apply (uniqueSolution_iff _ _).mpr
  refine ⟨(minorRows_iff rhs columns choice y).mpr sol,fun x good => ?_⟩
  exact Matrix.mulVec_injective_of_det_ne_zero det (((minorRows_iff rhs columns choice x).mp good).trans sol.symm)

def selections (dim free : ℕ) := (List.finRange free).sublistsLen dim

theorem selection_count (dim free : ℕ) :
    (selections dim free).length = free.choose dim ∧ (selections dim free).length ≤ free^dim := by
  simp only [selections,List.length_sublistsLen,List.length_finRange]
  exact ⟨trivial,Nat.choose_le_pow ..⟩

theorem retained_size {s : Input} {rel : Relations} (ok : stageOne s = some rel) :
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

/-- One nonsingular minor with a verifiable reconstructed solution forces
the executable enumeration to return a verifiable proposal. An earlier
successful minor also suffices. -/
theorem minor_search_verifies {dim free n target Q e bits : ℕ}
    (rhs : Vector ℤ dim) (cols : Vector (Vector ℤ dim) free) (idx : List (Fin free))
    (sub : idx.Sublist (List.finRange free)) (size : idx.length = dim)
    (det : (minorMatrix cols ((Vector.ofFn idx.get).cast size)).det ≠ 0)
    (cert : ∀ y, (minorMatrix cols ((Vector.ofFn idx.get).cast size)).mulVec y =
      (fun i => -(rhs.get i:ℚ)) → verify n target (reconstructedProposal y Q e bits) ≠ none) :
    ∃ x, (selections dim free).findSome? (verifiedColumns n target Q e bits rhs cols) = some x ∧
      verify n target (reconstructedProposal x Q e bits) ≠ none := by
  obtain ⟨y,sol,eq⟩ := solveColumns_of_det_ne_zero rhs cols idx size det
  have good := Option.isSome_iff_ne_none.mpr (cert y eq)
  have hit : verifiedColumns n target Q e bits rhs cols idx = some y := by
    simp [verifiedColumns,sol,good]
  have found := subset_search_complete sub size (by rw [hit]; simp)
  cases hx : (selections dim free).findSome? (verifiedColumns n target Q e bits rhs cols) with
  | none => exact (found hx).elim
  | some x =>
    obtain ⟨i,_,ok⟩ := List.exists_of_findSome?_eq_some hx
    refine ⟨x,rfl,?_⟩
    unfold verifiedColumns at ok
    obtain ⟨v,_,test⟩ := Option.bind_eq_some_iff.mp ok
    split at test
    next valid => cases test; exact Option.isSome_iff_ne_none.mp valid
    next _ => cases test

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
