import Cogentic.ProjectionGates

namespace Cogentic.BinaryProjection
open BinaryDivision BinaryPivot BinaryRootColumns

private def fillWords (s : Marking.Input) (a P : ℕ) (roots : Vector Point s.degree) :=
  Vector.ofFnM (fun j : Fin s.degree=> (logFromRoot s a P (some (roots.get j))).1)

private def projected (logs : Vector ℤ d) (j P : ℕ) : ℤ :=
  let h := (BinaryHelmert.coefficient j.bits (2*P+16)).1
  (row (fun k=>encode (logs.toArray[k]?.getD 0)) j h (2*P+16) (3*P/2)).1

/-- Both root vectors and both mark-log vectors are shared in the same order
as in Concrete.markColumns. Failure of either guard short-circuits the candidate. -/
def columnWords (s : Marking.Input) (rel : Marking.Relations) :
    Option (Vector (Vector ℤ (2*s.degree-2)) rel.marks.length) := do
  let P := TryPair.localBits s rel
  let ls ← Vector.ofFnM (fun j : Fin s.degree=>(BinaryBisection.isolate s false j (2*P)).1)
  let rs ← Vector.ofFnM (fun j : Fin s.degree=>(BinaryBisection.isolate s true j (2*P)).1)
  Vector.ofFnM fun i : Fin rel.marks.length => do
    let l ← fillWords s (rel.marks.get i) P ls
    let r ← fillWords s (rel.marks.get i) P rs
    return Vector.ofFn fun k : Fin (2*s.degree-2) =>
      projected (if k.val<s.degree-1 then l else r) (k.val%(s.degree-1)+1) P

private theorem mapWords {n : ℕ} {α : Type*} {f : Fin n → Option α} {g : Fin n → α}
    (h : ∀ i,f i=some (g i)) : Vector.ofFnM f=some (Vector.ofFn g) := by
  rw [show f=(fun i=>pure (g i)) from funext h,Vector.ofFnM_pure]; rfl

private theorem projected_value {d : ℕ} (z : Vector ℤ d) (q : Vector ℚ d) {j : ℕ} (jp : 0<j) (jl : j<d)
    (P : ℕ) (eq : ∀ k : Fin d,(z.get k:ℚ)/2^(2*P+16)=q.get k) :
    (projected z j P:ℚ)/2^(3*P/2)=ArchNumerics.roundDyadic (Concrete.projection q j (2*P+16)) (3*P/2) := by
  let h := (BinaryHelmert.coefficient j.bits (2*P+16)).1
  let y := fun k : ℕ => encode (z.toArray[k]?.getD 0)
  let M := ∑ k∈Finset.range (j+1),(y k).digits.length
  let W := M+j+h.length+2*(2*P+16)+1+3*P/2
  have hv := (BinaryHelmert.coefficient_spec j.bits (by simpa) (2*P+16)).1
  apply (row_spec q y j h _ _ W jp ?_ (by simpa only [value_bits] using hv) ?_
    (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega)).1
  · intro k hk
    have lt : k<d := hk.trans_lt jl
    have hq : k<q.toArray.size := by simpa using lt
    have hz : k<z.toArray.size := by simpa using lt
    change ((encode (z.toArray[k]?.getD 0)).decode:ℚ)/_= _
    rw [decode_encode,Array.getElem?_eq_getElem hz,Array.getElem?_eq_getElem hq]
    exact eq ⟨k,lt⟩
  · intro k hk
    have small : (y k).digits.length≤M := Finset.single_le_sum (f:=fun a=>(y a).digits.length) (fun _ _=>Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp only [W]; omega

/-- The integer matrix fed to the observation stage represents every dyadic
entry of the original executable column computation, for every boxed candidate
whose stage-one guards pass. -/
theorem constructed_column_words {n ell u v w z : ℕ} (hn : 2≤n) (large : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel →
    let P := TryPair.localBits s rel
    ∃ out, columnWords s rel=some out ∧ Concrete.markColumns s rel=
      some (out.map (fun v=>v.map (fun (t:ℤ)=>(t:ℚ)/2^(3*P/2)))) := by
  intro s rel marked P
  obtain ⟨roots,_,logs,hr,hl,_⟩ := Construction.constructed_mark_logs hn large target box marked
  have Ap : 0<s.A := Nat.two_pow_pos _
  have emitted (side) (j : Fin s.degree) : ∃ t,(BinaryBisection.isolate s side j (2*P)).1=some t := by
    have e := BinaryBisection.isolate_value s side j (2*P)
    rw [(hr side j).1] at e
    cases hit : (BinaryBisection.isolate s side j (2*P)).1 with
    | none => simp [hit] at e
    | some t => exact ⟨t,rfl⟩
  choose t ht using emitted
  have logged (i : Fin rel.marks.length) (side) (j : Fin s.degree) :
      ∃ y,(logFromRoot s (rel.marks.get i) P (some (t side j))).1=some y ∧
        (y:ℚ)/2^(2*P+16)=logs i side j := by
    have e := entry_value s Ap (rel.marks.get i) P side j
    rw [ht side j,(hr side j).1] at e
    simp only [Option.bind_some] at e
    rw [(hl i side j).1] at e
    cases h : (logFromRoot s (rel.marks.get i) P (some (t side j))).1 with
    | none => rw [h] at e; contradiction
    | some y => rw [h] at e; exact ⟨y,rfl,Option.some.inj e⟩
  choose y hy val using logged
  let Z := fun i side=>Vector.ofFn (y i side)
  let result := Vector.ofFn fun i : Fin rel.marks.length=>Vector.ofFn fun k : Fin (2*s.degree-2)=>
    projected (Z i (decide (s.degree-1≤k.val))) (k.val%(s.degree-1)+1) P
  refine ⟨result,?_,?_⟩
  · unfold columnWords
    dsimp only
    rw [mapWords (ht false),mapWords (ht true)]
    dsimp only [bind,Option.bind]
    apply mapWords
    intro i
    have side (c : Bool) : fillWords s (rel.marks.get i) P (Vector.ofFn (t c))=some (Z i c) := by
      apply mapWords; intro j; simpa [Vector.get_eq_getElem] using hy i c j
    rw [side false,side true]
    apply congrArg some
    apply congrArg Vector.ofFn
    funext k
    change projected (if k.val<s.degree-1 then Z i false else Z i true) _ P=
      projected (Z i (decide (s.degree-1≤k.val))) _ P
    by_cases h : k.val<s.degree-1
    · rw [if_pos h,decide_eq_false (Nat.not_le_of_lt h)]
    · rw [if_neg h,decide_eq_true (Nat.le_of_not_gt h)]
  · rw [Concrete.markColumns_values s rel roots logs (fun c j=>(hr c j).1) (fun i c j=>(hl i c j).1)]
    apply congrArg some
    ext i hi k hk
    simp only [result,Vector.getElem_ofFn,Vector.getElem_map]
    have dp : 2≤ s.degree := by change 2≤Fixed.d (n.log2+1); omega
    let j := k%(s.degree-1)+1
    have jl : j<s.degree := by have := Nat.mod_lt k (by omega : 0 < s.degree-1); dsimp [j]; omega
    symm
    exact projected_value _ _ (Nat.succ_pos _) jl P (fun idx=>by
      simpa only [Z,Vector.get_eq_getElem,Vector.getElem_ofFn] using val ⟨i,hi⟩ (decide (s.degree-1≤k)) idx)

end Cogentic.BinaryProjection
