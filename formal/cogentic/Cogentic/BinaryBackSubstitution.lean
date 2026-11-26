import Cogentic.SolverFillHeight
import Cogentic.BinaryRationalCost

namespace Cogentic.SolverStage
open Elimination BinaryRational Finset

private theorem get_ofFn {α} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by simp [Vector.get_eq_getElem]

/-- A binary dot product with reduction to canonical rational words after each
operation. A uniform bound for partial sums suffices for every addition. -/
private def dot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → Word) : List (Fin n) → Word × ℕ
  | [] => (pack 0, 0)
  | i :: is =>
    let tail := dot a x is
    let prod := wordMul (pack (a i : ℚ)) (x i)
    let sum := wordAdd prod.1 tail.1
    (sum.1, tail.2 + prod.2 + sum.2)

private theorem dot_spec {n W : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ)
    (aw : ∀ i, width (a i:ℚ) ≤ W) (xw : ∀ i, width (x i) ≤ W)
    (partialWidth : ∀ s : Finset (Fin n), width (∑ i ∈ s,(a i:ℚ)*x i) ≤ W)
    (is : List (Fin n)) (distinct : is.Nodup) :
    let out := dot a (fun i => pack (x i)) is
    out.1 = pack (∑ i ∈ is.toFinset, (a i:ℚ)*x i) ∧ out.2 ≤ 2*is.length*budget W := by
  induction is with
  | nil => simp [dot]
  | cons i is ih =>
    obtain ⟨absent,nodup⟩ := List.nodup_cons.mp distinct
    obtain ⟨tail,tc⟩ := ih nodup
    obtain ⟨prod,pc⟩ := wordMul_spec (a i) (x i) W (aw i) (xw i)
    have one : width ((a i:ℚ)*x i) ≤ W := by simpa using partialWidth {i}
    obtain ⟨sum,sc⟩ := wordAdd_spec _ _ W one (partialWidth is.toFinset)
    have fresh : i ∉ is.toFinset := by simpa using absent
    simp only [dot,tail,prod,List.toFinset_cons,Finset.sum_insert fresh,sum,
      List.length_cons]
    exact ⟨trivial, (Nat.add_le_add (Nat.add_le_add tc pc) sc).trans_eq (by ring)⟩

def recover {n : ℕ} (p : Row (n+1)) (x : Fin n → Word) : Word × ℕ :=
  let d := dot p.drop.coeffs.get x (List.finRange n)
  let v := wordSub (pack (p.rhs:ℚ)) d.1
  let r := wordDiv v.1 (pack (p.head:ℚ))
  (r.1,d.2+v.2+r.2)

set_option maxHeartbeats 2000000 in
/-- Every pivot of an actual solve has a bit cost polynomial in the initial
dimensions and bit height, even when its intermediate dot products cancel. -/
theorem recover_gates {N n H : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H) {rows : List (Row (n+1))}
    (reach : SolveStep base rows) (dim : n ≤ N) (p : Row (n+1))
    {f : Family n} (tail : solve n (rows.map p.reduce)=some f)
    (found : rows.find? (fun r => r.head != 0)=some p) (y : Fin f.free → ℤ) (hy : ∀ j, |y j| ≤ 1) :
    let x := f.values (fun i => (y i:ℚ))
    let W := fillWidth N base.length H
    (recover p (fun i => pack (x i))).1 = pack (p.recover x) ∧
    (recover p (fun i => pack (x i))).2 ≤ (2*n+2)*budget W := by
  intro x W
  let a := p.drop.coeffs.get
  obtain ⟨xw,pw,st,nw⟩ := recover_operand_widths base hp input reach dim p
    (List.mem_of_find?_eq_some found) tail found y hy
  have aw (i) : width (a i:ℚ) ≤ W := by
    simpa only [a,W,width,Row.drop,Row.aug,Option.elim_some,get_ofFn] using pw (some i.succ)
  have full : (List.finRange n).toFinset = univ := by ext; simp
  obtain ⟨dv,dc⟩ := dot_spec a x aw xw st (List.finRange n) (List.nodup_finRange n)
  rw [full] at dv
  rw [List.length_finRange] at dc
  let total : ℚ := ∑ i, (a i:ℚ)*x i
  let xs := fun i => pack (x i)
  let dp := dot a xs (List.finRange n)
  let rhs := pack (p.rhs:ℚ)
  let head := pack (p.head:ℚ)
  change dp.1 = pack total at dv
  change dp.2 ≤ 2*n*budget W at dc
  obtain ⟨sv,sc⟩ := wordSub_spec (p.rhs:ℚ) total W (pw none) (st univ)
  obtain ⟨rv,rc⟩ := wordDiv_spec ((p.rhs:ℚ)-total) (p.head:ℚ) W nw (pw (some 0))
  change (wordDiv (wordSub rhs dp.1).1 head).1 = pack (p.recover x) ∧
    dp.2 + (wordSub rhs dp.1).2 + (wordDiv (wordSub rhs dp.1).1 head).2 ≤ (2*n+2)*budget W
  change (wordSub rhs (pack total)).1 = _ at sv
  rw [dv,sv]
  exact ⟨rv,(Nat.add_le_add (Nat.add_le_add dc sc) rc).trans_eq (by ring)⟩

structure FillProgram (n : ℕ) where
  family : Family n
  run : (Fin family.free → ℤ) → Vector Word n × ℕ

private def empty : FillProgram 0 :=
  ⟨emptyFamily, fun _ => (Vector.ofFn Fin.elim0,0)⟩

private def extendFree {n} (c : FillProgram n) : FillProgram (n+1) :=
  ⟨freeLift c.family,fun y =>
    let tail := c.run (fun i => y i.succ)
    (Vector.ofFn (Fin.cons (pack (y (0:Fin (c.family.free+1)):ℚ)) tail.1.get),tail.2)⟩

private def extendPivot {n} (p : Row (n+1)) (c : FillProgram n) : FillProgram (n+1) :=
  ⟨pivotLift p c.family,fun y =>
    let tail := c.run y
    let head := recover p tail.1.get
    (Vector.ofFn (Fin.cons head.1 tail.1.get),tail.2+head.2)⟩

/-- Record a backward pass along the same pivot choices as forward elimination. -/
def compileFill : (n : ℕ) → List (Row n) → Option (FillProgram n)
  | 0, rows => if rows.all (fun r => r.rhs == 0) then some empty else none
  | n+1, rows =>
    match rows.find? (fun r => r.head != 0) with
    | none => (compileFill n (rows.map Row.drop)).map extendFree
    | some p => (compileFill n (rows.map p.reduce)).map (extendPivot p)

/-- Inspect the empty magnitude tag of each canonical signed word. A scan
stops as soon as it sees a nonzero entry. -/
private def scan {α} (f : α → ℤ) : List α → Option α × ℕ
  | [] => (none,1)
  | r :: rs =>
    if (BinaryPivot.encode (f r)).digits.isEmpty then
      let tail := scan f rs
      (tail.1,tail.2+2)
    else (some r,2)

private theorem scan_spec {α} (f : α → ℤ) (rs : List α) :
    (scan f rs).1 = rs.find? (fun r => f r != 0) ∧ (scan f rs).2 ≤ 2*rs.length+1 := by
  induction rs with
  | nil => simp [scan]
  | cons r rs ih =>
    by_cases h : f r=0
    · simp [scan,h,BinaryPivot.encode,ih.1]
      omega
    · have tag : (BinaryPivot.encode (f r)).digits.isEmpty=false :=
        List.isEmpty_eq_false_iff.mpr (by
          intro eq
          have := congrArg BinaryDivision.value eq
          simp only [BinaryPivot.encode,BinaryDivision.value_bits,BinaryDivision.value,Int.natAbs_eq_zero] at this
          contradiction)
      simp [scan,h,tag]
      omega

/-- Fuse the backward program with the binary forward pivots. This charges
all reached pivot searches and the terminal consistency scan. -/
def binarySolve : (n : ℕ) → List (Row n) → Option (FillProgram n) × ℕ
  | 0, rows =>
    let check := scan Row.rhs rows
    (if check.1.isNone then some empty else none, check.2)
  | n+1, rows =>
    let check := scan Row.head rows
    match check.1 with
    | none =>
      let tail := binarySolve n (rows.map Row.drop)
      (tail.1.map extendFree,check.2+tail.2)
    | some p =>
      let reduced := rows.map (BinaryPivot.pivot p)
      let tail := binarySolve n (reduced.map Prod.fst)
      (tail.1.map (extendPivot p),check.2+(reduced.map Prod.snd).sum+tail.2)

theorem binarySolve_spec {N n H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (r.aug j).natAbs≤H) {rows : List (Row n)}
    (reach : SolveStep base rows) :
    (binarySolve n rows).1 = compileFill n rows ∧
    (binarySolve n rows).2 ≤ (BinaryPivot.solve n rows).2 + (n+1)*(2*rows.length+1) := by
  induction n with
  | zero =>
    obtain ⟨same,cost⟩ := scan_spec Row.rhs rows
    have iff : (rows.find? (fun r => r.rhs != 0)).isNone = rows.all (fun r => r.rhs == 0) := by
      apply Bool.eq_iff_iff.mpr
      simp
    simp only [binarySolve,compileFill,BinaryPivot.solve,same,iff,Nat.zero_add,Nat.one_mul]
    exact ⟨trivial,cost⟩
  | succ n ih =>
    obtain ⟨tested,cost⟩ := scan_spec Row.head rows
    rw [binarySolve,compileFill,BinaryPivot.solve,tested]
    cases found : rows.find? (fun r => r.head != 0) with
    | none =>
      obtain ⟨ok,work⟩ := ih (.drop reach found)
      simp only [List.length_map] at work
      refine ⟨congrArg (Option.map extendFree) ok,?_⟩
      dsimp only
      rw [Nat.succ_mul]
      omega
    | some p =>
      have same : (rows.map (BinaryPivot.pivot p)).map Prod.fst=rows.map p.reduce := by
        rw [List.map_map]
        exact List.map_congr_left (fun r hr => (BinaryPivot.pivot_spec base hp input reach p r
          (List.mem_of_find?_eq_some found) hr).1)
      simp only [same]
      obtain ⟨ok,work⟩ := ih (.pivot reach found)
      simp only [List.length_map] at work
      refine ⟨congrArg (Option.map (extendPivot p)) ok,?_⟩
      rw [Nat.succ_mul]
      omega

theorem compileFill_value (n : ℕ) (rows : List (Row n)) :
    (compileFill n rows).map FillProgram.family = solve n rows := by
  induction n with
  | zero => simp only [compileFill,solve]; split <;> rfl
  | succ n ih =>
    rw [compileFill,solve]
    cases rows.find? (fun r => r.head != 0) with
    | none => rw [← ih (rows.map Row.drop)]; simp [Option.map_map, Function.comp_def,extendFree]
    | some p => dsimp only; rw [← ih (rows.map p.reduce)]; simp [Option.map_map, Function.comp_def,extendPivot]

theorem fill_gates {N n H : ℕ} (base : List (Row N)) (hp : 1 ≤ H)
    (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H) {rows : List (Row n)}
    (reach : SolveStep base rows) (dim : n ≤ N) {c : FillProgram n}
    (found : compileFill n rows=some c) (y : Fin c.family.free → ℤ)
    (hy : ∀ j, |y j| ≤ 1) :
    let W := fillWidth N base.length H
    (∀ i, ((c.run y).1.get i) = pack (c.family.values (fun j => (y j:ℚ)) i)) ∧
    (c.run y).2 ≤ n*(n+1)*budget W := by
  intro W
  induction n with
  | zero =>
    simp only [compileFill] at found
    split at found
    · cases Option.some.inj found
      exact ⟨fun i => i.elim0,by simp [empty]⟩
    · contradiction
  | succ n ih =>
    rw [compileFill] at found
    split at found
    next miss =>
      cases run : compileFill n (rows.map Row.drop) with
      | none => simp [run] at found
      | some sub =>
        have eq : extendFree sub=c := by simpa [run] using found
        subst c
        change Fin (sub.family.free+1) → ℤ at y
        obtain ⟨val,cost⟩ := ih (.drop reach miss) (by omega) run
          (fun j => y j.succ) (fun j => hy j.succ)
        constructor
        · intro i; induction i using Fin.cases with
          | zero => simp [extendFree,Family.values,freeLift]
          | succ j => simpa [extendFree,Family.values,freeLift,get_ofFn] using val j
        · change (sub.run _).2 ≤ _
          exact cost.trans (Nat.mul_le_mul_right _ (by nlinarith : n*(n+1) ≤ (n+1)*(n+1+1)))
    next p hit =>
      cases run : compileFill n (rows.map p.reduce) with
      | none => simp [run] at found
      | some sub =>
        have eq : extendPivot p sub=c := by simpa [run] using found
        subst c
        obtain ⟨val,cost⟩ := ih (.pivot reach hit) (by omega) run y hy
        have tail : solve n (rows.map p.reduce) = some sub.family := by
          rw [← compileFill_value,run]; rfl
        obtain ⟨hv,hc⟩ := recover_gates base hp input reach (by omega) p tail hit y hy
        rw [← funext val] at hv hc
        constructor
        · intro i; induction i using Fin.cases with
          | zero => simpa [extendPivot,Family.values,pivotLift,get_ofFn] using hv
          | succ j => simpa [extendPivot,Family.values,pivotLift,get_ofFn] using val j
        · exact (Nat.add_le_add cost hc).trans_eq (by ring)

private def unitInput {k : ℕ} (j : Fin k) (i : Fin k) : ℤ := if i=j then 1 else 0

private theorem fill_width {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H)
    {c : FillProgram n} (found : compileFill n rows=some c)
    (y : Fin c.family.free → ℤ) (hy : ∀ i, |y i| ≤ 1) (i : Fin n) :
    width (c.family.values (fun j => (y j:ℚ)) i) ≤ fillExponent n rows.length H + 1 := by
  have ok : solve n rows = some c.family := by rw [← compileFill_value,found]; rfl
  have ⟨num,den⟩ := (solve_back_substitution_height rows hp input .start ok y hy).reduced i
  let h := (n+1).factorial*((rows.length+1).factorial*H^(rows.length+1))^n
  have upper := fill_height_exp n rows.length H
  have small (m : ℕ) (cap : m ≤ h) : m.size ≤ fillExponent n rows.length H + 1 :=
    (Nat.size_le_size (cap.trans upper)).trans_eq Nat.size_pow
  rw [Int.abs_eq_natAbs] at num
  exact max_le (small _ (by exact_mod_cast num)) (small _ (by exact_mod_cast den))

/-- Materialize all affine columns with the zero assignment shared between
the unit directions. Charge each actual subtraction of rational words. -/
def materialize {n : ℕ} (c : FillProgram n) :
    (Vector Word n × Vector (Vector Word n) c.family.free) × ℕ :=
  let p := c.run (fun _ => 0)
  let dirs := Vector.ofFn (fun j =>
    let u := c.run (unitInput j)
    let es := Vector.ofFn (fun i => wordSub (u.1.get i) (p.1.get i))
    (es.map Prod.fst,u.2+∑ i, (es.get i).2))
  ((p.1,dirs.map Prod.fst),p.2+∑ j,(dirs.get j).2)

def materializeWork {n : ℕ} (c : FillProgram n) := (materialize c).2

theorem materialize_values {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H) {c : FillProgram n}
    (found : compileFill n rows = some c) :
    (∀ i, (materialize c).1.1.get i = pack (c.family.point i)) ∧
    (∀ j i, ((materialize c).1.2.get j).get i = pack (c.family.direction j i)) := by
  have point := (fill_gates rows hp input .start le_rfl found (fun _ => 0) (by simp)).1
  refine ⟨by simpa only [materialize,Family.point,Int.cast_zero] using point,?_⟩
  intro j i
  have unit (i j : Fin c.family.free) : |unitInput j i| ≤ 1 := by simp only [unitInput]; split <;> decide
  have one := (fill_gates rows hp input .start le_rfl found (unitInput j) (fun k => unit k j)).1
  let x := c.family.values (fun k => (unitInput j k:ℚ)) i
  let y := c.family.values (fun _ => 0) i
  have same : x-y=c.family.direction j i := by
    simp [x,y,Family.direction,Family.point,unitInput,apply_ite (Int.cast : ℤ → ℚ)]
  simp only [materialize,Vector.get_eq_getElem,Vector.getElem_map,Vector.getElem_ofFn]
  change (wordSub _ _).1=_
  rw [← Vector.get_eq_getElem,← Vector.get_eq_getElem,one,point]
  rw [←same]
  exact (wordSub_spec x y (max (width x) (width y)) (le_max_left ..) (le_max_right ..)).1

theorem materialize_gates {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H) {c : FillProgram n}
    (found : compileFill n rows = some c) :
    let W := fillWidth n rows.length H
    let work := n*(n+1)*budget W
    materializeWork c ≤ work + n*(work+n*budget W) := by
  intro W work
  have zero (i : Fin c.family.free) : (|(0:ℤ)|) ≤ 1 := by norm_num
  have unit (i j : Fin c.family.free) : |unitInput j i| ≤ 1 := by simp only [unitInput]; split <;> decide
  obtain ⟨point,pointWork⟩ := fill_gates rows hp input .start le_rfl found _ zero
  have monotone : fillExponent n rows.length H ≤ fillExponent (n+1) rows.length H := by
    unfold fillExponent
    apply Nat.add_le_add
    · exact Nat.mul_le_mul (Nat.size_le_size (by omega)) (by omega)
    · exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  have wide : fillExponent n rows.length H+1 ≤ W := by dsimp only [W,fillWidth]; omega
  have charge (j) :
      (c.run (unitInput j)).2 + (∑ i, (wordSub ((c.run (unitInput j)).1.get i)
        ((c.run (fun _ => 0)).1.get i)).2) ≤ work+n*budget W := by
    obtain ⟨one,oneWork⟩ := fill_gates rows hp input .start le_rfl found (unitInput j) (fun i => unit i j)
    have sub (i) : (wordSub ((c.run (unitInput j)).1.get i) ((c.run (fun _ => 0)).1.get i)).2 ≤ budget W := by
      rw [one i,point i]
      exact (wordSub_spec _ _ W ((fill_width rows hp input found _ (fun k => unit k j) i).trans wide)
        ((fill_width rows hp input found _ zero i).trans wide)).2
    simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] using
      Nat.add_le_add oneWork (sum_le_sum (s:=univ) (fun i _ => sub i))
  have total := sum_le_sum (s:=univ) (fun j _ => charge j)
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at total
  have ok : solve n rows = some c.family := by rw [← compileFill_value,found]; rfl
  have arity : c.family.free ≤ n := by
    have eq := solveWithFillCounter_value n rows
    cases h : solveWithFillCounter n rows with
    | none => simp [h,ok] at eq
    | some t =>
      have same : t.family=c.family := by simpa [h,ok] using eq
      rw [← same]; exact t.arity
  simpa only [materializeWork,materialize,Vector.get_eq_getElem,Vector.getElem_ofFn]
    using Nat.add_le_add pointWork (total.trans (Nat.mul_le_mul_right _ arity))

end Cogentic.SolverStage

#print axioms Cogentic.SolverStage.recover_gates

#print axioms Cogentic.SolverStage.fill_gates

#print axioms Cogentic.SolverStage.materialize_gates
