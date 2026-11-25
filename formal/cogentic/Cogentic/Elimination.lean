import Cogentic.Marking
import Mathlib.Algebra.GCDMonoid.Finset

namespace Cogentic.Elimination

open Finset

structure Row (n : ℕ) where
  coeffs : Vector ℤ n
  rhs : ℤ

def Row.eval {n : ℕ} (r : Row n) (x : Fin n → ℚ) : ℚ :=
  ∑ i, (r.coeffs.get i : ℚ)*x i

def Row.Holds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Prop := r.eval x = r.rhs

def Holds {n : ℕ} (rows : List (Row n)) (x : Fin n → ℚ) : Prop := ∀ r ∈ rows, r.Holds x

@[simp] private theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by simp [Vector.get_eq_getElem]

def Row.content {n : ℕ} (r : Row n) : ℕ := r.rhs.natAbs.gcd (univ.gcd (fun i => (r.coeffs.get i).natAbs))

def Row.primitive {n : ℕ} (r : Row n) : Row n :=
  let g := r.content
  if g = 0 then r else ⟨Vector.ofFn (fun i => r.coeffs.get i / (g:ℤ)), r.rhs / (g:ℤ)⟩

theorem primitive_holds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : r.primitive.Holds x ↔ r.Holds x := by
  by_cases zero : r.content = 0
  · simp [Row.primitive,zero]
  have coeff (i) : (r.content : ℤ) ∣ r.coeffs.get i := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Row.content] using (Nat.gcd_dvd_right r.rhs.natAbs _).trans
      (Finset.gcd_dvd (f := fun i => (r.coeffs.get i).natAbs) (Finset.mem_univ i))
  have rhs : (r.content : ℤ) ∣ r.rhs := by
    apply Int.natAbs_dvd_natAbs.mp; simpa [Row.content] using Nat.gcd_dvd_left r.rhs.natAbs _
  have scale (z : ℤ) (dvd : (r.content:ℤ) ∣ z) :
      ((z/(r.content:ℤ):ℤ):ℚ)*(r.content:ℚ) = (z:ℚ) := by exact_mod_cast Int.ediv_mul_cancel dvd
  have nonzero : (r.content:ℚ) ≠ 0 := by exact_mod_cast zero
  rw [show r.primitive.Holds x ↔ r.primitive.eval x * (r.content:ℚ) =
      (r.primitive.rhs:ℚ) * (r.content:ℚ) from (mul_left_inj' nonzero).symm]
  simp only [Row.primitive,zero,if_false,Row.eval,get_ofFn,Finset.sum_mul,scale _ rhs,Row.Holds]
  simp_rw [show ∀ i, (((r.coeffs.get i)/(r.content:ℤ):ℤ):ℚ)*x i*(r.content:ℚ) =
      (r.coeffs.get i:ℚ)*x i from fun i => by rw [mul_right_comm,scale _ (coeff i)]]

def Row.drop {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨Vector.ofFn (fun i => r.coeffs.get i.succ),r.rhs⟩

def Row.head {n : ℕ} (r : Row (n+1)) : ℤ := r.coeffs.get 0

private theorem eval_split {n : ℕ} (r : Row (n+1)) (x : Fin (n+1) → ℚ) :
    r.eval x = r.head*x 0 + r.drop.eval (fun i => x i.succ) := by
  simp [Row.eval, Fin.sum_univ_succ, Row.head, Row.drop]

/-- The coefficients are materialized once per row. The content gcd removes
    every common integer factor after each fraction-free pivot operation. -/
def Row.reduce {n : ℕ} (p r : Row (n+1)) : Row n :=
  (Row.mk (Vector.ofFn (fun i => p.head*r.coeffs.get i.succ-r.head*p.coeffs.get i.succ))
    (p.head*r.rhs-r.head*p.rhs)).primitive

private theorem reduce_iff {n : ℕ} (p r : Row (n+1)) (x : Fin (n+1) → ℚ)
    (nz : p.head ≠ 0) (pivot : p.Holds x) :
    (p.reduce r).Holds (fun i => x i.succ) ↔ r.Holds x := by
  have nonzero : (p.head : ℚ) ≠ 0 := by exact_mod_cast nz
  have eq : p.head*x 0 + p.drop.eval (fun i => x i.succ) = p.rhs := (eval_split p x).symm.trans pivot
  unfold Row.reduce
  rw [primitive_holds]
  simp only [Row.Holds,Row.eval,get_ofFn]
  push_cast
  have linear : (∑ i : Fin n, ((p.head:ℚ)*r.coeffs.get i.succ-r.head*p.coeffs.get i.succ)*x i.succ) =
      p.head*r.drop.eval (fun i => x i.succ) - r.head*p.drop.eval (fun i => x i.succ) := by
    simp only [sub_mul,mul_assoc,sum_sub_distrib,← Finset.mul_sum,Row.drop,Row.eval,get_ofFn]
  rw [linear]
  change _ ↔ r.eval x = r.rhs
  rw [eval_split]
  constructor
  · intro h
    apply mul_left_cancel₀ nonzero
    linear_combination h + r.head*eq
  · intro h
    linear_combination p.head*h - r.head*eq

def Row.recover {n : ℕ} (p : Row (n+1)) (tail : Fin n → ℚ) : ℚ :=
  ((p.rhs:ℚ) - p.drop.eval tail)/p.head

private theorem pivot_iff {n : ℕ} {p : Row (n+1)} (nz : p.head ≠ 0) (x : Fin (n+1) → ℚ) :
    p.Holds x ↔ x 0 = p.recover (fun i => x i.succ) := by
  have nonzero : (p.head:ℚ) ≠ 0 := by exact_mod_cast nz
  unfold Row.Holds Row.recover
  rw [eval_split,eq_div_iff nonzero]
  constructor <;> intro h <;> linarith only [h, mul_comm (p.head:ℚ) (x 0)]

structure Family (n : ℕ) where
  free : ℕ
  position : Fin free → Fin n
  fill : (Fin free → ℚ) → Vector ℚ n

def Family.values {n : ℕ} (s : Family n) (y : Fin s.free → ℚ) := (s.fill y).get
def Family.read {n : ℕ} (s : Family n) (x : Fin n → ℚ) := fun i => x (s.position i)

def emptyFamily : Family 0 := ⟨0,Fin.elim0,fun _ => Vector.ofFn Fin.elim0⟩

def freeLift {n : ℕ} (f : Family n) : Family (n+1) where
  free := f.free+1
  position := Fin.cases 0 (fun i => (f.position i).succ)
  fill := fun y =>
    let tail := f.fill (fun i => y i.succ)
    Vector.ofFn (Fin.cons (y 0) tail.get)

def pivotLift {n : ℕ} (p : Row (n+1)) (f : Family n) : Family (n+1) where
  free := f.free
  position := fun i => (f.position i).succ
  fill := fun y =>
    let tail := f.fill y
    Vector.ofFn (Fin.cons (p.recover tail.get) tail.get)

def solve : (n : ℕ) → List (Row n) → Option (Family n)
  | 0,rows => if rows.all (fun r => r.rhs == 0) then some emptyFamily else none
  | n+1,rows =>
    match rows.find? (fun r => r.head != 0) with
    | none => (solve n (rows.map Row.drop)).map freeLift
    | some p => (solve n (rows.map p.reduce)).map (pivotLift p)

def Correct {n : ℕ} (rows : List (Row n)) : Option (Family n) → Prop
  | none => ∀ x, ¬ Holds rows x
  | some f => (∀ y, Holds rows (f.values y) ∧ f.read (f.values y) = y) ∧
    ∀ x, Holds rows x → f.values (f.read x) = x

private theorem without_pivot {n : ℕ} {rows : List (Row (n+1))} (zero : ∀ r ∈ rows, r.head = 0)
    (x : Fin (n+1) → ℚ) : Holds rows x ↔ Holds (rows.map Row.drop) (fun i => x i.succ) := by
  constructor
  · intro h r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    have eq := (eval_split s x).symm.trans (h s hs)
    change s.drop.eval _ = (s.rhs:ℚ)
    simpa [zero s hs] using eq
  · intro h r hr
    have eq := h r.drop (List.mem_map.mpr ⟨r,hr,rfl⟩)
    change r.drop.eval _ = (r.rhs:ℚ) at eq
    change r.eval x = (r.rhs:ℚ)
    simpa only [eval_split r x,zero r hr,Int.cast_zero,zero_mul,zero_add] using eq

private theorem with_pivot {n : ℕ} {rows : List (Row (n+1))} {p : Row (n+1)}
    (mem : p ∈ rows) (nz : p.head ≠ 0) (x : Fin (n+1) → ℚ) :
    Holds rows x ↔ x 0 = p.recover (fun i => x i.succ) ∧
      Holds (rows.map p.reduce) (fun i => x i.succ) := by
  constructor
  · intro h
    have eq := h p mem
    refine ⟨(pivot_iff nz x).mp eq, ?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact (reduce_iff p s x nz eq).mpr (h s hs)
  · rintro ⟨head,tail⟩ r hr
    exact (reduce_iff p r x nz ((pivot_iff nz x).mpr head)).mp
      (tail _ (List.mem_map.mpr ⟨r,hr,rfl⟩))

private theorem free_values {n : ℕ} (f : Family n) (y : Fin (f.free+1) → ℚ) :
    (freeLift f).values y = Fin.cons (y 0) (f.values (fun i => y i.succ)) := by
  funext i; simp [Family.values,freeLift]

private theorem pivot_values {n : ℕ} (p : Row (n+1)) (f : Family n) (y : Fin f.free → ℚ) :
    (pivotLift p f).values y = Fin.cons (p.recover (f.values y)) (f.values y) := by
  funext i; simp [Family.values,pivotLift]

private theorem zero_correct {rows : List (Row 0)} : Correct rows (solve 0 rows) := by
  rw [solve]
  split
  next h =>
    have zero : ∀ r ∈ rows, r.rhs = 0 := by simpa using h
    refine ⟨fun _ => ⟨fun r hr => ?_,funext (fun i => Fin.elim0 (i : Fin 0))⟩,
      fun _ _ => Subsingleton.elim _ _⟩
    simp [Row.Holds,Row.eval,zero r hr]
  next bad =>
    intro x ok
    apply bad
    apply List.all_eq_true.mpr
    intro r hr
    have := ok r hr
    change (r.rhs == 0) = true
    apply beq_iff_eq.mpr
    unfold Row.Holds Row.eval at this
    simpa using this.symm

private theorem free_correct {n : ℕ} {rows : List (Row (n+1))} {opt : Option (Family n)}
    (zero : ∀ r ∈ rows, r.head = 0) (ih : Correct (rows.map Row.drop) opt) :
    Correct rows (opt.map freeLift) := by
  cases opt with
  | none => exact fun x hx => ih _ ((without_pivot zero x).mp hx)
  | some f =>
    obtain ⟨sound,all⟩ := ih
    constructor
    · intro y
      have ⟨eq,coords⟩ := sound (fun i => y i.succ)
      constructor
      · apply (without_pivot zero _).mpr
        simpa only [free_values f y,Fin.cons_succ] using eq
      · funext j; refine Fin.cases ?_ (fun i => ?_) j
        · simp [Family.read,Family.values,freeLift]
        · simpa [Family.read,free_values,freeLift,Family.values] using congrFun coords i
    · intro x hx
      have eq := all _ ((without_pivot zero x).mp hx)
      rw [free_values f ((freeLift f).read x)]
      funext j; refine Fin.cases ?_ (fun i => ?_) j
      · simp [Family.read,freeLift]
      · simp only [Fin.cons_succ]
        exact congrFun eq i

private theorem pivot_correct {n : ℕ} {rows : List (Row (n+1))} {opt : Option (Family n)}
    {p : Row (n+1)} (mem : p ∈ rows) (nz : p.head ≠ 0) (ih : Correct (rows.map p.reduce) opt) :
    Correct rows (opt.map (pivotLift p)) := by
  cases opt with
  | none => exact fun x hx => ih _ ((with_pivot mem nz x).mp hx).2
  | some f =>
    obtain ⟨sound,all⟩ := ih
    constructor
    · intro y
      have ⟨eq,coords⟩ := sound y
      constructor
      · apply (with_pivot mem nz _).mpr
        rw [pivot_values p f y]
        simp only [Fin.cons_zero,Fin.cons_succ,true_and]
        exact eq
      · funext j
        simpa [Family.read,pivotLift,Family.values] using congrFun coords j
    · intro x hx
      have ⟨head,tail⟩ := (with_pivot mem nz x).mp hx
      have eq := all _ tail
      change (pivotLift p f).values (f.read (fun i => x i.succ)) = x
      rw [pivot_values,eq]
      funext j; refine Fin.cases ?_ (fun i => ?_) j
      · simpa using head.symm
      · simp

/-- Inconsistent systems yield no answers. A successful elimination parametrizes
    every affine rational solution uniquely by the original nonpivot coordinates. -/
theorem solve_correct (n : ℕ) (rows : List (Row n)) : Correct rows (solve n rows) := by
  induction n with
  | zero => exact zero_correct
  | succ n ih =>
    rw [solve]
    split
    next h =>
      apply free_correct _ (ih _)
      simpa only [List.find?_eq_none, bne_iff_ne,not_not] using h
    next p h =>
      have mem := List.mem_of_find?_eq_some h
      have nz : p.head ≠ 0 := by simpa using List.find?_some h
      exact pivot_correct mem nz (ih _)

def Kernel {n : ℕ} (rows : List (Row n)) (x : Fin n → ℚ) := ∀ r ∈ rows, r.eval x = 0

def Family.point {n : ℕ} (f : Family n) := f.values (fun _ => 0)
def Family.direction {n : ℕ} (f : Family n) (j : Fin f.free) (i : Fin n) :=
  f.values (fun t => if t = j then 1 else 0) i - f.point i

private theorem eval_plus {n : ℕ} (r : Row n) (x y : Fin n → ℚ) :
    r.eval (fun i => x i+y i) = r.eval x+r.eval y := by
  simp [Row.eval,mul_add,Finset.sum_add_distrib]

private theorem eval_minus {n : ℕ} (r : Row n) (x y : Fin n → ℚ) :
    r.eval (fun i => x i-y i) = r.eval x-r.eval y := by
  simp [Row.eval,mul_sub,Finset.sum_sub_distrib]

private theorem eval_combination {n k : ℕ} (r : Row n) (c : Fin k → ℚ) (dirs : Fin k → Fin n → ℚ) :
    r.eval (fun i => ∑ j, c j*dirs j i) = ∑ j, c j*r.eval (dirs j) := by
  unfold Row.eval
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

/-- The recovered homogeneous directions form a basis. The coefficients of any
    null vector are its free coordinates in the original column numbering. -/
theorem family_basis {n : ℕ} {rows : List (Row n)} {f : Family n} (ok : solve n rows = some f) :
    Holds rows f.point ∧
    (∀ j, Kernel rows (f.direction j)) ∧
    (∀ j i, f.direction j (f.position i) = if i=j then 1 else 0) ∧
    ∀ x, Kernel rows x → ∀ i, x i = ∑ j, x (f.position j)*f.direction j i := by
  have good := solve_correct n rows
  rw [ok] at good
  obtain ⟨sound,complete⟩ := good
  have point : Holds rows f.point := (sound (fun _ => 0)).1
  have dirs (j) : Kernel rows (f.direction j) := by
    intro r hr
    change r.eval (fun i => _-_) = 0
    rw [eval_minus,(sound _).1 r hr,point r hr,sub_self]
  have free (j i) : f.direction j (f.position i) = if i=j then 1 else 0 := by
    have a := congrFun (sound (fun t => if t=j then 1 else 0)).2 i
    have b := congrFun (sound (fun _ => 0)).2 i
    change f.values _ (f.position i) - f.values _ (f.position i) = _
    change f.values _ (f.position i) = _ at a b
    rw [a,b,sub_zero]
  refine ⟨point,dirs,free,?_⟩
  intro x kernel i
  let z := fun t => ∑ j, x (f.position j)*f.direction j t
  have homogeneous : Kernel rows z := by
    intro r hr
    change r.eval (fun t => ∑ j, x (f.position j)*f.direction j t) = 0
    rw [eval_combination]
    simp [fun j => dirs j r hr]
  have addPoint (v) (kv : Kernel rows v) : Holds rows (fun t => f.point t+v t) := by
    intro r hr
    change r.eval (fun t => _+_) = _
    rw [eval_plus,kv r hr,add_zero]
    exact point r hr
  have readEq : f.read (fun t => f.point t+x t) = f.read (fun t => f.point t+z t) := by
    funext j
    simp [Family.read,z,free,mul_ite]
  have eq := (complete _ (addPoint x kernel)).symm.trans
    ((congrArg f.values readEq).trans (complete _ (addPoint z homogeneous)))
  exact add_left_cancel (congrFun eq i)

def integerScale {n : ℕ} (x : Fin n → ℚ) : ℕ := univ.lcm (fun i => (x i).den)
def integerVector {n : ℕ} (x : Fin n → ℚ) : Vector ℤ n :=
  let m := integerScale x
  Vector.ofFn (fun i => (x i).num*(m/(x i).den : ℕ))

theorem integerScale_pos {n : ℕ} (x : Fin n → ℚ) : 0 < integerScale x := by
  apply Nat.pos_of_ne_zero
  simp [integerScale,Finset.lcm_eq_zero_iff]

theorem integerVector_spec {n : ℕ} (x : Fin n → ℚ) (i) :
    ((integerVector x).get i : ℚ) = x i*(integerScale x : ℚ) := by
  have dvd : (x i).den ∣ integerScale x := Finset.dvd_lcm (Finset.mem_univ i)
  simp only [integerVector,get_ofFn,Int.cast_mul,Int.cast_natCast]
  calc ((x i).num:ℚ)*(integerScale x/(x i).den:ℕ) =
        (x i*(x i).den)*(integerScale x/(x i).den:ℕ) := by rw [Rat.mul_den_eq_num]
       _ = _ := by rw [mul_assoc,←Nat.cast_mul,Nat.mul_div_cancel' dvd]

structure IntegerFamily (n : ℕ) where
  free : ℕ
  position : Fin free → Fin n
  scale : ℕ
  particular : Vector ℤ n
  directions : Vector (Vector ℤ n) free
  scales : Vector ℕ free

def Family.integers {n : ℕ} (f : Family n) : IntegerFamily n where
  free := f.free
  position := f.position
  scale := integerScale f.point
  particular := integerVector f.point
  directions := Vector.ofFn (fun j => integerVector (f.direction j))
  scales := Vector.ofFn (fun j => integerScale (f.direction j))

def relationRows (s : Marking.Relations) : List (Row s.marks.length) :=
  List.ofFn (fun i : Fin (s.rows.length+1) => ⟨Vector.ofFn (s.matrix i), -s.rhs i⟩)

def stageTwo (s : Marking.Relations) : Option (IntegerFamily s.marks.length) :=
  (solve _ (relationRows s)).map Family.integers

private theorem rows_iff (s : Marking.Relations) (x : Fin s.marks.length → ℚ) :
    Holds (relationRows s) x ↔ ∀ i, (∑ j, (s.matrix i j:ℚ)*x j) = -(s.rhs i:ℚ) := by
  simp [Holds,relationRows,List.mem_ofFn,Row.Holds,Row.eval,Fin.forall_fin_succ]

theorem stageTwo_inconsistent (s : Marking.Relations) : stageTwo s = none ↔
    ¬∃ x : Fin s.marks.length → ℚ, ∀ i, (∑ j, (s.matrix i j:ℚ)*x j) = -(s.rhs i:ℚ) := by
  have good := solve_correct _ (relationRows s)
  unfold stageTwo
  cases h : solve _ (relationRows s) with
  | none =>
    rw [h] at good
    exact ⟨fun _ ⟨x,hx⟩ => good x ((rows_iff s x).mpr hx), fun _ => rfl⟩
  | some f =>
    rw [h] at good
    have sat := (rows_iff s _).mp (good.1 (fun _ => 0)).1
    exact ⟨by simp,fun none => (none ⟨_,sat⟩).elim⟩

private theorem kernel_iff (s : Marking.Relations) (x : Fin s.marks.length → ℚ) :
    Kernel (relationRows s) x ↔ ∀ i, (∑ j, (s.matrix i j:ℚ)*x j) = 0 := by
  simp [Kernel,relationRows,List.mem_ofFn,Row.eval,Fin.forall_fin_succ]

private theorem eval_intVec {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ) :
    ((∑ i, a i*(integerVector x).get i : ℤ):ℚ) = (∑ i, (a i:ℚ)*x i)*(integerScale x:ℚ) := by
  push_cast
  simp only [integerVector_spec,Finset.sum_mul,mul_assoc]

/-- The actual integer output solves the target with positive multiplier.
    The computed columns are a rational basis of the homogeneous kernel.
    Their free-coordinate submatrix is diagonal with nonzero integer entries. -/
theorem stageTwo_verified {s : Marking.Relations} {out : IntegerFamily s.marks.length}
    (ok : stageTwo s = some out) :
    0 < out.scale ∧
    (∀ i, (∑ j, s.matrix i j*out.particular.get j) = -(out.scale:ℤ)*s.rhs i) ∧
    (∀ k, 0 < out.scales.get k ∧
      (∀ i, (∑ j, s.matrix i j*(out.directions.get k).get j) = 0) ∧
      (∀ t, (out.directions.get k).get (out.position t) = if t=k then (out.scales.get k:ℤ) else 0)) ∧
    ∀ x : Fin s.marks.length → ℚ, (∀ i, (∑ j, (s.matrix i j:ℚ)*x j) = 0) →
      ∀ i, x i = ∑ k, (x (out.position k)/(out.scales.get k:ℚ))*((out.directions.get k).get i:ℚ) := by
  unfold stageTwo at ok
  cases h : solve _ (relationRows s) with
  | none => simp [h] at ok
  | some f =>
    rw [h] at ok
    cases ok
    obtain ⟨p,ker,diag,span⟩ := family_basis h
    refine ⟨integerScale_pos _, ?_, ?_, ?_⟩
    · intro i
      apply Rat.intCast_injective
      change ((∑ j, s.matrix i j*(integerVector f.point).get j : ℤ):ℚ) = _
      rw [eval_intVec,(rows_iff s _).mp p i]
      push_cast; change _ = -(integerScale f.point:ℚ)*(s.rhs i:ℚ); ring
    · intro k
      change Fin f.free at k
      simp only [Family.integers,get_ofFn]
      refine ⟨integerScale_pos _,?_,?_⟩
      · intro i
        apply Rat.intCast_injective
        rw [eval_intVec,(kernel_iff s _).mp (ker k) i]
        simp
      · intro t
        apply Rat.intCast_injective
        rw [integerVector_spec,diag k t]
        split <;> simp
    · intro x hx i
      simp only [Family.integers,get_ofFn,integerVector_spec]
      rw [span x ((kernel_iff s x).mpr hx) i]
      apply Finset.sum_congr rfl
      intro k _
      have nz : (integerScale (f.direction k):ℚ) ≠ 0 := by exact_mod_cast (integerScale_pos _).ne'
      field_simp

def trySolved (construct : ℕ → ℕ → ℕ → ℕ → ℕ → Marking.Input)
    (finish : (s : Marking.Input) → (r : Marking.Relations) → IntegerFamily r.marks.length →
      Option TwoThirdsSearch.Proposal) : TwoThirdsSearch.TryPair :=
  Marking.tryMarked construct (fun s r => (stageTwo r).bind (finish s r))

end Cogentic.Elimination

#print axioms Cogentic.Elimination.solve_correct
#print axioms Cogentic.Elimination.family_basis
#print axioms Cogentic.Elimination.stageTwo_verified
