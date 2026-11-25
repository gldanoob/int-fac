import Cogentic.Elimination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Heights of the intermediate integer rows of the executable content-
normalized fraction-free elimination, including its augmented column. -/

namespace Cogentic.Elimination
open scoped Matrix BigOperators

/-- Treat the right-hand side just like a surviving coefficient in all
determinants and gcd normalizations. -/
def Row.aug {n : ℕ} (r : Row n) : Option (Fin n) → ℤ := fun j => j.elim r.rhs r.coeffs.get

private def rawReduce {n : ℕ} (p r : Row (n+1)) : Row n :=
  ⟨Vector.ofFn (fun i => p.head*r.coeffs.get i.succ-r.head*p.coeffs.get i.succ),p.head*r.rhs-r.head*p.rhs⟩

private def tailKey {n : ℕ} : Option (Fin n) → Option (Fin (n+1)) := Option.map Fin.succ

private theorem raw_aug {n : ℕ} (p r : Row (n+1)) (j : Option (Fin n)) :
    (rawReduce p r).aug j = p.head*r.aug (tailKey j)-r.head*p.aug (tailKey j) := by
  cases j <;> simp [rawReduce,Row.aug,tailKey,Vector.get_eq_getElem]

private def divisor {n : ℕ} (r : Row n) := if r.content=0 then 1 else r.content

private theorem divisor_pos {n : ℕ} (r : Row n) : 0<divisor r := by
  unfold divisor; split <;> omega

private theorem content_dvd {n : ℕ} (r : Row n) (j : Option (Fin n)) : (divisor r:ℤ) ∣ r.aug j := by
  unfold divisor
  split
  · simp
  · apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_natCast]
    cases j with
    | none => exact Nat.gcd_dvd_left ..
    | some i => exact (Nat.gcd_dvd_right ..).trans (Finset.gcd_dvd (f:=fun k => (r.coeffs.get k).natAbs) (Finset.mem_univ i))

private theorem prim_aug {n : ℕ} (r : Row n) (j : Option (Fin n)) :
    r.primitive.aug j*(divisor r:ℤ)=r.aug j := by
  by_cases h : r.content=0
  · simp [Row.primitive,divisor,h]
  · have dvd := content_dvd r j
    simp only [divisor,h,if_false] at dvd ⊢
    cases j <;> simpa only [Row.primitive,h,if_false,Row.aug,Option.elim,Vector.get_eq_getElem,Vector.getElem_ofFn] using Int.ediv_mul_cancel dvd

private theorem den_divides {q : ℚ} {a b : ℤ} (e : q*(a:ℚ)=b) : q.den ∣ a.natAbs := by
  by_cases h : a=0
  · simp [h]
  · have eq : q=(b:ℚ)/a := (eq_div_iff (Int.cast_ne_zero.mpr h)).mpr e
    rw [eq,←Rat.divInt_eq_div]
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd b a)

/-- Primitive normalization of an integral row proportional to a nonzero
rational multiple of an integral vector cannot exceed that vector in any
coordinate. This is the cancellation missing from the naive doubling bound. -/
theorem primitive_le_integral_representative {n : ℕ} (r : Row n) (D : Option (Fin n) → ℤ)
    (q : ℚ) (nz : q≠0) (rep : ∀ j, q*(r.aug j:ℚ)=D j) (j : Option (Fin n)) :
    (r.primitive.aug j).natAbs ≤ (D j).natAbs := by
  have zero (h : r.content=0) : r.aug j=0 := by
    have div : r.content ∣ (r.aug j).natAbs := by
      cases j with
      | none => exact Nat.gcd_dvd_left ..
      | some i => exact (Nat.gcd_dvd_right ..).trans (Finset.gcd_dvd (f:=fun k => (r.coeffs.get k).natAbs) (Finset.mem_univ i))
    exact Int.natAbs_eq_zero.mp ((zero_dvd_iff).mp (h ▸ div))
  by_cases h : r.content=0
  · simp [Row.primitive,h,zero h]
  · have dd : q.den ∣ r.content := Nat.dvd_gcd (den_divides (rep none))
      (Finset.dvd_gcd (fun i _ => den_divides (rep (some i))))
    have cap := Nat.le_of_dvd (Nat.pos_of_ne_zero h) dd
    have id : q.num*(r.aug j)=(q.den:ℤ)*(D j) := by
      have e := rep j
      rw [← Rat.num_div_den q] at e
      have eq : (q.num:ℚ)*(r.aug j:ℚ)=(q.den:ℚ)*(D j:ℚ) := by field_simp at e; linarith
      exact_mod_cast eq
    have nat := congrArg Int.natAbs id
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at nat
    have prim := congrArg Int.natAbs (prim_aug r j)
    simp only [Int.natAbs_mul,Int.natAbs_natCast,divisor,h,if_false] at prim
    have num : 1 ≤ q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr nz)
    apply Nat.le_of_mul_le_mul_right (c:=q.den) _ q.pos
    calc
      _ ≤ (r.primitive.aug j).natAbs*r.content := Nat.mul_le_mul_left _ cap
      _ = (r.aug j).natAbs := prim
      _ ≤ q.num.natAbs*(r.aug j).natAbs := Nat.le_mul_of_pos_left _ num
      _ = _ := nat.trans (Nat.mul_comm ..)

private def bordered {μ κ : Type*} {k : ℕ} (A : Matrix μ κ ℤ)
    (P : Fin k → μ) (C : Fin k → κ) (r : μ) (j : κ) : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
  A.submatrix (Fin.cons r P) (Fin.cons j C)

/-- A linear combination of selected pivot rows and one original row which
vanishes in the pivot columns is exactly a rational multiple of its bordered
minors. No division-free coefficient-growth recurrence is used. -/
private theorem bordered_identity {μ κ : Type*} {k : ℕ} (A : Matrix μ κ ℤ)
    (P : Fin k → μ) (C : Fin k → κ) (r : μ) (j : κ) (a : ℚ) (v : Fin k → ℚ)
    (zero : ∀ i, a*(A r (C i):ℚ)+∑ l, v l*(A (P l) (C i):ℚ)=0) :
    a*((bordered A P C r j).det:ℚ) =
      (a*(A r j:ℚ)+∑ l, v l*(A (P l) j:ℚ))*((A.submatrix P C).det:ℚ) := by
  classical
  let M := (bordered A P C r j).map (Int.castRingHom ℚ)
  let c : Fin (k+1) → ℚ := Fin.cons a v
  let S := ∑ i, c i • M i
  have linear := Matrix.det_updateRow_sum M 0 c
  change (M.updateRow 0 S).det=a*M.det at linear
  have pivotCol (l : Fin k) : S l.succ=0 := by
    simp only [S,Fin.sum_univ_succ,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact zero l
  have head : S 0=a*(A r j:ℚ)+∑ l, v l*(A (P l) j:ℚ) := by
    simp only [S,Fin.sum_univ_succ,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rfl
  have cast1 : M.det=((bordered A P C r j).det:ℚ) := (Int.cast_det _).symm
  rw [←cast1,←linear,Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  have minors : (M.updateRow 0 S).submatrix Fin.succ Fin.succ = (A.submatrix P C).map (Int.castRingHom ℚ) := by
    ext i q; simp [M,bordered,Matrix.updateRow_apply,Fin.succ_ne_zero,Fin.cons_succ]
  simp [Matrix.updateRow_apply,head,pivotCol,minors,←Int.cast_det]

/-- An actual row is the original identically indexed row scaled by a nonzero
rational, plus a combination of the previous pivot rows, and vanishes in the
previous pivot columns. The list of live columns includes the right-hand side. -/
private structure PivotState {μ κ : Type*} (A : Matrix μ κ ℤ) {n : ℕ} (current : μ → Row n) where
  k : ℕ
  P : Fin k → μ
  C : Fin k → κ
  live : Option (Fin n) → κ
  nonsingular : (A.submatrix P C).det ≠ 0
  factor : μ → ℚ
  nonzero : ∀ r, factor r≠0
  weights : μ → Fin k → ℚ
  zeros : ∀ r i, factor r*(A r (C i):ℚ)+∑ l, weights r l*(A (P l) (C i):ℚ)=0
  values : ∀ r j, factor r*(A r (live j):ℚ)+∑ l, weights r l*(A (P l) (live j):ℚ)=(current r).aug j

private theorem PivotState.minors {μ κ : Type*} {A : Matrix μ κ ℤ} {n : ℕ} {current : μ → Row n}
    (st : PivotState A current) (r : μ) (j : Option (Fin n)) :
    ((A.submatrix st.P st.C).det:ℚ)/st.factor r*((current r).aug j:ℚ) =
      (bordered A st.P st.C r (st.live j)).det := by
  have eq := bordered_identity A st.P st.C r (st.live j) (st.factor r) (st.weights r) (st.zeros r)
  rw [st.values] at eq
  field_simp [st.nonzero r]
  linarith

private def PivotState.drop {μ κ : Type*} {A : Matrix μ κ ℤ} {n : ℕ} {current : μ → Row (n+1)}
    (st : PivotState A current) : PivotState A (fun r => (current r).drop) where
  k := st.k
  P := st.P
  C := st.C
  live := st.live ∘ tailKey
  nonsingular := st.nonsingular
  factor := st.factor
  nonzero := st.nonzero
  weights := st.weights
  zeros := st.zeros
  values r j := by
    cases j with
    | none => exact st.values r none
    | some i =>
      simpa only [Row.drop,Row.aug,Option.elim,tailKey,Option.map,Function.comp_apply,Vector.get_eq_getElem,Vector.getElem_ofFn] using
        st.values r (some i.succ)

private def PivotState.pivotRaw {μ κ : Type*} {A : Matrix μ κ ℤ} {n : ℕ} {current : μ → Row (n+1)}
    (st : PivotState A current) (pick : μ) (pivot : (current pick).head≠0) :
    PivotState A (fun r => rawReduce (current pick) (current r)) := by
  let p := current pick
  let pc := st.live (some 0)
  let coeff := fun r : μ => (current r).head
  let v := fun r : μ => (Fin.cons (-(coeff r:ℚ)*st.factor pick)
    (fun i => (p.head:ℚ)*st.weights r i-(coeff r:ℚ)*st.weights pick i) : Fin (st.k+1) → ℚ)
  have nzp : (p.head:ℚ)≠0 := Int.cast_ne_zero.mpr pivot
  have linear (r : μ) (j : κ) :
      ((p.head:ℚ)*st.factor r)*(A r j:ℚ)+∑ l, v r l*(A ((Fin.cons pick st.P : Fin (st.k+1) → μ) l) j:ℚ) =
        (p.head:ℚ)*(st.factor r*(A r j:ℚ)+∑ l, st.weights r l*(A (st.P l) j:ℚ))-
        (coeff r:ℚ)*(st.factor pick*(A pick j:ℚ)+∑ l, st.weights pick l*(A (st.P l) j:ℚ)) := by
    rw [Fin.sum_univ_succ]
    simp only [v,Fin.cons_zero,Fin.cons_succ,sub_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  refine ⟨st.k+1,Fin.cons pick st.P,Fin.cons pc st.C,st.live ∘ tailKey,?_,
    fun r => (p.head:ℚ)*st.factor r,fun r => mul_ne_zero nzp (st.nonzero r),v,?_,?_⟩
  · intro zero
    have eq := st.minors pick (some 0)
    change ((A.submatrix st.P st.C).det:ℚ)/st.factor pick*(p.head:ℚ)=((bordered A st.P st.C pick pc).det:ℚ) at eq
    rw [show (bordered A st.P st.C pick pc).det=0 from zero,Int.cast_zero] at eq
    exact (mul_ne_zero (div_ne_zero (Int.cast_ne_zero.mpr st.nonsingular) (st.nonzero pick)) nzp) eq
  · intro r i
    rw [linear]
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [Fin.cons_zero]
      rw [show pc=st.live (some 0) from rfl,st.values,st.values]
      change (p.head:ℚ)*(coeff r:ℚ)-(coeff r:ℚ)*(p.head:ℚ)=0
      ring
    · simp only [Fin.cons_succ,st.zeros,mul_zero,sub_self]
  · intro r j
    rw [linear]
    simp only [Function.comp_apply,st.values,raw_aug,Int.cast_sub,Int.cast_mul]
    rfl

private def PivotState.normalize {μ κ : Type*} {A : Matrix μ κ ℤ} {n : ℕ} {current : μ → Row n}
    (st : PivotState A current) : PivotState A (fun r => (current r).primitive) := by
  let g := fun r => (divisor (current r):ℚ)
  have gn (r) : g r≠0 := Nat.cast_ne_zero.mpr (divisor_pos (current r)).ne'
  have linear (r : μ) (j : κ) : (st.factor r/g r)*(A r j:ℚ)+
      ∑ l, (st.weights r l/g r)*(A (st.P l) j:ℚ) =
      (st.factor r*(A r j:ℚ)+∑ l, st.weights r l*(A (st.P l) j:ℚ))/g r := by
    simp only [div_mul_eq_mul_div,←Finset.sum_div,add_div]
  refine ⟨st.k,st.P,st.C,st.live,st.nonsingular,fun r => st.factor r/g r,fun r => div_ne_zero (st.nonzero r) (gn r),
    fun r l => st.weights r l/g r,?_,?_⟩
  · intro r i; rw [linear,st.zeros,zero_div]
  · intro r j; rw [linear,st.values]
    apply (div_eq_iff (gn r)).mpr
    dsimp only [g]
    exact_mod_cast (prim_aug (current r) j).symm

private theorem PivotState.order_le {μ κ : Type*} [Fintype μ] {A : Matrix μ κ ℤ} {n : ℕ}
    {cur : μ → Row n} (st : PivotState A cur) : st.k ≤ Fintype.card μ := by
  have inj : Function.Injective st.P := by
    intro i j eq
    by_contra ne
    exact st.nonsingular (Matrix.det_zero_of_row_eq ne (by ext l; simp [Matrix.submatrix,eq]))
  simpa using Fintype.card_le_of_injective st.P inj

private theorem integer_det_bound {t H : ℕ} (M : Matrix (Fin t) (Fin t) ℤ)
    (bound : ∀ i j, (M i j).natAbs ≤ H) : M.det.natAbs ≤ t.factorial*H^t := by
  have le : |M.det| ≤ (t.factorial:ℤ)*(H:ℤ)^t := by
    rw [Matrix.det_apply']
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin t), |(Equiv.Perm.sign σ:ℤ)*∏ i, M (σ i) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Equiv.Perm (Fin t), (H:ℤ)^t := by
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul,Int.isUnit_iff_abs_eq.mp (Equiv.Perm.sign σ).isUnit,one_mul,Finset.abs_prod]
        calc
          _ ≤ ∏ _ : Fin t, (H:ℤ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun i _ => by rw [Int.abs_eq_natAbs]; exact_mod_cast bound (σ i) i)
          _ = _ := by simp
      _ = _ := by simp [Fintype.card_perm]
  rw [Int.abs_eq_natAbs] at le
  exact_mod_cast le

private theorem PivotState.primitive_bound {μ κ : Type*} [Fintype μ] {A : Matrix μ κ ℤ} {n H : ℕ}
    (hp : 1≤H) (input : ∀ r j, (A r j).natAbs ≤ H) {cur : μ → Row n} (st : PivotState A cur)
    (r : μ) (j : Option (Fin n)) :
    ((cur r).primitive.aug j).natAbs ≤ (Fintype.card μ+1).factorial*H^(Fintype.card μ+1) := by
  let D := fun t => (bordered A st.P st.C r (st.live t)).det
  let q := ((A.submatrix st.P st.C).det:ℚ)/st.factor r
  have nz : q≠0 := div_ne_zero (Int.cast_ne_zero.mpr st.nonsingular) (st.nonzero r)
  have bounded := primitive_le_integral_representative (cur r) D q nz (st.minors r) j
  have det := integer_det_bound (bordered A st.P st.C r (st.live j))
    (fun i l => input ((Fin.cons r st.P : Fin (st.k+1) → μ) i) ((Fin.cons (st.live j) st.C : Fin (st.k+1) → κ) l))
  have le := Nat.succ_le_succ st.order_le
  exact bounded.trans (det.trans (Nat.mul_le_mul (Nat.factorial_le le) (Nat.pow_le_pow_right hp le)))

/-- The precise recursive states visited by solve. The head pivot and both
recursive calls are the ones in the executable list traversal. -/
inductive SolveStep {N : ℕ} (initial : List (Row N)) : {n : ℕ} → List (Row n) → Prop
  | start : SolveStep initial initial
  | drop {n} {rows : List (Row (n+1))} (prev : SolveStep initial rows)
      (empty : rows.find? (fun r => r.head != 0)=none) : SolveStep initial (rows.map Row.drop)
  | pivot {n} {rows : List (Row (n+1))} (prev : SolveStep initial rows) {p : Row (n+1)}
      (found : rows.find? (fun r => r.head != 0)=some p) : SolveStep initial (rows.map p.reduce)

private def initialMatrix {N : ℕ} (rows : List (Row N)) : Matrix (Fin rows.length) (Option (Fin N)) ℤ :=
  fun r j => (rows.get r).aug j

private def firstState {N : ℕ} (rows : List (Row N)) : PivotState (initialMatrix rows) rows.get where
  k := 0
  P := Fin.elim0
  C := Fin.elim0
  live := id
  nonsingular := by simp
  factor := fun _ => 1
  nonzero := fun _ => one_ne_zero
  weights := fun _ => Fin.elim0
  zeros _ i := i.elim0
  values r j := by simp [initialMatrix]

/-- Every intermediate augmented row, even on inconsistent systems and trials
which eventually fail, has height at most (m+1)! H^(m+1) for m input rows of
height ≤ H. Storing its pre-gcd cross-products costs at most one further
squaring and a factor of two. -/
theorem solve_intermediate_height {N n H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (Row.aug r j).natAbs ≤ H)
    {rows : List (Row n)} (reachable : SolveStep base rows) :
    ∀ r∈rows, ∀ j, (Row.aug r j).natAbs ≤ (base.length+1).factorial*H^(base.length+1) := by
  let cap := (base.length+1).factorial*H^(base.length+1)
  let A := initialMatrix base
  have raw : ∀ r j, (A r j).natAbs≤H := fun r j => input _ (List.get_mem base r) j
  suffices ∃ curr : Fin base.length → Row n, rows=List.ofFn curr ∧ Nonempty (PivotState A curr) ∧
      ∀ i j, ((curr i).aug j).natAbs≤cap by
    obtain ⟨curr,rfl,_,height⟩ := this
    intro r hr j
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact height i j
  induction reachable with
  | start =>
    refine ⟨base.get,(List.ofFn_get _).symm,⟨firstState base⟩,?_⟩
    intro r j
    have cap1 : H≤cap := by
      have pow := Nat.pow_le_pow_right hp (show 1≤base.length+1 by omega)
      simpa using pow.trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _))
    exact (raw r j).trans cap1
  | drop prev _ ih =>
    obtain ⟨cur,rfl,⟨st⟩,bound⟩ := ih
    refine ⟨fun r => (cur r).drop,List.map_ofFn,⟨st.drop⟩,?_⟩
    intro r j
    cases j with
    | none => exact bound r none
    | some i => simpa only [Row.drop,Row.aug,Option.elim,Vector.get_eq_getElem,Vector.getElem_ofFn] using bound r (some i.succ)
  | pivot prev found ih =>
    obtain ⟨cur,rfl,⟨st⟩,_⟩ := ih
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp (List.mem_of_find?_eq_some found)
    have nz : (cur r).head ≠ 0 := by simpa using List.find?_some found
    let st' := st.pivotRaw r nz
    refine ⟨fun i => (cur r).reduce (cur i),List.map_ofFn,⟨st'.normalize⟩,?_⟩
    intro i j
    change ((rawReduce (cur r) (cur i)).primitive.aug j).natAbs ≤ (base.length+1).factorial*H^(base.length+1)
    simpa only [Fintype.card_fin] using st'.primitive_bound hp raw i j

/-- The size of the signed difference materialized immediately before each gcd. -/
theorem solve_cross_product_height {N n H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (Row.aug r j).natAbs ≤ H)
    {rows : List (Row (n+1))} (reachable : SolveStep base rows)
    (p r : Row (n+1)) (pm : p∈rows) (rm : r∈rows) (j : Option (Fin n)) :
    (p.head*r.aug (j.map Fin.succ)-r.head*p.aug (j.map Fin.succ)).natAbs ≤
      2*((base.length+1).factorial*H^(base.length+1))^2 := by
  let C := (base.length+1).factorial*H^(base.length+1)
  have bound := solve_intermediate_height base hp input reachable
  have ph : p.head.natAbs ≤ C := bound p pm (some 0)
  have rh : r.head.natAbs ≤ C := bound r rm (some 0)
  apply (Int.natAbs_sub_le ..).trans
  simp only [Int.natAbs_mul, pow_two, two_mul]
  exact Nat.add_le_add (Nat.mul_le_mul ph (bound r rm _)) (Nat.mul_le_mul rh (bound p pm _))

private theorem cap_le_pow (m H : ℕ) : m.factorial*H^m ≤ 2^((m.size+H.size)*m) := by
  calc
    _ ≤ m^m*H^m := Nat.mul_le_mul_right _ m.factorial_le_pow
    _ = (m*H)^m := (mul_pow ..).symm
    _ ≤ (2^m.size*2^H.size)^m := Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.lt_size_self m).le (Nat.lt_size_self H).le) _
    _ = _ := by rw [←pow_add,←pow_mul]

/-- Bit size of every raw product difference, including the right-hand side.
Here `Nat.size` is binary length, with `size 0 = 0`. -/
theorem solve_cross_product_bits {N n H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (Row.aug r j).natAbs ≤ H)
    {rows : List (Row (n+1))} (reachable : SolveStep base rows)
    (p r : Row (n+1)) (pm : p∈rows) (rm : r∈rows) (j : Option (Fin n)) :
    (p.head*r.aug (j.map Fin.succ)-r.head*p.aug (j.map Fin.succ)).natAbs.size ≤
      2*(((base.length+1).size+H.size)*(base.length+1))+2 := by
  let k := ((base.length+1).size+H.size)*(base.length+1)
  apply Nat.size_le.mpr
  have square := Nat.pow_le_pow_left (cap_le_pow (base.length+1) H) 2
  have raw := solve_cross_product_height base hp input reachable p r pm rm j
  apply lt_of_le_of_lt (raw.trans (Nat.mul_le_mul_left 2 square))
  change 2*(2^k)^2 < 2^(2*k+2)
  rw [←pow_mul,Nat.mul_comm k 2,pow_add]
  have p : 0 < 2^(2*k) := by positivity
  omega

end Cogentic.Elimination

#print axioms Cogentic.Elimination.solve_intermediate_height
#print axioms Cogentic.Elimination.solve_cross_product_bits
