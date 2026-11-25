import Cogentic.BinaryDivisionCost

namespace Cogentic.BinaryPivot
open Cogentic.BinaryDivision

/-- A full adder uses a shared XOR, two ANDs, one OR and one more XOR. -/
def addDigits : ℕ → List Bool → List Bool → Bool → List Bool × ℕ
  | 0, _, _, c => ([c], 0)
  | w+1, xs, ys, c =>
    let x := xs.headD false
    let y := ys.headD false
    let s := xor x y
    let next := (x && y) || (s && c)
    let upper := addDigits w xs.tail ys.tail next
    (xor s c :: upper.1, upper.2+5)

theorem addDigits_spec (w : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length≤w) (hy : ys.length≤w) :
    let out := addDigits w xs ys c
    out.1.length=w+1 ∧ out.2=5*w ∧ value out.1=value xs+value ys+c.toNat := by
  induction w generalizing xs ys c with
  | zero =>
    have nx := List.length_eq_zero_iff.mp (by omega : xs.length=0)
    have ny := List.length_eq_zero_iff.mp (by omega : ys.length=0)
    simp [nx,ny,addDigits,value]
  | succ w ih =>
    let x := xs.headD false
    let y := ys.headD false
    let b := (x && y) || (xor x y && c)
    obtain ⟨len,cost,val⟩ := ih xs.tail ys.tail b (by simp; omega) (by simp; omega)
    let upper := addDigits w xs.tail ys.tail b
    change (_ :: upper.1).length = w+1+1 ∧ upper.2+5=5*(w+1) ∧ _ = _
    refine ⟨by simp [upper,len],by simp [upper,cost,Nat.mul_succ],?_⟩
    change value (xor (xor x y) c :: upper.1)=_
    rw [value,value_head xs,value_head ys]
    have bit : (xor (xor x y) c).toNat+2*b.toNat=x.toNat+y.toNat+c.toNat := by
      dsimp only [b]; cases x <;> cases y <;> cases c <;> decide
    change value upper.1=value xs.tail+value ys.tail+b.toNat at val
    change _ = x.toNat+2*value xs.tail+(y.toNat+2*value ys.tail)+c.toNat
    omega

private theorem mask_value (bs : List Bool) (b : Bool) :
    value (bs.map (fun x => b && x))=b.toNat*value bs := by
  induction bs with
  | nil => simp [value]
  | cons x xs ih => cases b <;> simp_all [value]

/-- Schoolbook multiplication. The low multiplier bit masks one copy of the
multiplicand; adding it to the shifted upper product costs five gates per bit. -/
def multiply (ys : List Bool) : List Bool → List Bool × ℕ
  | [] => ([],0)
  | b::bs =>
    let prev := multiply ys bs
    let width := max ys.length (prev.1.length+1)
    let add := addDigits width (false::prev.1) (ys.map (fun x => b && x)) false
    (add.1,prev.2+ys.length+add.2)

theorem multiply_spec (ys xs : List Bool) :
    let out := multiply ys xs
    value out.1=value xs*value ys ∧ out.1.length≤ys.length+2*xs.length ∧
      out.2≤xs.length*(ys.length+5*(ys.length+2*xs.length)) := by
  induction xs with
  | nil => simp [multiply,value]
  | cons b bs ih =>
    let prev := multiply ys bs
    let w := max ys.length (prev.1.length+1)
    have ⟨val,len,cost⟩ := ih
    change value prev.1=_ at val
    change prev.1.length≤_ at len
    change prev.2≤_ at cost
    have h₁ : (false::prev.1).length≤w := le_max_right ..
    have h₂ : (ys.map (fun x => b && x)).length≤w := by simp [w]
    obtain ⟨length,gates,num⟩ := addDigits_spec w _ _ false h₁ h₂
    simp only [multiply,List.length_cons]
    dsimp only [prev,w] at num length gates
    rw [num,length,gates]
    simp only [value, Bool.toNat_false, Nat.zero_add,Nat.add_zero,mask_value]
    change _ ∧ w+1≤ys.length+2*(bs.length+1) ∧ prev.2+ys.length+5*w≤_
    have maxle : w≤ys.length+2*bs.length+1 := max_le (by omega) (by omega)
    refine ⟨?_,by omega,?_⟩
    · change 2*value prev.1 + b.toNat*value ys=_
      rw [val]; ring
    · nlinarith [show 0≤bs.length by omega]

structure SignedWord where
  negative : Bool
  digits : List Bool

def signed (s : Bool) (m : ℕ) : ℤ := if s then -(m:ℤ) else m

def SignedWord.decode (x : SignedWord) : ℤ := signed x.negative (value x.digits)

def encode (z : ℤ) : SignedWord := ⟨decide (z<0),z.natAbs.bits⟩

@[simp] theorem decode_encode (z : ℤ) : (encode z).decode=z := by
  cases z <;> simp [encode,SignedWord.decode,signed]
  omega

/-- Evaluate both magnitude differences and the sum. The signs and the
borrow select the correct magnitude through two bitwise multiplexers. -/
def signedDifference (x y : SignedWord) : SignedWord × ℕ :=
  let w := max x.digits.length y.digits.length
  let a := subtract w x.digits y.digits false
  let b := subtract w y.digits x.digits false
  let magnitude := selectDigits w a.borrow (!a.borrow) b.digits a.digits
  let total := addDigits w x.digits y.digits false
  let opposite := xor x.negative y.negative
  let keep := !opposite
  let chosen := selectDigits (w+1) opposite keep total.1 magnitude.1
  (⟨xor x.negative (keep && a.borrow),chosen.1⟩,
    a.gates+b.gates+magnitude.2+total.2+chosen.2+5)

theorem signedDifference_spec (x y : SignedWord) :
    let w := max x.digits.length y.digits.length
    let out := signedDifference x y
    out.1.decode=x.decode-y.decode ∧ out.2=25*w+8 := by
  let w := max x.digits.length y.digits.length
  let a := subtract w x.digits y.digits false
  let b := subtract w y.digits x.digits false
  let opp := xor x.negative y.negative
  let d := selectDigits w a.borrow (!a.borrow) b.digits a.digits
  let t := addDigits w x.digits y.digits false
  let sel := selectDigits (w+1) opp (!opp) t.1 d.1
  have hx : x.digits.length≤w := le_max_left ..
  have hy : y.digits.length≤w := le_max_right ..
  have ⟨al,ac,ae⟩ := subtract_spec w x.digits y.digits false hx hy
  have ⟨bl,bc,be⟩ := subtract_spec w y.digits x.digits false hy hx
  have ⟨dl,dc,de⟩ := select_spec w a.borrow b.digits a.digits bl.le al.le
  have ⟨tl,tc,te⟩ := addDigits_spec w x.digits y.digits false hx hy
  have ⟨_,sc,se⟩ := select_spec (w+1) opp t.1 d.1 tl.le (dl.trans_le (by omega))
  change a.digits.length=w at al
  change b.digits.length=w at bl
  change value a.digits+value y.digits+0=value x.digits+2^w*a.borrow.toNat at ae
  change value b.digits+value x.digits+0=value y.digits+2^w*b.borrow.toNat at be
  have af := value_lt a.digits
  have bf := value_lt b.digits
  rw [al] at af
  rw [bl] at bf
  change value d.1 = if a.borrow then value b.digits else value a.digits at de
  have diff : signed a.borrow (value d.1) = (value x.digits : ℤ)-value y.digits := by
    cases ha : a.borrow <;> cases hb : b.borrow <;>
      simp [ha,hb,signed] at de ae be ⊢ <;> omega
  change value sel.1 = if opp then value t.1 else value d.1 at se
  change value t.1=value x.digits+value y.digits+0 at te
  change a.gates=7*w at ac
  change b.gates=7*w at bc
  change d.2=3*w at dc
  change t.2=5*w at tc
  change sel.2=3*(w+1) at sc
  change signed (xor x.negative ((!opp) && a.borrow)) (value sel.1)=
    signed x.negative (value x.digits)-signed y.negative (value y.digits) ∧
    a.gates+b.gates+d.2+t.2+sel.2+5=25*w+8
  constructor
  · rw [se]
    cases sx : x.negative <;> cases sy : y.negative <;> cases ha : a.borrow <;>
      simp [opp,sx,sy,ha,signed,te] at diff ⊢ <;> omega
  · omega

private theorem signed_mul (a b : Bool) (x y : ℕ) :
    signed (xor a b) (x*y) = signed a x*signed b y := by
  cases a <;> cases b <;> simp [signed]

/-- Two schoolbook products and a signed difference refine one raw pivot
entry; the extra two XOR gates compute the two product signs. -/
def cross (a b c d : SignedWord) : SignedWord × ℕ :=
  let p := multiply b.digits a.digits
  let q := multiply d.digits c.digits
  let sub := signedDifference ⟨xor a.negative b.negative,p.1⟩ ⟨xor c.negative d.negative,q.1⟩
  (sub.1,p.2+q.2+sub.2+2)

theorem cross_spec (a b c d : SignedWord) (W : ℕ)
    (ha : a.digits.length≤W) (hb : b.digits.length≤W)
    (hc : c.digits.length≤W) (hd : d.digits.length≤W) :
    (cross a b c d).1.decode=a.decode*b.decode-c.decode*d.decode ∧
    (cross a b c d).2≤32*W^2+75*W+10 := by
  let p := multiply b.digits a.digits
  let q := multiply d.digits c.digits
  let u : SignedWord := ⟨xor a.negative b.negative,p.1⟩
  let v : SignedWord := ⟨xor c.negative d.negative,q.1⟩
  obtain ⟨pv,pl,pc⟩ := multiply_spec b.digits a.digits
  obtain ⟨qv,ql,qc⟩ := multiply_spec d.digits c.digits
  obtain ⟨sv,sc⟩ := signedDifference_spec u v
  change value p.1=_ at pv
  change value q.1=_ at qv
  have up : u.decode=a.decode*b.decode := by simp only [SignedWord.decode,u,pv,signed_mul]
  have vp : v.decode=c.decode*d.decode := by simp only [SignedWord.decode,v,qv,signed_mul]
  refine ⟨sv.trans (congrArg₂ (·-·) up vp),?_⟩
  have pm : p.2≤W*(W+5*(W+2*W)) := pc.trans (Nat.mul_le_mul ha (by omega))
  have qm : q.2≤W*(W+5*(W+2*W)) := qc.trans (Nat.mul_le_mul hc (by omega))
  have len : max p.1.length q.1.length≤3*W := max_le (pl.trans (by omega)) (ql.trans (by omega))
  change (signedDifference u v).2=25*(max p.1.length q.1.length)+8 at sc
  change p.2+q.2+(signedDifference u v).2+2≤_
  nlinarith

/-- Width of an input operand of a cross product in a reachable row. -/
private theorem operand_bits {N n H : ℕ} (base : List (Elimination.Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (r.aug j).natAbs≤H) {rows : List (Elimination.Row n)}
    (reach : Elimination.SolveStep base rows) (r : Elimination.Row n) (rm : r∈rows)
    (j : Option (Fin n)) :
    (r.aug j).natAbs.size≤((base.length+1).size+H.size)*(base.length+1)+1 := by
  let m := base.length+1
  let k := (m.size+H.size)*m
  have cap : m.factorial*H^m ≤ 2^k := calc
    _ ≤ m^m*H^m := Nat.mul_le_mul_right _ m.factorial_le_pow
    _ = (m*H)^m := (mul_pow ..).symm
    _ ≤ (2^m.size*2^H.size)^m := Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.lt_size_self m).le (Nat.lt_size_self H).le) _
    _ = _ := by rw [←pow_add,←pow_mul]
  have bound := (Elimination.solve_intermediate_height base hp input reach r rm j).trans cap
  exact Nat.size_le.mpr (bound.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self k)))

def crossEntry {n : ℕ} (p r : Elimination.Row (n+1)) (j : Option (Fin n)) : ℤ × ℕ :=
  let out := cross (encode p.head) (encode (r.aug (j.map Fin.succ)))
    (encode r.head) (encode (p.aug (j.map Fin.succ)))
  (out.1.decode,out.2)

/-- Each raw augmented matrix entry is produced by the signed bit circuit. -/
theorem pivot_entry_gates {N n H : ℕ} (base : List (Elimination.Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (r.aug j).natAbs≤H) {rows : List (Elimination.Row (n+1))}
    (reach : Elimination.SolveStep base rows) (p r : Elimination.Row (n+1)) (pm : p∈rows) (rm : r∈rows)
    (j : Option (Fin n)) :
    let W := ((base.length+1).size+H.size)*(base.length+1)+1
    (crossEntry p r j).1=(p.rawPivot r).aug j ∧ (crossEntry p r j).2≤32*W^2+75*W+10 := by
  intro W
  have small (t : Elimination.Row _) (tm : t∈rows) (i) :
      (encode (t.aug i)).digits.length ≤ W := by
    simpa only [W,encode,←Nat.size_eq_bits_len] using operand_bits base hp input reach t tm i
  obtain ⟨eq,cost⟩ := cross_spec _ _ _ _ W (small p pm (some 0))
    (small r rm (j.map Fin.succ)) (small r rm (some 0)) (small p pm (j.map Fin.succ))
  refine ⟨?_,cost⟩
  simp only [decode_encode] at eq
  cases j <;> simpa [crossEntry,Elimination.Row.rawPivot,Elimination.Row.aug,Elimination.Row.head,
    Vector.get_eq_getElem] using eq

/-- Materialize the raw pivot entries from their circuits, then normalize by
the binary Euclidean/quotient circuits using the same materialized row. -/
def pivot {n : ℕ} (p r : Elimination.Row (n+1)) : Elimination.Row n × ℕ :=
  let vs := Vector.ofFn (fun i : Fin n => crossEntry p r (some i))
  let rhs := crossEntry p r none
  let raw : Elimination.Row n := ⟨vs.map Prod.fst,rhs.1⟩
  let out := normalize raw
  (out.1,out.2+rhs.2+∑ i, (vs.get i).2)

private theorem pivot_spec {N n H : ℕ} (base : List (Elimination.Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (r.aug j).natAbs≤H) {rows : List (Elimination.Row (n+1))}
    (reach : Elimination.SolveStep base rows) (p r : Elimination.Row (n+1)) (pm : p∈rows) (rm : r∈rows) :
    let W := ((base.length+1).size+H.size)*(base.length+1)+1
    let B := 2*W
    let K := (32*W^2+75*W+10)+(2*B+1)*(B*(20*B+1))
    (pivot p r).1=p.reduce r ∧ (pivot p r).2≤(n+1)*K := by
  intro W B K
  let vs := Vector.ofFn (fun i : Fin n => crossEntry p r (some i))
  let rhs := crossEntry p r none
  let raw : Elimination.Row n := ⟨vs.map Prod.fst,rhs.1⟩
  have est := pivot_entry_gates base hp input reach p r pm rm
  have rawEq : raw=p.rawPivot r := by
    have veq : vs.map Prod.fst=(p.rawPivot r).coeffs := by
      ext i hi
      simpa only [vs,Vector.getElem_map,Vector.getElem_ofFn,Elimination.Row.aug,Option.elim,Vector.get_eq_getElem]
        using (est (some ⟨i,hi⟩)).1
    exact congrArg₂ Elimination.Row.mk veq (est none).1
  have ⟨same,normCost⟩ := solve_pivot_normalization_gates base hp input reach p r pm rm
  have ⟨good,budget⟩ := normalize_spec (p.rawPivot r) same
  have norm : (normalize raw).2 ≤ (n+1)*((2*B+1)*(B*(20*B+1))) := by
    rw [rawEq,budget]
    convert normCost using 1
    dsimp [B,W]
    ring
  let C := 32*W^2+75*W+10
  have rhsCost : rhs.2≤C := (est none).2
  have coeffs : (∑ i : Fin n, (vs.get i).2)≤n*C := by
    have each (i : Fin n) : (vs.get i).2≤C := by
      simpa [vs,C,W,Vector.get_eq_getElem] using (est (some i)).2
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i)
  change (normalize raw).1=p.reduce r ∧ (normalize raw).2+rhs.2+∑ i, (vs.get i).2≤_
  refine ⟨rawEq ▸ good,?_⟩
  change _ ≤ (n+1)*(C+(2*B+1)*(B*(20*B+1)))
  nlinarith only [norm,rhsCost,coeffs]

private theorem sum_bound {α : Type*} (xs : List α) (f : α → ℕ) (k : ℕ)
    (bounded : ∀ x∈xs, f x≤k) : (xs.map f).sum≤xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (bounded x (by simp)) (ih (fun y hy => bounded y (by simp [hy])))

/-- All fraction-free cross products and normalizations use binary circuits;
a free column still follows the solver's existing drop branch. -/
def solve : (n : ℕ) → List (Elimination.Row n) → Option (Elimination.Family n) × ℕ
  | 0, rows => (Elimination.solve 0 rows,0)
  | n+1, rows =>
    match rows.find? (fun r => r.head != 0) with
    | none =>
      let tail := solve n (rows.map Elimination.Row.drop)
      (tail.1.map Elimination.freeLift,tail.2)
    | some p =>
      let reduced := rows.map (pivot p)
      let tail := solve n (reduced.map Prod.fst)
      (tail.1.map (Elimination.pivotLift p),(reduced.map Prod.snd).sum+tail.2)

/-- Boolean gates for the cross products and all normalization divisions on
every forward path, with agreement on the returned family or failure. -/
theorem solve_pivot_gates {N H : ℕ} (base : List (Elimination.Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (r.aug j).natAbs≤H) {n : ℕ} {rows : List (Elimination.Row n)}
    (reach : Elimination.SolveStep base rows) :
    let W := ((base.length+1).size+H.size)*(base.length+1)+1
    let B := 2*W
    let K := (32*W^2+75*W+10)+(2*B+1)*(B*(20*B+1))
    (solve n rows).1=Elimination.solve n rows ∧ (solve n rows).2≤rows.length*n*(n+1)*K := by
  intro W B K
  induction n with
  | zero => simp [solve]
  | succ n ih =>
    rw [solve,Elimination.solve]
    cases found : rows.find? (fun r => r.head != 0) with
    | none =>
      obtain ⟨ok,work⟩ := ih (Elimination.SolveStep.drop reach found)
      simp only [List.length_map] at work
      exact ⟨congrArg (Option.map Elimination.freeLift) ok,work.trans (by nlinarith [Nat.zero_le (rows.length*n*K), Nat.zero_le (rows.length*K)])⟩
    | some p =>
      have pm := List.mem_of_find?_eq_some found
      have one := fun r hr => pivot_spec base hp input reach p r pm hr
      have eq : (rows.map (pivot p)).map Prod.fst=rows.map p.reduce := by
        rw [List.map_map]; exact List.map_congr_left (fun r hr => (one r hr).1)
      have next := eq.symm ▸ Elimination.SolveStep.pivot reach found
      obtain ⟨ok,work⟩ := ih next
      have cost := sum_bound rows (fun r => (pivot p r).2) ((n+1)*K) (fun r hr => (one r hr).2)
      simp only [List.length_map] at work
      change ((solve n ((rows.map (pivot p)).map Prod.fst)).1.map (Elimination.pivotLift p) = _) ∧
        ((rows.map (pivot p)).map Prod.snd).sum+(solve n ((rows.map (pivot p)).map Prod.fst)).2 ≤ _
      refine ⟨by rw [ok,eq],?_⟩
      rw [List.map_map]
      change (rows.map (fun r => (pivot p r).2)).sum + _ ≤ _
      nlinarith only [cost,work,Nat.zero_le (rows.length*n*K),Nat.zero_le (rows.length*K)]

/-- Specialize the Boolean-circuit bound to the zero/one augmented system
assembled from the exact stage-one output. -/
theorem stageTwo_pivot_gates (s : Marking.Relations) :
    let m := s.rows.length+1
    let n := s.marks.length
    let W := ((m+1).size+1)*(m+1)+1
    let B := 2*W
    let K := (32*W^2+75*W+10)+(2*B+1)*(B*(20*B+1))
    let out := solve n (Elimination.relationRows s)
    out.1.map Elimination.Family.integers = Elimination.stageTwo s ∧ out.2 ≤ m*n*(n+1)*K := by
  intro m n W B K out
  have height (r : Elimination.Row n) (hr : r∈Elimination.relationRows s) (j : Option (Fin n)) :
      (r.aug j).natAbs≤1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    cases j with
    | none =>
      change (-(s.rhs i)).natAbs≤1
      induction i using Fin.cases with
      | zero => change (0:ℕ)≤1; decide
      | succ i => dsimp [Marking.Relations.rhs]; split <;> decide
    | some k =>
      change ((Vector.ofFn (s.matrix i)).get k).natAbs≤1
      simp only [Vector.get_eq_getElem,Vector.getElem_ofFn]
      induction i using Fin.cases with
      | zero => change (1:ℕ)≤1; decide
      | succ i => dsimp [Marking.Relations.matrix]; split <;> decide
  have ⟨val,gates⟩ := solve_pivot_gates (Elimination.relationRows s) (H:=1) le_rfl height Elimination.SolveStep.start
  refine ⟨congrArg (Option.map Elimination.Family.integers) val,?_⟩
  simpa [out,K,B,W,m,n,Elimination.relationRows] using gates

end Cogentic.BinaryPivot

#print axioms Cogentic.BinaryPivot.cross_spec
#print axioms Cogentic.BinaryPivot.solve_pivot_gates

#print axioms Cogentic.BinaryPivot.stageTwo_pivot_gates
