import Cogentic.BinaryBackSubstitution
import Cogentic.IntegerFamilyCost
import Cogentic.SolverStageParameters
import Cogentic.MinorEnumerationCost

namespace Cogentic.SolverStage
open Elimination BinaryIntegerFamily BinaryRational Concrete Concrete.SolverGrowth Finset

/-- Convert the materialized binary point and directions directly to integer
columns, sharing each computed word vector with its denominator fold. -/
def materializeIntegers {n : ℕ} (c : FillProgram n) :=
  let f := materialize c
  let p := integerizeWords f.1.1.get
  let ds := Vector.ofFn (fun j => integerizeWords (f.1.2.get j).get)
  ((p.1,ds.map Prod.fst),f.2+(p.2+∑ j,(ds.get j).2))

theorem materializeIntegers_value {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H) {c : FillProgram n}
    (found : compileFill n rows = some c) :
    (materializeIntegers c).1 =
      (encodedColumn c.family.point,Vector.ofFn (fun j => encodedColumn (c.family.direction j))) := by
  obtain ⟨p,d⟩ := materialize_values rows hp input found
  apply Prod.ext
  · change (integerizeWords _).1=_
    rw [funext p]
    exact integerize_value _
  · apply Vector.ext
    intro i hi
    simp only [materializeIntegers,Vector.getElem_map,Vector.getElem_ofFn]
    change (integerizeWords ((materialize c).1.2.get ⟨i,hi⟩).get).1 = _
    rw [funext (d ⟨i,hi⟩)]
    exact integerize_value _

private theorem integerWork_eq {n H : ℕ} (rows : List (Row n)) (hp : 1 ≤ H)
    (input : ∀ r ∈ rows, ∀ j, (r.aug j).natAbs ≤ H) {c : FillProgram n}
    (found : compileFill n rows = some c) :
    (materializeIntegers c).2 = materializeWork c + familyWork c.family := by
  obtain ⟨p,d⟩ := materialize_values rows hp input found
  dsimp only [materializeIntegers,materializeWork,familyWork,integerize,
    Vector.get_eq_getElem,Vector.getElem_ofFn]
  rw [funext p]
  congr 2
  apply sum_congr rfl
  intro j _
  simp only [Vector.getElem_ofFn]
  change (integerizeWords ((materialize c).1.2.get j).get).2 = _
  rw [funext (d j)]
  rfl

/-- Charge all forward pivot gates, all solved columns and their integer
representations. In a square minor this also upper-bounds the unique point
requested by the search when the other directions are discarded. -/
def solverWork {n : ℕ} (rows : List (Row n)) : ℕ :=
  let forward := binarySolve n rows
  forward.2 + match forward.1 with
    | none => 0
    | some c => (materializeIntegers c).2

private theorem uniform_work {n H S : ℕ} (rows : List (Row n)) (hp : 1≤H)
    (input : ∀ r∈rows,∀ j,(r.aug j).natAbs≤H) (pos : 0<S)
    (dims : Within S 30000 n) (counts : Within S 30000 rows.length) (height : Within S 30000 H.size) :
    Within S 10000000 (solverWork rows) := by
  let m := rows.length
  let E := fillExponent n m H
  let W := fillWidth n m H
  let V := ((m+1).size+H.size)*(m+1)+1
  let B := 2*V
  let K := (32*V^2+75*V+10)+(2*B+1)*(B*(20*B+1))
  let pay := n*(n+1)*budget W
  let one := numeral S 1 pos
  let two := numeral S 2 pos
  let plus1 := plus pos dims one
  let m1 := plus pos counts one
  have naturalE : Within S 200000 E := weaken (plus pos
    (product (bitLength plus1) plus1)
    (product (product (plus pos (bitLength m1) height) m1) dims)) (by decide)
  have Wb : Within S 400000 W := by
    let n2 := plus pos plus1 one
    have Eh := plus pos (product (bitLength n2) n2)
      (product (product (plus pos (bitLength m1) height) m1) plus1)
    exact weaken (plus pos (product two Eh) (numeral S 3 pos)) (by decide)
  have bgt : Within S 2300000 (budget W) := by
    exact weaken (product (smallPower 20 two) (smallPower 3 (plus pos Wb one))) (by decide)
  have paid : Within S 2400000 pay := weaken (product (product dims plus1) bgt) (by decide)
  have material := plus pos paid (product dims (plus pos paid (product dims bgt)))
  have limb := plus pos (product two naturalE) two
  let I := 2*E+2
  have li : Within S 210000 I := weaken limb (by decide)
  have ilim : BinaryCollector.lcmBudget I + I*(20*I+1) + 16*I^2 + 9*I+2 ≤ 512*(I+1)^3 := by
    unfold BinaryCollector.lcmBudget BinaryModularPower.gcdBudget; ring_nf; omega
  have integers := product plus1 (product dims (smaller
    (product (numeral S 512 pos) (smallPower 3 (plus pos li one))) ilim))
  have vlim := plus pos (product (plus pos (bitLength m1) height) m1) one
  have pb : K ≤ 1024*(V+1)^3 := by dsimp only [K,B]; ring_nf; omega
  have pivots := product (product (product counts dims) plus1)
    (smaller (product (numeral S 1024 pos) (smallPower 3 (plus pos vlim one))) pb)
  obtain ⟨_,forward⟩ := BinaryPivot.solve_pivot_gates rows hp input .start
  obtain ⟨agrees,loop⟩ := binarySolve_spec rows hp input .start
  have scans := product plus1 (plus pos (product two counts) one)
  have front := smaller (plus pos (smaller pivots forward) scans) loop
  unfold solverWork
  dsimp only
  rw [agrees]
  split
  next => simpa using (weaken front (by decide : _ ≤ 10000000))
  next c success =>
    rw [integerWork_eq rows hp input success]
    have ok : solve n rows = some c.family := by rw [← compileFill_value,success]; rfl
    have all := plus pos front (plus pos (smaller material (materialize_gates rows hp input success))
      (smaller integers (solve_integerization_gates rows hp input ok)))
    exact weaken all (by decide)

/-- Every reached stage-two solve, including a rejected system, meets one
fixed binary gate bound on the integer schedule. -/
theorem relation_work {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n g pair) = some rel) :
    solverWork (relationRows rel) ≤ 2^(10000000*TwoThirdsCost.scale (n.log2+1)) := by
  obtain ⟨pos,dim,rows,_,_⟩ := fixed_parameters stage
  exact uniform_work (relationRows rel) (H:=1) le_rfl (BinaryPivot.relation_height rel) pos dim
    (by simpa only [Within,relationRows,List.length_ofFn] using rows) (weaken (numeral _ 1 pos) (by decide))

def minorWork {d f : ℕ} (rhs : Vector ℤ d) (cols : Vector (Vector ℤ d) f)
    (indices : List (Fin f)) : ℕ :=
  if h : indices.length = d then solverWork (minorRows rhs cols ((Vector.ofFn indices.get).cast h))
  else 0

/-- All rounded-minor solves pay for their pivot and backward paths, even
when singular or when the later certificate verifier rejects the answer. -/
theorem minor_work {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ {lat}, stageTwo rel=some lat →
    ∀ {cols}, markColumns s rel=some cols →
    ∀ idx, minorWork (observation cols lat.particular (TryPair.localBits s rel))
        (lat.directions.map (fun dir => observation cols dir (TryPair.localBits s rel))) idx
        ≤ 2^(10000000*TwoThirdsCost.scale (n.log2+1)) := by
  intro s rel stage lat solved cols marked idx
  obtain ⟨pos,_,_,dim,Hw⟩ := fixed_parameters stage
  obtain ⟨rhs,cs⟩ := constructed_observation_height hn big target box stage solved marked
  unfold minorWork
  split
  next h =>
    apply uniform_work _ (by omega) _ pos dim (by simpa only [Within,minorRows,List.length_ofFn] using dim) Hw
    intro row mem j
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    cases j with
    | none => simpa only [Row.aug,Option.elim_none,Int.natAbs_neg] using rhs i
    | some k => simpa only [Row.aug,Option.elim_some,Vector.get_eq_getElem,Vector.getElem_ofFn] using (cs (((Vector.ofFn idx.get).cast h).get k) i)
  next => exact Nat.zero_le _

end Cogentic.SolverStage

#print axioms Cogentic.SolverStage.materializeIntegers_value
#print axioms Cogentic.SolverStage.relation_work
#print axioms Cogentic.SolverStage.minor_work
