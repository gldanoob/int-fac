import Cogentic.MinorReconstructionCost

namespace Cogentic.Concrete
open Elimination BinaryReconstruction

namespace SolverGrowth

def Within (s k a : ℕ) : Prop := a≤2^(k*s)

theorem weaken {s k l a} (h : Within s k a) (le : k≤l) : Within s l a :=
  h.trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right s le))

theorem product {s k l a b : ℕ} (x : Within s k a) (y : Within s l b) : Within s (k+l) (a*b) := by
  exact (Nat.mul_le_mul x y).trans_eq (by rw [←pow_add,Nat.add_mul])

theorem plus {s k l a b : ℕ} (pos : 0<s) (x : Within s k a) (y : Within s l b) :
    Within s (k+l+1) (a+b) := by
  have u := weaken x (Nat.le_add_right k l)
  have v := weaken y (Nat.le_add_left l k)
  unfold Within at *
  exact (Nat.add_le_add u v).trans (calc
    _ = 2^(1+(k+l)*s) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by simp only [Nat.add_mul,one_mul]; omega))

theorem top {s k l a b : ℕ} (x : Within s k a) (y : Within s l b) : Within s (k+l) (max a b) :=
  max_le (weaken x (Nat.le_add_right ..)) (weaken y (Nat.le_add_left ..))

theorem smaller {s k a b} (x : Within s k b) (le : a≤b) : Within s k a := le.trans x

theorem numeral (s c : ℕ) (pos : 0<s) : Within s c c :=
  (Nat.lt_two_pow_self (n:=c)).le.trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_mul_of_pos_right c pos))

theorem bitLength {s k a : ℕ} (x : Within s k a) : Within s k a.size :=
  smaller x (Nat.size_le.mpr Nat.lt_two_pow_self)

theorem productLength {s k l a b : ℕ} (pos : 0<s) (x : Within s k a.size) (y : Within s l b.size) :
    Within s (k+l+1) (a*b).size := by
  apply smaller (plus pos x y)
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (Nat.lt_size_self _).le (Nat.two_pow_pos _)

theorem succLength {s k a : ℕ} (pos : 0<s) (x : Within s k a.size) : Within s (k+2) (a+1).size := by
  apply smaller (plus pos x (numeral s 1 pos))
  apply Nat.size_le.mpr
  rw [pow_succ]
  have := Nat.lt_size_self a
  omega

theorem factorialLength {s k a : ℕ} (pos : 0<s) (x : Within s k a) : Within s (k+k+2) a.factorial.size := by
  have b : a.factorial ≤ 2^(a*a) := calc
    _ ≤ a^a := Nat.factorial_le_pow _
    _ ≤ (2^a)^a := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=a)).le _
    _ = _ := by rw [←pow_mul]
  exact smaller (plus pos (product x x) (numeral s 1 pos)) (by
    simpa only [Nat.size_pow] using Nat.size_le_size b)

theorem powerLength {s k a : ℕ} (pos : 0<s) (x : Within s k a) : Within s (k+2) (2^a).size := by
  simpa only [Nat.size_pow] using plus pos x (numeral s 1 pos)

theorem smallPower {s k a : ℕ} (r : ℕ) (x : Within s k a) : Within s (k*r) (a^r) := by
  exact (Nat.pow_le_pow_left x r).trans_eq (by rw [←pow_mul]; congr 1; ring)

end SolverGrowth

open SolverGrowth

private theorem verification_polynomial {d h w V cap a n W : ℕ}
    (dd : d≤W) (hh : h≤W) (ww : w≤W) (vv : V≤W) (cc : cap≤W) (aa : a≤W) (nn : n≤W) :
    1+d*(coordinateBudget h+BinaryCollector.lcmBudget w+3)+(16*V^2+7*(cap+3*V+2)+cap+3)+
      3*(3*V+1)+BinaryModularPower.powerBudget a (cap+1) n+n+(cap+1)+7 ≤ 1000000*(W+1)^6 := by
  calc
    _ ≤ 1+W*(coordinateBudget W+BinaryCollector.lcmBudget W+3)+(16*W^2+7*(W+3*W+2)+W+3)+
      3*(3*W+1)+BinaryModularPower.powerBudget W (W+1) W+W+(W+1)+7 := by
        dsimp only [coordinateBudget,BinaryCollector.lcmBudget,BinaryModularPower.gcdBudget,BinaryModularPower.powerBudget]
        gcongr
    _ ≤ _ := by
      dsimp only [coordinateBudget,BinaryCollector.lcmBudget,BinaryModularPower.gcdBudget,BinaryModularPower.powerBudget]
      ring_nf; omega

/-- Gate count of the full reconstruction and modular check on each rounded
minor returned by the solver on an actual boxed candidate. -/
theorem constructed_minor_verify_gates {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ {lat}, stageTwo rel=some lat →
    ∀ {cols}, markColumns s rel=some cols →
    let P := TryPair.localBits s rel
    ∀ {indices x}, solveColumns (observation cols lat.particular P)
        (lat.directions.map (fun direction=>observation cols direction P)) indices=some x →
      (verified n ell x (TryPair.denominatorCap s rel) lat.scale (min P (Fixed.precision (n.log2+1)))).2
        ≤ 2^(99999999*TwoThirdsCost.scale (n.log2+1)) := by
  intro s rel stage lat solved cols computed P indices x found
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have pos : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have bBound : Within S 1 b := (Nat.lt_log2_self (n:=b)).le.trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by simpa only [one_mul,Fixed.z] using zs))
  have nBound : Within S 1 n.size := smaller bBound (Nat.size_le.mpr Nat.lt_log2_self)
  have dBound : Within S 1 s.degree := smaller bBound (Fixed.degree_le_bits _)
  have bBits : Within S 1 s.L₀ := bBound
  have BBound : Within S 1000 s.B := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs)
  have targetBound : Within S 1000 ell := smaller BBound (mem_dyadicTargets.mp target).2.2
  have marks : Within S 10000 rel.marks.length := (retained_size stage).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs))
  have rows := smaller (product (numeral S 2 pos) (smallPower 2 (plus pos BBound (numeral S 1 pos))))
    (ArchPrecision.retained_rows stage)
  let d := 2*s.degree-2
  have dim := smaller (product (numeral S 2 pos) dBound) (Nat.sub_le (2*s.degree) 2)
  let R := rel.rows.length+1
  have rBound := plus pos rows (numeral S 1 pos)
  let H := rel.marks.length*R.factorial*(2*s.degree*(s.L₀+1)+1)*2^P+1
  have one := numeral S 1 pos
  have precision : Within S 2100 P := weaken
    (product (product (product (numeral S 64 pos) (smallPower 3 dBound)) rBound) bBits) (by decide)
  have logSize := plus pos (product (product (numeral S 2 pos) dBound) (plus pos bBits one)) one
  have magnitude : Within S 25000 H.size := weaken (succLength pos (productLength pos
    (productLength pos (productLength pos (bitLength marks) (factorialLength pos rBound)) (bitLength logSize))
    (powerLength pos precision))) (by decide)
  have eBound : Within S 5000 lat.scale.size :=
    smaller (weaken (factorialLength pos rBound) (by decide)) (Nat.size_le_size (stageTwo_height solved).1.1)
  let Q := TryPair.denominatorCap s rel
  have qBound : Within S 2100 Q.size := weaken
    (powerLength pos (product (product (product (numeral S 3 pos) dBound) rBound) bBits)) (by decide)
  let cap := min P (Fixed.precision b)
  have capBound : Within S 2100 cap := smaller precision (min_le_left ..)
  let h := max Q.size (fillExponent d d H+1)
  have dim1 := plus pos dim one
  have dimBits := bitLength dim1
  have fill := plus pos (product dimBits dim1) (product (product (plus pos dimBits magnitude) dim1) dim)
  have hBound : Within S 30000 h := weaken (top qBound (plus pos fill one)) (by decide)
  have width := constructed_minor_width hn big target box stage solved computed found
  have checked := (verified_proposal_spec n ell (by omega) x Q lat.scale cap h (le_max_left ..)
    (fun i=>⟨(width i).1.trans (le_max_right ..),(width i).2.trans (le_max_right ..)⟩)).2
  let W := 2^(30000*S)
  let w := 1+Q.size*(d+1)
  let V := max lat.scale.size w
  have wBound : Within S 2200 w := weaken (plus pos one (product qBound dim1)) (by decide)
  have vb : V≤W := weaken (top eBound wBound) (by decide)
  have wb : w≤W := weaken wBound (by decide)
  have cb : cap≤W := weaken capBound (by decide)
  have db : d≤W := weaken dim (by decide)
  have nb : n.size≤W := weaken nBound (by decide)
  have eb : ell.size≤W := weaken (bitLength targetBound) (by decide)
  have hh : h≤W := hBound
  change (verified n ell x Q lat.scale cap).2 ≤ 2^(99999999*S)
  exact checked.trans ((verification_polynomial db hh wb vb cb eb nb).trans
    (weaken (product (numeral S 1000000 pos) (smallPower 6
      (plus pos (show Within S 30000 W from le_rfl) one))) (by decide)))

/-- The successful output of the minor search comes from an actual solved minor. -/
theorem selected_solution {dim free n g Q e bits : ℕ} {rhs : Vector ℤ dim}
    {cols : Vector (Vector ℤ dim) free} {indices : List (List (Fin free))} {x : Fin dim → ℚ}
    (hit : indices.findSome? (verifiedColumns n g Q e bits rhs cols)=some x) :
    ∃ i∈indices, solveColumns rhs cols i=some x := by
  obtain ⟨i,hi,found⟩ := List.exists_of_findSome?_eq_some hit
  unfold verifiedColumns at found
  obtain ⟨v,solved,test⟩ := Option.bind_eq_some_iff.mp found
  refine ⟨i,hi,?_⟩
  split at test
  next => cases test; exact solved
  next => cases test

/-- Sum the checks over every solved minor and charge the returned solution
again for reconstruction in `TryPair.finish` and verification in `searchBox`. -/
def minorVerificationWork (s : Marking.Input) (rel : Marking.Relations)
    (lat : IntegerFamily rel.marks.length) (cols : Vector (Vector ℚ (2*s.degree-2)) rel.marks.length) : ℕ :=
  let P := TryPair.localBits s rel
  let rhs := observation cols lat.particular P
  let obs := lat.directions.map (fun dir=>observation cols dir P)
  let choices := selections (2*s.degree-2) lat.free
  let Q := TryPair.denominatorCap s rel
  let bits := min P (Fixed.precision (s.n.log2+1))
  let cost := fun x => (verified s.n s.target x Q lat.scale bits).2
  (choices.map fun indices=>
    match solveColumns rhs obs indices with
    | none => 0
    | some x => cost x).sum +
    match choices.findSome? (verifiedColumns s.n s.target Q lat.scale bits rhs obs) with
    | none => 0
    | some x => cost x

theorem all_minor_verification_gates {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b:=n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s=some rel → ∀ {lat}, stageTwo rel=some lat →
    ∀ {cols}, markColumns s rel=some cols → lat.free<rel.marks.length →
      minorVerificationWork s rel lat cols ≤ 2^(100020000*TwoThirdsCost.scale (n.log2+1)) := by
  intro s rel stage lat solved cols marked guard
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  let C := 2^(99999999*S)
  let P := TryPair.localBits s rel
  let rhs := observation cols lat.particular P
  let obs := lat.directions.map (fun dir=>observation cols dir P)
  let choices := selections (2*s.degree-2) lat.free
  let Q := TryPair.denominatorCap s rel
  let bits := min P (Fixed.precision b)
  let finalPass := match choices.findSome? (verifiedColumns n ell Q lat.scale bits rhs obs) with
    | none => 0
    | some x => (verified n ell x Q lat.scale bits).2
  let g (idx : List (Fin lat.free)) := match solveColumns rhs obs idx with
    | none => 0
    | some x => (verified n ell x (TryPair.denominatorCap s rel) lat.scale (min P (Fixed.precision b))).2
  have pay (idx) : g idx≤C := by
    dsimp only [g]; split
    next => exact Nat.zero_le _
    next x eq => exact constructed_minor_verify_gates hn big target box stage solved marked eq
  have total (xs : List (List (Fin lat.free))) : (xs.map g).sum≤xs.length*C := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (pay x) ih
  have vs := (Fixed.scale_bounds (show 0<b from Nat.succ_pos _)).1
  have number := (per_candidate_minor_count stage guard).trans (Nat.pow_le_pow_right Nat.zero_lt_two
    (Nat.mul_le_mul_left 20000 vs))
  have last : finalPass≤C := by
    unfold finalPass
    split
    next => exact Nat.zero_le _
    next x hit =>
      obtain ⟨i,_,eq⟩ := selected_solution hit
      exact constructed_minor_verify_gates hn big target box stage solved marked eq
  have subtotal : (choices.map g).sum≤2^(100019999*S) :=
    (total _).trans ((Nat.mul_le_mul_right C number).trans_eq (by dsimp [C,S,b]; rw [←pow_add]; congr 1; omega))
  have cap : C≤2^(100019999*S) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have pos : 0<S := (Nat.succ_pos _ : 0<Fixed.z b).trans_le
    ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans
      ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos (Nat.succ_pos _))).trans vs))
  change (choices.map g).sum+finalPass≤2^(100020000*S)
  exact (Nat.add_le_add subtotal (last.trans cap)).trans (calc
    _ = 2^(1+100019999*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))

end Cogentic.Concrete
