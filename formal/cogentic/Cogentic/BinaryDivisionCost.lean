import Cogentic.EliminationWork

/-! Restoring long division on little-endian bit lists. The counter charges
Boolean gates in the full subtractor, the restoring multiplexers and quotient bit.
List storage and conversion between naturals and bit lists are outside the model. -/
namespace Cogentic.BinaryDivision

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2*value bs

@[simp] theorem value_bits (a : ℕ) : value a.bits = a := by
  induction a using Nat.binaryRec' with
  | zero => simp [value]
  | bit b a ha ih =>
    rw [Nat.bits_append_bit _ _ ha]
    cases b <;> simp [value, ih, Nat.add_comm]

theorem value_lt (xs : List Bool) : value xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [value, pow_succ] <;> omega

structure Difference where
  digits : List Bool
  borrow : Bool
  gates : ℕ

/-- Zero-extended ripple-borrow subtractor. Each column uses two XORs, a
NOT, two ANDs and two ORs. Each input list is read from least significant bit. -/
def subtract : ℕ → List Bool → List Bool → Bool → Difference
  | 0, _, _, borrow => ⟨[], borrow, 0⟩
  | w+1, xs, ys, borrow =>
    let x := xs.headD false
    let y := ys.headD false
    let difference := xor (xor x y) borrow
    let next := (!x && (y || borrow)) || (y && borrow)
    let tail := subtract w xs.tail ys.tail next
    ⟨difference :: tail.digits, tail.borrow, tail.gates+7⟩

private theorem column_eq (x y b : Bool) :
    (xor (xor x y) b).toNat + y.toNat + b.toNat =
    x.toNat + 2*((!x && (y || b)) || (y && b)).toNat := by
  cases x <;> cases y <;> cases b <;> decide

theorem value_head (xs : List Bool) :
    value xs = (xs.headD false).toNat + 2*value xs.tail := by
  cases xs <;> rfl

theorem subtract_spec (w : ℕ) (xs ys : List Bool) (b : Bool)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) :
    let out := subtract w xs ys b
    out.digits.length = w ∧ out.gates = 7*w ∧
    value out.digits + value ys + b.toNat = value xs + 2^w*out.borrow.toNat := by
  induction w generalizing xs ys b with
  | zero =>
    have xnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have ynil : ys = [] := List.length_eq_zero_iff.mp (by omega)
    simp [xnil, ynil, value, subtract]
  | succ w ih =>
    let x := xs.headD false
    let y := ys.headD false
    let c := (!x && (y || b)) || (y && b)
    have ⟨len, work, eq⟩ := ih xs.tail ys.tail c (by simp; omega) (by simp; omega)
    have col := column_eq x y b
    let tail := subtract w xs.tail ys.tail c
    change ((xor (xor x y) b) :: tail.digits).length = _ ∧ tail.gates+7 = _ ∧
      value ((xor (xor x y) b) :: tail.digits) + value ys + b.toNat = value xs + _*tail.borrow.toNat
    refine ⟨by simpa [tail] using congrArg Nat.succ len, by simp [tail, Nat.mul_succ, work], ?_⟩
    rw [value, value_head ys, value_head xs, pow_succ]
    change value tail.digits + value ys.tail + c.toNat = value xs.tail + 2^w*tail.borrow.toNat at eq
    change _ + y.toNat + b.toNat = x.toNat + 2*c.toNat at col
    change _ + _ + (y.toNat + _) + _ = x.toNat + _ + _ * 2 * tail.borrow.toNat
    rw [mul_right_comm (2^w) 2]
    omega

def selectDigits : ℕ → Bool → Bool → List Bool → List Bool → List Bool × ℕ
  | 0, _, _, _, _ => ([], 0)
  | w+1, f, g, xs, ys =>
    let tail := selectDigits w f g xs.tail ys.tail
    (((f && xs.headD false) || (g && ys.headD false)) :: tail.1, tail.2+3)

theorem select_spec (w : ℕ) (f : Bool) (xs ys : List Bool)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) :
    let result := selectDigits w f (!f) xs ys
    result.1.length = w ∧ result.2 = 3*w ∧ value result.1 = if f then value xs else value ys := by
  induction w generalizing xs ys with
  | zero =>
    have xnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have ynil : ys = [] := List.length_eq_zero_iff.mp (by omega)
    simp [selectDigits, xnil, ynil, value]
  | succ w ih =>
    obtain ⟨len, gates, val⟩ := ih xs.tail ys.tail (by simp; omega) (by simp; omega)
    dsimp only [selectDigits]
    refine ⟨by simp [len], by simp [gates, Nat.mul_succ], ?_⟩
    rw [value, val, value_head xs, value_head ys]
    cases f <;> simp

structure Division where
  quotient : List Bool
  remainder : List Bool
  width : ℕ
  gates : ℕ

/-- Each new input digit tries doubling the previous remainder and subtracting
the divisor. The final borrow selects the remainder and its complement is the
new quotient bit. Width grows by one per digit to avoid a normalization scan. -/
def divide (divisor : List Bool) : List Bool → Division
  | [] => ⟨[], [], divisor.length, 0⟩
  | b :: hi =>
    let prev := divide divisor hi
    let candidate := b :: prev.remainder
    let width := prev.width+1
    let trial := subtract width candidate divisor false
    let take := !trial.borrow
    let selected := selectDigits width trial.borrow take candidate trial.digits
    ⟨take :: prev.quotient, selected.1, width, prev.gates+trial.gates+selected.2+1⟩

set_option maxHeartbeats 800000 in
theorem divide_spec (d xs : List Bool) (hd : 0 < value d) :
    let out := divide d xs
    out.width = d.length+xs.length ∧ out.remainder.length ≤ out.width ∧
    value xs = value out.quotient*value d + value out.remainder ∧ value out.remainder < value d ∧
    out.gates ≤ xs.length*(10*(d.length+xs.length)+1) := by
  induction xs with
  | nil => simp [divide, value, hd]
  | cons b xs ih =>
    let prev := divide d xs
    let candidate := b :: prev.remainder
    let trial := subtract (prev.width+1) candidate d false
    obtain ⟨width, len, decomp, small, cost⟩ := ih
    change prev.width = d.length+xs.length at width
    change prev.remainder.length ≤ prev.width at len
    have hc : candidate.length ≤ prev.width+1 := by simp [candidate]; exact len
    have hd' : d.length ≤ prev.width+1 := by omega
    obtain ⟨tlen, tcost, eq⟩ := subtract_spec (prev.width+1) candidate d false hc hd'
    change trial.digits.length = prev.width+1 at tlen
    change trial.gates = 7*(prev.width+1) at tcost
    change value trial.digits + value d + false.toNat = value candidate + 2^(prev.width+1)*trial.borrow.toNat at eq
    have rlt := value_lt trial.digits
    rw [tlen] at rlt
    have bsmall : b.toNat ≤ 1 := by cases b <;> decide
    change value prev.remainder < value d at small
    change value xs = value prev.quotient*value d + value prev.remainder at decomp
    change prev.gates ≤ xs.length*(10*(d.length+xs.length)+1) at cost
    let selected := selectDigits (prev.width+1) trial.borrow (!trial.borrow) candidate trial.digits
    obtain ⟨slen, scost, sval⟩ := select_spec (prev.width+1) trial.borrow candidate trial.digits hc tlen.le
    change value selected.1 = if trial.borrow then value candidate else value trial.digits at sval
    have cost' : prev.gates+trial.gates+selected.2+1 ≤ (xs.length+1)*(10*(d.length+(xs.length+1))+1) := by
      change selected.2 = _ at scost
      rw [tcost, scost, width]
      nlinarith
    change prev.width+1 = _ ∧ selected.1.length ≤ prev.width+1 ∧
      value (b::xs) = value ((!trial.borrow)::prev.quotient)*value d + value selected.1 ∧
      value selected.1 < value d ∧ _
    refine ⟨by simp [width, Nat.add_assoc], slen.le, ?_⟩
    rw [sval]
    cases hb : trial.borrow
    · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at eq
      simp only [if_false, Bool.false_eq_true, Bool.not_false, value, Bool.toNat_true]
      refine ⟨?_, ?_, cost'⟩
      · dsimp [candidate, value] at eq
        nlinarith
      · dsimp [candidate, value] at eq
        omega
    · simp only [hb, Bool.toNat_true, Nat.mul_one, Bool.toNat_false, Nat.add_zero] at eq
      simp only [if_true, Bool.not_true, value, Bool.toNat_false, Nat.zero_add]
      refine ⟨?_, by omega, cost'⟩
      dsimp [candidate, value]
      rw [decomp]
      ring

/-- A concrete binary implementation of the two operations used by Euclidean
normalization. The bound is quadratic in the operand bit lengths. -/
theorem divide_naturals (a d : ℕ) (positive : 0 < d) :
    let out := divide d.bits a.bits
    value out.quotient = a/d ∧ value out.remainder = a%d ∧
    out.gates ≤ a.size*(10*(d.size+a.size)+1) := by
  have ⟨_, _, decomp, small, cost⟩ := divide_spec d.bits a.bits (by simpa using positive)
  simp only [value_bits] at decomp small
  let out := divide d.bits a.bits
  change a = value out.quotient*d + value out.remainder at decomp
  change value out.remainder < d at small
  refine ⟨?_, ?_, ?_⟩
  · conv_rhs => rw [decomp, Nat.mul_comm (value out.quotient) d, Nat.mul_add_div positive, Nat.div_eq_of_lt small, Nat.add_zero]
  · conv_rhs => rw [decomp, Nat.mul_comm (value out.quotient) d, Nat.mul_add_mod, Nat.mod_eq_of_lt small]
  · simpa only [←Nat.size_eq_bits_len] using cost

/-- A Euclidean gcd that uses the restoring divider for every nonzero
divisor. The counter records the gates of those individual divisions. -/
def gcdViaDivision (a b : ℕ) : ℕ × ℕ :=
  if _zero : a = 0 then (b, 0) else
    let out := divide a.bits b.bits
    let rest := gcdViaDivision (value out.remainder) a
    (rest.1, rest.2+out.gates)
termination_by a
decreasing_by
  have rem := (divide_naturals b a (Nat.pos_of_ne_zero _zero)).2.1
  exact rem.trans_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero _zero))

private theorem gcdViaDivision_spec (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (gcdViaDivision a b).1 = a.gcd b ∧
    (gcdViaDivision a b).2 ≤ (Elimination.gcdWithCount a b).2*(B*(20*B+1)) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    rw [gcdViaDivision, Elimination.gcdWithCount]
    by_cases hz : a = 0
    · simp [hz]
    · have pos := Nat.pos_of_ne_zero hz
      let out := divide a.bits b.bits
      have ⟨_, rem, cost⟩ := divide_naturals b a pos
      have small := Nat.mod_lt b pos
      obtain ⟨val, budget⟩ := ih (b%a) small a ((Nat.size_le_size small.le).trans ha) ha
      have gates : out.gates ≤ B*(20*B+1) := cost.trans (Nat.mul_le_mul hb (by omega))
      simp only [hz, ↓reduceDIte, rem, val]
      refine ⟨(Nat.gcd_rec ..).symm, ?_⟩
      change (gcdViaDivision (b%a) a).2 + out.gates ≤ _
      rw [Nat.succ_mul]
      exact Nat.add_le_add budget gates

/-- Bounds the Boolean division gates used throughout the Euclidean algorithm
for two operands of at most B bits. -/
theorem gcd_division_gates (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (gcdViaDivision a b).1 = a.gcd b ∧ (gcdViaDivision a b).2 ≤ 2*B*(B*(20*B+1)) := by
  have spec := gcdViaDivision_spec a b B ha hb
  exact ⟨spec.1, spec.2.trans (Nat.mul_le_mul_right _ ((Elimination.gcdWithCount_le ..).trans
    (Nat.mul_le_mul_left 2 ha)))⟩

private theorem content_dvd_aug {n : ℕ} (r : Elimination.Row n) (j : Option (Fin n)) :
    r.content ∣ (r.aug j).natAbs := by
  cases j with
  | none => exact Nat.gcd_dvd_left _ _
  | some i =>
    exact (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i))

private theorem signed_quotient (z : ℤ) (g : ℕ) (pos : 0 < g) (dz : g ∣ z.natAbs) :
    z.sign * (↑(z.natAbs/g) : ℤ) = z/(g : ℤ) := by
  have dvd : (g : ℤ) ∣ z := Int.natAbs_dvd_natAbs.mp (by simpa using dz)
  apply mul_right_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt pos)
  rw [Int.ediv_mul_cancel dvd, mul_assoc, ←Nat.cast_mul, Nat.div_mul_cancel dz, Int.sign_mul_natAbs]

/-- Refine a nonzero-content normalization at any reached elimination pivot:
the bit-list quotient computes the returned signed coefficient, the remainder
is zero, and the gate bound uses only the original dimensions and input height. -/
theorem solve_pivot_binary_division {N n H : ℕ} (base : List (Elimination.Row N))
    (hp : 1 ≤ H) (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Elimination.Row (n+1))} (reached : Elimination.SolveStep base rows)
    (p r : Elimination.Row (n+1)) (pm : p ∈ rows) (rm : r ∈ rows) (j : Option (Fin n))
    (pos : 0 < (p.rawPivot r).content) :
    let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
    let z := (p.rawPivot r).aug j
    let out := divide (p.rawPivot r).content.bits z.natAbs.bits
    z.sign*(value out.quotient : ℤ) = (p.reduce r).aug j ∧ value out.remainder = 0 ∧
      out.gates ≤ B*(20*B+1) := by
  let raw := p.rawPivot r
  let z := raw.aug j
  let g := raw.content
  let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
  let out := divide g.bits z.natAbs.bits
  have ⟨quot, rem, gates⟩ := divide_naturals z.natAbs g pos
  have dz : g ∣ z.natAbs := content_dvd_aug raw j
  have bound : z.natAbs.size ≤ B :=
    (Elimination.solve_forward_bounds base hp input).2.2 reached p pm r rm j
  have reduced : (p.reduce r).aug j = z/(g : ℤ) := by
    change raw.primitive.aug j = raw.aug j/(raw.content : ℤ)
    cases j <;> simp [Elimination.Row.primitive, Elimination.Row.aug, Nat.ne_of_gt pos,
      raw, Vector.get_eq_getElem]
  refine ⟨?_, rem.trans (Nat.mod_eq_zero_of_dvd dz), ?_⟩
  · change z.sign*(value out.quotient : ℤ) = _
    rw [reduced, show value out.quotient = z.natAbs/g from quot]
    exact signed_quotient _ _ pos dz
  · change out.gates ≤ B*(20*B+1)
    change out.gates ≤ _ at gates
    by_cases hz : z.natAbs = 0
    · simpa [hz] using gates.trans (show z.natAbs.size*(10*(g.size+z.natAbs.size)+1) ≤ B*(20*B+1) by simp [hz])
    · have gb := (Nat.size_le_size (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) dz)).trans bound
      exact gates.trans (Nat.mul_le_mul bound (by omega))

private def foldGcd : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | a :: xs =>
    let rest := foldGcd xs
    let step := gcdViaDivision a rest.1
    (step.1, step.2+rest.2)

private theorem foldGcd_spec (xs : List ℕ) (B : ℕ) (bounded : ∀ a ∈ xs, a.size ≤ B) :
    let rest := foldGcd xs
    rest.1.size ≤ B ∧ (∀ d, d ∣ rest.1 ↔ ∀ a ∈ xs, d ∣ a) ∧
    rest.2 ≤ xs.length*(2*B*(B*(20*B+1))) := by
  induction xs with
  | nil => simp [foldGcd]
  | cons a xs ih =>
    have ha := bounded a (by simp)
    obtain ⟨hb, divides, work⟩ := ih (fun y hy => bounded y (by simp [hy]))
    have ⟨eq, step⟩ := gcd_division_gates a (foldGcd xs).1 B ha hb
    simp only [foldGcd, eq, Nat.dvd_gcd_iff, List.forall_mem_cons, divides, iff_self, implies_true,
      true_and, List.length_cons]
    constructor
    · by_cases az : a=0
      · simpa [az] using hb
      · exact (Nat.size_le_size (Nat.gcd_le_left _ (Nat.pos_of_ne_zero az))).trans ha
    · simpa only [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add step work

/-- Compute row content using Euclidean remainder circuits and record the
total gate evaluations in those circuits. -/
def contentViaDivision {n : ℕ} (r : Elimination.Row n) : ℕ × ℕ :=
  foldGcd (r.rhs.natAbs :: List.ofFn (fun i => (r.coeffs.get i).natAbs))

theorem content_division_gates {n : ℕ} (r : Elimination.Row n) (B : ℕ)
    (bounded : ∀ j, (r.aug j).natAbs.size ≤ B) :
    (contentViaDivision r).1 = r.content ∧
    (contentViaDivision r).2 ≤ (n+1)*(2*B*(B*(20*B+1))) := by
  let xs := r.rhs.natAbs :: List.ofFn (fun i => (r.coeffs.get i).natAbs)
  have hxs (a : ℕ) (ha : a ∈ xs) : a.size ≤ B := by
    rcases List.mem_cons.mp ha with rfl | hx
    · exact bounded none
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact bounded (some i)
  obtain ⟨_, dvd, work⟩ := foldGcd_spec xs B hxs
  have deq (d : ℕ) : d ∣ (contentViaDivision r).1 ↔ d ∣ r.content := by
    change d ∣ (foldGcd xs).1 ↔ _
    simp [dvd, xs, Elimination.Row.content, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, List.mem_ofFn]
  exact ⟨Nat.dvd_antisymm ((deq _).mp dvd_rfl) ((deq _).mpr dvd_rfl), by simpa [xs, contentViaDivision] using work⟩

/-- All bit-list division gates for the content and all exact scalar quotients
of one materialized row on an actual forward-elimination pivot. -/
theorem solve_pivot_normalization_gates {N n H : ℕ} (base : List (Elimination.Row N))
    (hp : 1 ≤ H) (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {rows : List (Elimination.Row (n+1))} (reached : Elimination.SolveStep base rows)
    (p r : Elimination.Row (n+1)) (pm : p ∈ rows) (rm : r ∈ rows) :
    let raw := p.rawPivot r
    let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
    let content := contentViaDivision raw
    let quotients := if content.1 = 0 then 0 else
      ∑ j : Option (Fin n), (divide content.1.bits (raw.aug j).natAbs.bits).gates
    content.1 = raw.content ∧
      content.2 + quotients ≤ (n+1)*(2*B+1)*(B*(20*B+1)) := by
  let raw := p.rawPivot r
  let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
  have bounded := (Elimination.solve_forward_bounds base hp input).2.2 reached p pm r rm
  have ⟨same, work⟩ := content_division_gates raw B bounded
  refine ⟨same, ?_⟩
  change (contentViaDivision raw).2 + (if (contentViaDivision raw).1 = 0 then 0 else
    ∑ j : Option (Fin n), (divide (contentViaDivision raw).1.bits (raw.aug j).natAbs.bits).gates) ≤
      (n+1)*(2*B+1)*(B*(20*B+1))
  rw [same]
  split
  · simp only [Nat.add_zero]
    exact work.trans (by nlinarith [Nat.zero_le ((n+1)*(B*(20*B+1)))])
  · next nz =>
    have budget (j : Option (Fin n)) :
        (divide raw.content.bits (raw.aug j).natAbs.bits).gates ≤ B*(20*B+1) :=
      (solve_pivot_binary_division base hp input reached p r pm rm j (Nat.pos_of_ne_zero nz)).2.2
    have total := Finset.sum_le_sum (s := Finset.univ) (fun j _ => budget j)
    have q : (∑ j : Option (Fin n), (divide raw.content.bits (raw.aug j).natAbs.bits).gates) ≤
        (n+1)*(B*(20*B+1)) := by simpa using total
    exact (Nat.add_le_add work q).trans_eq (by ring)

private def divideEntry (g : ℕ) (z : ℤ) : ℤ × ℕ :=
  let out := divide g.bits z.natAbs.bits
  (z.sign*(value out.quotient : ℤ), out.gates)

/-- The gcd and each augmented quotient are materialized once, and the
attached cost is the sum of their binary division circuit costs. -/
def normalize {n : ℕ} (raw : Elimination.Row n) : Elimination.Row n × ℕ :=
  let content := contentViaDivision raw
  if content.1 = 0 then (raw, content.2) else
    let xs := Vector.ofFn (fun i => divideEntry content.1 (raw.coeffs.get i))
    let rhs := divideEntry content.1 raw.rhs
    (⟨Vector.ofFn (fun i => (xs.get i).1), rhs.1⟩,
      content.2 + (rhs.2 + ∑ i, (xs.get i).2))

theorem normalize_spec {n : ℕ} (raw : Elimination.Row n)
    (same : (contentViaDivision raw).1 = raw.content) :
    (normalize raw).1 = raw.primitive ∧ (normalize raw).2 = (contentViaDivision raw).2 +
      if (contentViaDivision raw).1 = 0 then 0 else
        ∑ j : Option (Fin n), (divide (contentViaDivision raw).1.bits (raw.aug j).natAbs.bits).gates := by
  by_cases zero : raw.content = 0
  · simp [normalize, same, zero, Elimination.Row.primitive]
  · have entry (j : Option (Fin n)) :
        (divideEntry raw.content (raw.aug j)).1 = raw.aug j/(raw.content : ℤ) := by
      simp only [divideEntry, (divide_naturals _ _ (Nat.pos_of_ne_zero zero)).1]
      exact signed_quotient _ _ (Nat.pos_of_ne_zero zero) (content_dvd_aug ..)
    have rhs := entry none
    have coefficients (i : Fin n) := entry (some i)
    simp only [Elimination.Row.aug, Option.elim, divideEntry, Vector.get_eq_getElem] at rhs coefficients
    simp [normalize, same, zero, Elimination.Row.primitive, rhs, coefficients, Fintype.sum_option,
      Elimination.Row.aug, Vector.get_eq_getElem, divideEntry]

private theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (k : ℕ)
    (bound : ∀ x ∈ xs, f x ≤ k) : (xs.map f).sum ≤ xs.length*k := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have b := bound a (by simp)
    have h := ih (fun x hx => bound x (by simp [hx]))
    simpa [Nat.add_comm, Nat.succ_mul] using Nat.add_le_add b h

/-- The original solver with the counted binary normalization substituted at
every pivot. This counter records just division-circuit gates. -/
def solveWithDivisionGates : (n : ℕ) → List (Elimination.Row n) → Option (Elimination.Family n) × ℕ
  | 0, rows => (Elimination.solve 0 rows, 0)
  | n+1, rows =>
    match rows.find? (fun r => r.head != 0) with
    | none =>
      let tail := solveWithDivisionGates n (rows.map Elimination.Row.drop)
      (tail.1.map Elimination.freeLift, tail.2)
    | some p =>
      let reduced := rows.map (fun r => normalize (p.rawPivot r))
      let tail := solveWithDivisionGates n (reduced.map Prod.fst)
      (tail.1.map (Elimination.pivotLift p), (reduced.map Prod.snd).sum+tail.2)

/-- Boolean gates for every Euclidean division and exact quotient used to
normalize rows throughout a whole run, on success or failure. -/
theorem solve_normalization_gates {N H : ℕ} (base : List (Elimination.Row N))
    (hp : 1 ≤ H) (input : ∀ r ∈ base, ∀ j, (r.aug j).natAbs ≤ H)
    {n : ℕ} {rows : List (Elimination.Row n)} (reached : Elimination.SolveStep base rows) :
    let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
    let K := (2*B+1)*(B*(20*B+1))
    (solveWithDivisionGates n rows).1 = Elimination.solve n rows ∧
    (solveWithDivisionGates n rows).2 ≤ rows.length*n*(n+1)*K := by
  let B := 2*(((base.length+1).size+H.size)*(base.length+1))+2
  let K := (2*B+1)*(B*(20*B+1))
  change _ ∧ _ ≤ rows.length*n*(n+1)*K
  induction n with
  | zero => simp [solveWithDivisionGates]
  | succ n ih =>
    rw [solveWithDivisionGates, Elimination.solve]
    cases found : rows.find? (fun r => r.head != 0) with
    | none =>
      have ⟨val, cost⟩ := ih (Elimination.SolveStep.drop reached found)
      simp only [List.length_map] at cost
      refine ⟨congrArg (Option.map Elimination.freeLift) val, ?_⟩
      dsimp only
      nlinarith [Nat.zero_le (rows.length*n*K), Nat.zero_le (rows.length*K)]
    | some p =>
      have pm := List.mem_of_find?_eq_some found
      let op := fun r => normalize (p.rawPivot r)
      have one (r) (rm : r ∈ rows) : (op r).1 = p.reduce r ∧ (op r).2 ≤ (n+1)*K := by
        have ⟨same, bound⟩ := solve_pivot_normalization_gates base hp input reached p r pm rm
        obtain ⟨val, work⟩ := normalize_spec (p.rawPivot r) same
        exact ⟨val, work.le.trans (bound.trans_eq (by dsimp [K, B]; ring))⟩
      have eq : (rows.map op).map Prod.fst = rows.map p.reduce := by
        rw [List.map_map]
        exact List.map_congr_left (fun r hr => (one r hr).1)
      have next : Elimination.SolveStep base ((rows.map op).map Prod.fst) :=
        eq.symm ▸ Elimination.SolveStep.pivot reached found
      have ⟨val, cost⟩ := ih next
      have stage := sum_map_le rows (fun r => (op r).2) _ (fun r hr => (one r hr).2)
      simp only [List.length_map] at cost
      change ((solveWithDivisionGates n ((rows.map op).map Prod.fst)).1.map (Elimination.pivotLift p) = _) ∧
        ((rows.map op).map Prod.snd).sum+(solveWithDivisionGates n ((rows.map op).map Prod.fst)).2 ≤ _
      refine ⟨by rw [val, eq], ?_⟩
      rw [List.map_map]
      change (rows.map (fun r => (op r).2)).sum + _ ≤ _
      nlinarith [Nat.zero_le (rows.length*n*K), Nat.zero_le (rows.length*K)]

end Cogentic.BinaryDivision

#print axioms Cogentic.BinaryDivision.divide_naturals
#print axioms Cogentic.BinaryDivision.solve_pivot_binary_division
#print axioms Cogentic.BinaryDivision.gcd_division_gates
#print axioms Cogentic.BinaryDivision.solve_pivot_normalization_gates
#print axioms Cogentic.BinaryDivision.solve_normalization_gates
