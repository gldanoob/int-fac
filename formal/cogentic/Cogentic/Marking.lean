import Cogentic.Driver
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Polynomial.Derivative

namespace Cogentic.Marking

open TwoThirdsSearch

/-- One trial remainder per eligible prime. Checking the product of the distinct
    prime divisors rejects both repeated factors and primes outside the base. -/
def divided (base : List ℕ) (value : ℕ) := base.filter (fun q => decide (q ∣ value))

def SquarefreeSmooth (base : List ℕ) (value : ℕ) : Prop :=
  value ≠ 0 ∧ Squarefree value ∧ ∀ p, p.Prime → p ∣ value → p ∈ base

theorem divided_correct {base : List ℕ} (unique : base.Nodup) (primes : ∀ q ∈ base, q.Prime)
    (n : ℕ) : (divided base n).prod = n ↔ SquarefreeSmooth base n := by
  let xs := divided base n
  have noDup : xs.Nodup := unique.filter _
  have membership {p : ℕ} : p ∈ xs ↔ p ∈ base ∧ p ∣ n := by simp [xs, divided]
  have prime (p : ℕ) (hp : p ∈ xs) := primes p (membership.mp hp).1
  constructor
  · intro prod
    have perm := Nat.primeFactorsList_unique prod prime
    have nz : n ≠ 0 := by
      have pos := List.prod_pos_iff_forall_pos_nat.mpr (fun p hp => (prime p hp).pos)
      exact prod ▸ pos.ne'
    refine ⟨nz,(Nat.squarefree_iff_nodup_primeFactorsList nz).mpr (perm.nodup_iff.mp noDup),?_⟩
    intro p pp pn
    exact (membership.mp (perm.mem_iff.mpr (Nat.mem_primeFactorsList'.mpr ⟨pp,pn,nz⟩))).1
  · rintro ⟨nz,sq,supported⟩
    apply Eq.trans _ (Nat.prod_primeFactorsList nz)
    apply List.Perm.prod_eq
    apply (List.perm_ext_iff_of_nodup noDup sq.nodup_primeFactorsList).mpr
    intro p
    rw [membership, Nat.mem_primeFactorsList']
    exact ⟨fun h => ⟨primes p h.1,h.2,nz⟩, fun ⟨pp,pn,_⟩ => ⟨supported p pp pn,pn⟩⟩

theorem divided_length {base : List ℕ} (unique : base.Nodup) (primes : ∀ q ∈ base, q.Prime)
    {n : ℕ} (eq : (divided base n).prod = n) : (divided base n).length = n.primeFactors.card := by
  have prime (p : ℕ) (hp : p ∈ divided base n) := primes p (List.mem_filter.mp hp).1
  have perm := Nat.primeFactorsList_unique eq prime
  have sq := ((divided_correct unique primes n).mp eq).2.1
  simpa [← Nat.toFinset_factors, List.toFinset_card_of_nodup sq.nodup_primeFactorsList] using perm.length_eq

/-- Coefficients in increasing degree order. Horner computes the value and the
    derivative together in the coefficient ring used by the caller. -/
def horner {R : Type*} [CommRing R] (x : R) : List ℤ → R × R
  | [] => (0,0)
  | c :: cs => let (v,d) := horner x cs; ((c : R)+x*v,v+x*d)

noncomputable def polynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * polynomial cs

theorem horner_correct {R : Type*} [CommRing R] (x : R) (cs : List ℤ) :
    horner x cs = ((polynomial cs).eval₂ (Int.castRingHom R) x,
      (polynomial cs).derivative.eval₂ (Int.castRingHom R) x) := by
  induction cs with
  | nil => simp [horner,polynomial]
  | cons c cs ih =>
    simp only [horner, polynomial, ih, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, zero_add, one_mul, Int.coe_castRingHom]

structure Input where
  n : ℕ
  m : ℕ
  degree : ℕ
  leading : ℕ
  A : ℕ
  B : ℕ
  L₀ : ℕ
  K₁ : ℕ
  target : ℕ
  factorBase : List ℕ
  marks : List ℕ
  first : List ℤ
  second : List ℤ

def Input.coeffs (s : Input) (side : Bool) := if side then s.second else s.first

def Input.polynomialGuard (s : Input) (coeffs : List ℤ) : Prop :=
  coeffs.length = s.degree+1 ∧ coeffs.getLast? = some s.leading ∧
  (∀ c ∈ coeffs, c.natAbs ≤ 2^s.L₀) ∧ (horner (s.m : ZMod s.n) coeffs).1 = 0

instance (s : Input) (cs : List ℤ) : Decidable (s.polynomialGuard cs) := by
  unfold Input.polynomialGuard
  infer_instance

def Input.guard (s : Input) : Prop :=
  9 ≤ s.n ∧ 2 ≤ s.m ∧ 9 ≤ s.degree ∧ 1 ≤ s.leading ∧ 2 ≤ s.A ∧ 4 ≤ s.B ∧
  16 ≤ s.K₁ ∧ 10 ≤ s.L₀ ∧ s.n ≤ 2^(s.degree*s.L₀) ∧ s.leading.Coprime s.n ∧
  s.m ≤ 2^s.L₀ ∧ s.A ≤ 2^s.L₀ ∧ s.B ≤ 2^s.L₀ ∧ s.K₁ ≤ 2^s.L₀ ∧
  s.polynomialGuard s.first ∧ s.polynomialGuard s.second

instance (s : Input) : Decidable s.guard := by unfold Input.guard; infer_instance

def Input.base (s : Input) := (s.factorBase.filter
  (fun p => decide (p.Prime ∧ p ≤ s.B ∧ p.Coprime (s.leading*s.n)))).dedup

theorem mem_base {s : Input} {p : ℕ} : p ∈ s.base ↔
    p ∈ s.factorBase ∧ p.Prime ∧ p ≤ s.B ∧ p.Coprime (s.leading*s.n) := by simp [Input.base]

structure Row where
  second : Bool
  q : ℕ
  r : ℕ
deriving DecidableEq, Repr

def Row.isRoot (f : List ℤ) (row : Row) : Bool :=
  decide ((horner (row.r : ZMod row.q) f).1 = 0)

def Row.bad (s : Input) (row : Row) : Bool :=
  decide ((horner (row.r : ZMod row.q) (s.coeffs row.second)).2 = 0) ||
    row.isRoot (s.coeffs (!row.second))

def Input.rows (s : Input) : List Row :=
  ((s.base.flatMap fun q => (List.range q).flatMap fun r =>
    [Row.mk false q r, Row.mk true q r]).filter
    (fun row => row.isRoot (s.coeffs row.second))).dedup

theorem mem_rows {s : Input} {row : Row} : row ∈ s.rows ↔ row.q ∈ s.base ∧ row.r < row.q ∧
    (polynomial (s.coeffs row.second)).eval₂ (Int.castRingHom (ZMod row.q)) (row.r : ZMod row.q) = 0 := by
  rcases row with ⟨side,q,r⟩
  cases side <;> simp [Input.rows,Row.isRoot,horner_correct,List.mem_flatMap,Row.mk.injEq,and_assoc]

def Input.clean (s : Input) := s.rows.filter (fun row => !(row.bad s))
def Input.badRows (s : Input) := s.rows.filter (fun row => row.bad s)

def Input.eligibleMarks (s : Input) := (s.marks.toFinset.filter (fun a =>
  1 ≤ a ∧ a ≤ s.A ∧ (((a:ℤ)-s.m).natAbs).Coprime s.n)).sort

def value (f : List ℤ) (a : ℕ) : ℕ := (horner (a:ℤ) f).1.natAbs

private theorem horner_size (xs : List ℤ) {a M : ℕ} (ha : 1 ≤ a)
    (height : ∀ c ∈ xs, c.natAbs ≤ M) : value xs a ≤ xs.length * M * a^xs.length := by
  induction xs with
  | nil => simp [value,horner]
  | cons c cs ih =>
    have step := ih (fun t ht => height t (by simp [ht]))
    have coeff := height c (by simp)
    have powPos : 0 < a^(cs.length+1) := Nat.pow_pos (by omega)
    have tail : (c + (a:ℤ)*(horner (a:ℤ) cs).1).natAbs ≤ c.natAbs + a*value cs a := by
      calc _ ≤ _ := Int.natAbs_add_le _ _
           _ = _ := by simp [value, Int.natAbs_mul]
    change (c + (a:ℤ)*(horner (a:ℤ) cs).1).natAbs ≤ (cs.length+1)*M*a^(cs.length+1)
    apply tail.trans
    calc c.natAbs+a*value cs a ≤ M*a^(cs.length+1) + a*(cs.length*M*a^cs.length) :=
           Nat.add_le_add (coeff.trans (Nat.le_mul_of_pos_right _ powPos)) (Nat.mul_le_mul_left _ step)
         _ = _ := by rw [Nat.pow_succ]; ring

/-- A uniform integer operand bound for the mark evaluations and the subsequent
    trial remainders. The exponent is linear in degree and input bit length. -/
theorem value_size {s : Input} {coeffs : List ℤ} (guard : s.polynomialGuard coeffs) {a : ℕ}
    (positive : 1 ≤ a) (within : a ≤ 2^s.L₀) (degreeBits : s.degree+1 ≤ 2^s.L₀) :
    value coeffs a ≤ 2^((s.degree+3)*s.L₀) := by
  apply (horner_size coeffs positive guard.2.2.1).trans
  rw [guard.1]
  calc
    _ ≤ 2^s.L₀ * 2^s.L₀ * (2^s.L₀)^(s.degree+1) := by gcongr
    _ = _ := by simp only [← Nat.pow_mul, ← Nat.pow_add]; congr 1; ring

def survives (s : Input) (bad : List Row) (a : ℕ) : Bool :=
  let x := value s.first a
  let y := value s.second a
  let left := divided s.base x
  let right := divided s.base y
  decide (left.prod = x ∧ right.prod = y ∧ 1+left.length+right.length ≤ s.L₀) &&
    bad.all (fun row => decide (a % row.q ≠ row.r))

theorem survives_correct (s : Input) (bad : List Row) (a : ℕ) :
    survives s bad a = true ↔
    SquarefreeSmooth s.base (value s.first a) ∧ SquarefreeSmooth s.base (value s.second a) ∧
    1+(value s.first a).primeFactors.card+(value s.second a).primeFactors.card ≤ s.L₀ ∧
    ∀ row ∈ bad, a%row.q ≠ row.r := by
  have unique : s.base.Nodup := List.nodup_dedup _
  have pp (q : ℕ) (hq : q ∈ s.base) := (mem_base.mp hq).2.1
  simp only [survives, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨left,right,size⟩,clean⟩
    rw [divided_length unique pp left, divided_length unique pp right] at size
    exact ⟨(divided_correct unique pp _).mp left,(divided_correct unique pp _).mp right,size,
      clean⟩
  · rintro ⟨left,right,size,clean⟩
    have l := (divided_correct unique pp _).mpr left
    have r := (divided_correct unique pp _).mpr right
    exact ⟨⟨l,r,by simpa [divided_length unique pp l, divided_length unique pp r] using size⟩,
      clean⟩

structure Relations where
  rows : List Row
  marks : List ℕ
  target : ℕ

/-- The zeroth row is the intercept. Remaining entries are the congruence
    indicators from the cleaned factor base. -/
def Relations.matrix (s : Relations) : Matrix (Fin (s.rows.length+1)) (Fin s.marks.length) ℤ :=
  Fin.cases (fun _ => 1) (fun i j =>
    let row := s.rows.get i
    if s.marks.get j % row.q = row.r then 1 else 0)

def Relations.rhs (s : Relations) : Fin (s.rows.length+1) → ℤ :=
  Fin.cases 0 (fun i =>
    let row := s.rows.get i
    if !row.second && row.q == s.target then 1 else 0)

def stageOne (s : Input) : Option Relations :=
  let rows := s.clean
  if s.guard ∧ s.target ∈ s.base ∧ (rows.filter (fun r => !r.second && r.q == s.target)).length = s.degree then
    some ⟨rows,s.eligibleMarks.filter (survives s s.badRows),s.target⟩
  else none

theorem retained_iff {s : Input} {out : Relations} (ok : stageOne s = some out) (a : ℕ) :
    a ∈ out.marks ↔ a ∈ s.eligibleMarks ∧ SquarefreeSmooth s.base (value s.first a) ∧
      SquarefreeSmooth s.base (value s.second a) ∧
      1+(value s.first a).primeFactors.card+(value s.second a).primeFactors.card ≤ s.L₀ ∧
      ∀ row ∈ s.badRows, a%row.q ≠ row.r := by
  simp only [stageOne] at ok
  split at ok <;> cases ok
  simp only [List.mem_filter, survives_correct]

/-- Supply the actual CRT polynomials for a four-coordinate trial and the
    subsequent exact solver. Failed factor-base checks discard this trial. -/
def tryMarked (construct : ℕ → ℕ → ℕ → ℕ → ℕ → Input)
    (finish : Input → Relations → Option Proposal) : TryPair :=
  fun g a b c d => let s := construct g a b c d; (stageOne s).bind (finish s)

end Cogentic.Marking

#print axioms Cogentic.Marking.retained_iff
