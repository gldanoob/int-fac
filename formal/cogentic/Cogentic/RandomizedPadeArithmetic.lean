import Cogentic.RandomizedPadeCost
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.List.OfFn

namespace Cogentic.Randomized.PadeArithmetic

open Polynomial

variable {K : Type*} [Field K] {W : ℕ}

/-- A dense array holding coefficients of degrees `0` through `W-1`. -/
abbrev Dense (K : Type*) (W : ℕ) := Vector K W

def Represents (a : Dense K W) (p : Polynomial K) : Prop :=
  (∀ i : Fin W, a[i.val] = p.coeff i.val) ∧ p.degree < (W : WithBot ℕ)

private def read (a : Dense K W) (i : ℕ) : K :=
  if h : i < W then a[i] else 0

private theorem read_represents {a : Dense K W} {p : Polynomial K} (ha : Represents a p) (i : ℕ) :
    read a i = p.coeff i := by
  by_cases hi : i < W
  · simpa only [read, dif_pos hi] using ha.1 ⟨i, hi⟩
  · rw [read, dif_neg hi, coeff_eq_zero_of_degree_lt
        (ha.2.trans_le (Nat.cast_le.mpr (Nat.le_of_not_gt hi)))]

/-- The field operations counted by this coefficient implementation. Index
arithmetic, zero padding, array allocation and coefficient copies are free here. -/
structure Charged (α : Type*) where
  value : α
  operations : ℕ

private def input (a : α) : Charged α := ⟨a, 0⟩
private def mul (a b : Charged K) : Charged K := ⟨a.value * b.value, a.operations + b.operations + 1⟩
private def sub (a b : Charged K) : Charged K := ⟨a.value - b.value, a.operations + b.operations + 1⟩
private def inv (a : K) : Charged K := ⟨a⁻¹, 1⟩

private def subShift (dst src : Dense K W) (a : K) (s : ℕ) : Charged (Dense K W) :=
  let entries := Vector.ofFn fun i : Fin W ↦
    sub (input dst[i.val]) (mul (input a) (input (if s ≤ i.val then read src (i.val-s) else 0)))
  ⟨entries.map Charged.value, (entries.toList.map Charged.operations).sum⟩

private theorem subShift_operations (dst src : Dense K W) (a : K) (s : ℕ) :
    (subShift dst src a s).operations = 2*W := by
  simp [subShift, input, mul, sub, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
    Nat.mul_comm]

private theorem subShift_represents {dst src : Dense K W} {p q : Polynomial K}
    (hp : Represents dst p) (hq : Represents src q) (a : K) (s : ℕ)
    (hshift : q.natDegree + s < W) :
    Represents (subShift dst src a s).value (p - C a * (q * X^s)) := by
  constructor
  · intro i
    simp only [subShift, Vector.getElem_map, Vector.getElem_ofFn, sub, input, mul,
      coeff_sub, coeff_C_mul, coeff_mul_X_pow', hp.1 i, read_represents hq]
  · have hs : (C a * (q * X^s)).natDegree < W := by
      apply (natDegree_C_mul_le _ _).trans_lt
      apply (natDegree_mul_le.trans ?_).trans_lt hshift
      rw [natDegree_X_pow]
    exact (degree_sub_le _ _).trans_lt
      (max_lt hp.2 (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr hs)))

/-- The two rows updated by one division: the remainder and its Bézout coefficient. -/
structure Rows (K : Type*) (W : ℕ) where
  remainder : Dense K W
  coefficient : Dense K W

/-- Cancel successive quotient slots from largest to smallest. The inverse
of the divisor's leading coefficient is computed once by `divide`. -/
private def divideLoop (divisor fixedCoeff : Dense K W) (d : ℕ) (leadInv : K) :
    ℕ → Rows K W → Charged (Rows K W)
  | 0, rows => input rows
  | s+1, rows =>
    let a := mul (input (read rows.remainder (d+s))) (input leadInv)
    let r := subShift rows.remainder divisor a.value s
    let b := subShift rows.coefficient fixedCoeff a.value s
    let tail := divideLoop divisor fixedCoeff d leadInv s ⟨r.value, b.value⟩
    ⟨tail.value, a.operations + r.operations + b.operations + tail.operations⟩

/-- Dense schoolbook division with simultaneous update of the Bézout row.
Inputs supply divisor degree `d` and the number of quotient slots. -/
def divide (rows : Rows K W) (divisor fixedCoeff : Dense K W) (d slots : ℕ) :
    Charged (Rows K W) :=
  let leadInv := inv (read divisor d)
  let tail := divideLoop divisor fixedCoeff d leadInv.value slots rows
  ⟨tail.value, leadInv.operations + tail.operations⟩

private theorem divideLoop_operations (divisor fixedCoeff : Dense K W) (d : ℕ) (leadInv : K)
    (slots : ℕ) (rows : Rows K W) :
    (divideLoop divisor fixedCoeff d leadInv slots rows).operations = (1+4*W)*slots := by
  induction slots generalizing rows with
  | zero => simp [divideLoop, input]
  | succ slots ih =>
    simp only [divideLoop, subShift_operations, ih, mul, input]
    ring

/-- A division uses one inversion, and per slot uses one multiplication
for the leading factor and a multiply-subtract at every coordinate of each row. -/
theorem divide_operations (rows : Rows K W) (divisor fixedCoeff : Dense K W) (d slots : ℕ) :
    (divide rows divisor fixedCoeff d slots).operations = 1+(1+4*W)*slots := by
  simp [divide, inv, divideLoop_operations]

/-- For positive width and a nonempty quotient, the exact arithmetic count
is at most six times the width times the quotient size. -/
theorem divide_operations_le (rows : Rows K W) (divisor fixedCoeff : Dense K W) (d slots : ℕ)
    (hW : 0 < W) (hslots : 0 < slots) :
    (divide rows divisor fixedCoeff d slots).operations ≤ 6*W*slots := by
  rw [divide_operations, Nat.add_mul, one_mul]
  have h : slots ≤ W*slots := by
    simpa using Nat.mul_le_mul_right slots (show 1 ≤ W by omega)
  have hr : 4*W*slots = 4*(W*slots) := by ring
  have hs : 6*W*slots = 6*(W*slots) := by ring
  rw [hr, hs]
  omega

private theorem cancel_degree (r divisor : Polynomial K) (d s : ℕ)
    (hd : divisor.natDegree = d) (hnz : divisor ≠ 0)
    (hr : r.degree < (↑(d + (s+1)) : WithBot ℕ)) :
    (r - C (r.coeff (d+s) * divisor.leadingCoeff⁻¹) * (divisor * X^s)).degree <
      (↑(d+s) : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro i hi
  rw [coeff_sub, coeff_C_mul, coeff_mul_X_pow', if_pos (show s ≤ i by omega)]
  by_cases he : i = d+s
  · subst i
    have hc : divisor.coeff (d+s-s) = divisor.leadingCoeff := by
      rw [Nat.add_sub_cancel, ← hd, coeff_natDegree]
    rw [hc, mul_assoc, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hnz), mul_one, sub_self]
  · have hr0 : r.coeff i = 0 :=
      coeff_eq_zero_of_degree_lt (hr.trans_le (Nat.cast_le.mpr (by omega)))
    have hd0 : divisor.coeff (i-s) = 0 := by
      apply coeff_eq_zero_of_degree_lt
      rw [degree_eq_natDegree hnz, hd, Nat.cast_lt]
      omega
    simp [hr0, hd0]

private theorem divideLoop_correct (divisor fixedCoeff : Dense K W) (d : ℕ)
    (D B : Polynomial K) (hdiv : Represents divisor D) (hb : Represents fixedCoeff B)
    (hd : D.natDegree = d) (hnz : D ≠ 0) (slots : ℕ) (rows : Rows K W)
    (r b : Polynomial K) (hr : Represents rows.remainder r) (hcoeff : Represents rows.coefficient b)
    (hdegree : r.degree < (↑(d+slots) : WithBot ℕ))
    (hwidth : d+slots ≤ W) (hbwidth : B.natDegree+slots ≤ W) :
    let out := (divideLoop divisor fixedCoeff d D.leadingCoeff⁻¹ slots rows).value
    ∃ q r' b' : Polynomial K, Represents out.remainder r' ∧ Represents out.coefficient b' ∧
      r'.degree < (d : WithBot ℕ) ∧ r' + D*q = r ∧ b' = b - B*q := by
  induction slots generalizing rows r b with
  | zero =>
    exact ⟨0, r, b, hr, hcoeff, by simpa using hdegree, by simp, by simp⟩
  | succ s ih =>
    let a := r.coeff (d+s) * D.leadingCoeff⁻¹
    let nextRows : Rows K W :=
      ⟨(subShift rows.remainder divisor a s).value,
        (subShift rows.coefficient fixedCoeff a s).value⟩
    let r₁ := r - C a * (D*X^s)
    let b₁ := b - C a * (B*X^s)
    have hra : Represents nextRows.remainder r₁ :=
      subShift_represents hr hdiv a s (by omega)
    have hba : Represents nextRows.coefficient b₁ :=
      subShift_represents hcoeff hb a s (by omega)
    have hstep := cancel_degree r D d s hd hnz hdegree
    obtain ⟨q, r', b', hrepr, hrepb, hsmall, hrem, hbe⟩ :=
      ih nextRows r₁ b₁ hra hba hstep (by omega) (by omega)
    have hscalar : (mul (input (read rows.remainder (d+s))) (input D.leadingCoeff⁻¹)).value = a := by
      simp [a, mul, input, read_represents hr]
    simp only [divideLoop, hscalar]
    refine ⟨C a * X^s + q, r', b', hrepr, hrepb, hsmall, ?_, ?_⟩
    · calc
        r' + D * (C a * X^s + q) = (r' + D*q) + C a * (D * X^s) := by ring
        _ = r := by rw [hrem]; dsimp [r₁]; ring
    · rw [hbe]
      dsimp [b₁]
      ring

private theorem quotient_remainder_unique {P D q r : Polynomial K} (hD : D ≠ 0)
    (he : r + D*q = P) (hsmall : r.degree < D.degree) : q = P/D ∧ r = P%D := by
  have hdiv := EuclideanDomain.div_add_mod P D
  have hprod : D*(q-P/D) = P%D-r := by
    calc
      _ = (r+D*q) - (D*(P/D)+P%D) + (P%D-r) := by ring
      _ = _ := by rw [he, hdiv, sub_self, zero_add]
  have hq : q = P/D := by
    by_contra hne
    have hbig := degree_le_mul_left D (sub_ne_zero.mpr hne)
    rw [hprod] at hbig
    exact not_lt_of_ge hbig ((degree_sub_le _ _).trans_lt (max_lt (degree_mod_lt P hD) hsmall))
  rw [hq, sub_self, mul_zero] at hprod
  exact ⟨hq, (sub_eq_zero.mp hprod.symm).symm⟩

/-- The dense routine computes the same polynomial remainder and Bézout
update as Euclidean division, provided the two shifted rows fit in the width. -/
theorem divide_correct (rows : Rows K W) (divisor fixedCoeff : Dense K W) (d slots : ℕ)
    {P D b₀ b₁ : Polynomial K} (hP : Represents rows.remainder P)
    (hD : Represents divisor D) (hb₀ : Represents rows.coefficient b₀)
    (hb₁ : Represents fixedCoeff b₁) (hd : D.natDegree = d) (hnz : D ≠ 0)
    (hdegree : P.degree < (↑(d+slots) : WithBot ℕ)) (hwidth : d+slots ≤ W)
    (hbwidth : b₁.natDegree+slots ≤ W) :
    let out := (divide rows divisor fixedCoeff d slots).value
    Represents out.remainder (P%D) ∧ Represents out.coefficient (b₀ - (P/D)*b₁) := by
  have hlead : read divisor d = D.leadingCoeff := by
    rw [read_represents hD, ← hd, coeff_natDegree]
  obtain ⟨q, r, b, hr, hb, hsmall, hrem, hbe⟩ :=
    divideLoop_correct divisor fixedCoeff d D b₁ hD hb₁ hd hnz slots rows P b₀ hP hb₀
      hdegree hwidth hbwidth
  rw [← hd, ← degree_eq_natDegree hnz] at hsmall
  obtain ⟨rfl, rfl⟩ := quotient_remainder_unique hnz hrem hsmall
  simpa only [divide, inv, hlead, hbe, mul_comm b₁ (P/D)] using And.intro hr hb

/-- The Euclidean invariant guarantees enough coefficient width for both
updates. Its quotient size is the degree gap plus one. -/
theorem euclid_step_correct_and_operations {A : Polynomial K} {N : ℕ}
    (s : Randomized.PadeEuclid.State A N) (hnz : s.remainder ≠ 0)
    (rows : Rows K (N+1)) (divisor fixedCoeff : Dense K (N+1))
    (hP : Represents rows.remainder s.previous) (hD : Represents divisor s.remainder)
    (hb₀ : Represents rows.coefficient s.previousCoefficient)
    (hb₁ : Represents fixedCoeff s.coefficient) :
    let d := s.remainder.natDegree
    let slots := s.previous.natDegree-d+1
    let out := divide rows divisor fixedCoeff d slots
    Represents out.value.remainder (s.step hnz).remainder ∧
      Represents out.value.coefficient (s.step hnz).coefficient ∧
      out.operations ≤ 6*(N+1)*((s.previous/s.remainder).natDegree+1) := by
  let d := s.remainder.natDegree
  let slots := s.previous.natDegree - d + 1
  have hdrop : d < s.previous.natDegree := natDegree_lt_natDegree hnz s.remainder_lt
  have hsum := s.coefficient_degree_sum
  have hwidth : d+slots ≤ N+1 := by dsimp [slots]; omega
  have hbwidth : s.coefficient.natDegree+slots ≤ N+1 := by dsimp [slots]; omega
  have hdegree : s.previous.degree < (↑(d+slots) : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by dsimp [slots]; omega))
  obtain ⟨hr, hb⟩ := divide_correct rows divisor fixedCoeff d slots hP hD hb₀ hb₁
    rfl hnz hdegree hwidth hbwidth
  refine ⟨hr, hb, ?_⟩
  rw [s.quotient_natDegree_eq_gap hnz]
  exact divide_operations_le rows divisor fixedCoeff d slots (by omega) (by simp [slots])

private def constantRow (c : K) : Dense K W :=
  Vector.ofFn (fun i ↦ if i.val = 0 then c else 0)

private theorem constantRow_represents (c : K) (hW : 0 < W) :
    Represents (constantRow (W := W) c) (C c) := by
  refine ⟨fun i ↦ ?_, degree_C_le.trans_lt (Nat.cast_lt.mpr hW)⟩
  simp [constantRow, coeff_C]

/-- Ordinary division returns both remainder and quotient by setting the
tracked rows to zero and minus one. This also supplies post-GCD exact division. -/
def divideWithQuotient (dividend divisor : Dense K W) (d slots : ℕ) : Charged (Rows K W) :=
  let minusOne := sub (input (0 : K)) (input 1)
  let out := divide ⟨dividend, constantRow 0⟩ divisor (constantRow minusOne.value) d slots
  ⟨out.value, minusOne.operations + out.operations⟩

theorem divideWithQuotient_correct (dividend divisor : Dense K W) (d slots : ℕ)
    {P D : Polynomial K} (hP : Represents dividend P) (hD : Represents divisor D)
    (hd : D.natDegree = d) (hnz : D ≠ 0) (hW : 0 < W)
    (hdegree : P.degree < (↑(d+slots) : WithBot ℕ)) (hwidth : d+slots ≤ W) :
    let out := (divideWithQuotient dividend divisor d slots).value
    Represents out.remainder (P%D) ∧ Represents out.coefficient (P/D) := by
  have hzero : Represents (constantRow (W := W) (0 : K)) (0 : Polynomial K) := by
    simpa using constantRow_represents (0 : K) hW
  have hneg : Represents (constantRow (W := W) (-1 : K)) (-1 : Polynomial K) := by
    simpa using constantRow_represents (-1 : K) hW
  have hbwidth : (-1 : Polynomial K).natDegree + slots ≤ W := by simp; omega
  have h := divide_correct ⟨dividend, constantRow 0⟩ divisor (constantRow (-1)) d slots
    hP hD hzero hneg hd hnz hdegree hwidth hbwidth
  simpa [divideWithQuotient, sub, input] using h

theorem divideWithQuotient_operations (dividend divisor : Dense K W) (d slots : ℕ) :
    (divideWithQuotient dividend divisor d slots).operations = 2+(1+4*W)*slots := by
  simp only [divideWithQuotient, divide_operations, sub, input]
  omega

theorem divideWithQuotient_operations_le_width (dividend divisor : Dense K W) (d slots : ℕ)
    (hslots : slots ≤ W) :
    (divideWithQuotient dividend divisor d slots).operations ≤ 2+(1+4*W)*W := by
  rw [divideWithQuotient_operations]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hslots) _

private theorem gcd_degree_gap_accounting (d : ℕ → ℕ) (k : ℕ)
    (hmono : ∀ i < k, d (i+1) ≤ d i)
    (hstrict : ∀ i < k, 0 < i → d (i+1) < d i) :
    d k+k ≤ d 0+1 ∧
      (∑ i ∈ Finset.range k, (d i - d (i+1) + 1)) = d 0 - d k + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi ↦ hmono i (Nat.lt_succ_of_lt hi))
      (fun i hi hi₀ ↦ hstrict i (Nat.lt_succ_of_lt hi) hi₀)
    have hnext := hmono k (Nat.lt_succ_self k)
    rw [Finset.sum_range_succ, hprev.2]
    by_cases hk : 0 < k
    · have hdrop := hstrict k (Nat.lt_succ_self k) hk
      omega
    · have hk₀ : k = 0 := by omega
      subst k
      omega

/-- For the normalization GCD, start with the larger-degree input. The
first degrees may tie, and subsequent divisor degrees strictly decrease.
Charging `divideWithQuotient` at width `n+1` then gives this quadratic budget. -/
theorem gcd_operations_le (d operations : ℕ → ℕ) (n k : ℕ) (hstart : d 0 ≤ n)
    (hmono : ∀ i < k, d (i+1) ≤ d i)
    (hstrict : ∀ i < k, 0 < i → d (i+1) < d i)
    (hcost : ∀ i < k, operations i ≤ 2+(1+4*(n+1))*(d i-d (i+1)+1)) :
    (∑ i ∈ Finset.range k, operations i) ≤ 2*(n+1)+(1+4*(n+1))*(2*n+1) := by
  obtain ⟨hdepth, hsum⟩ := gcd_degree_gap_accounting d k hmono hstrict
  have hk : k ≤ n+1 := by omega
  have hslots : (∑ i ∈ Finset.range k, (d i - d (i+1) + 1)) ≤ 2*n+1 := by
    rw [hsum]
    omega
  calc
    _ ≤ ∑ i ∈ Finset.range k, (2+(1+4*(n+1))*(d i-d (i+1)+1)) :=
      Finset.sum_le_sum fun i hi ↦ hcost i (Finset.mem_range.mp hi)
    _ = 2*k + (1+4*(n+1))*(∑ i ∈ Finset.range k, (d i-d (i+1)+1)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id,
        Nat.mul_comm k 2, ← Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hk) (Nat.mul_le_mul_left _ hslots)

private def scaleRow (row : Dense K W) (c : K) : Charged (Dense K W) :=
  let entries := Vector.ofFn fun i : Fin W ↦ mul (input c) (input row[i.val])
  ⟨entries.map Charged.value, (entries.toList.map Charged.operations).sum⟩

private theorem scaleRow_operations (row : Dense K W) (c : K) :
    (scaleRow row c).operations = W := by
  simp [scaleRow, mul, input, Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

private theorem scaleRow_represents {row : Dense K W} {p : Polynomial K} (hp : Represents row p)
    (c : K) : Represents (scaleRow row c).value (C c*p) := by
  constructor
  · intro i
    simp only [scaleRow, Vector.getElem_map, Vector.getElem_ofFn, mul, input, coeff_C_mul, hp.1 i]
  · by_cases hc : c = 0
    · simp [hc]
    · rw [degree_C_mul hc]
      exact hp.2

/-- After exact division by the gcd, scale the numerator and denominator
by the inverse constant term of the reduced denominator. -/
def normalize (rows : Rows K W) : Charged (Rows K W) :=
  let c := inv (read rows.coefficient 0)
  let r := scaleRow rows.remainder c.value
  let b := scaleRow rows.coefficient c.value
  ⟨⟨r.value, b.value⟩, c.operations + r.operations + b.operations⟩

theorem normalize_operations (rows : Rows K W) : (normalize rows).operations = 1+2*W := by
  simp only [normalize, inv, scaleRow_operations]
  omega

theorem normalize_correct (rows : Rows K W) {r b : Polynomial K}
    (hr : Represents rows.remainder r) (hb : Represents rows.coefficient b) (h₀ : b.coeff 0 ≠ 0) :
    let c := C (b.coeff 0)⁻¹
    let out := (normalize rows).value
    Represents out.remainder (c*r) ∧ Represents out.coefficient (c*b) ∧ (c*b).coeff 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [normalize, inv, read_represents hb] using scaleRow_represents hr (b.coeff 0)⁻¹
  · simpa only [normalize, inv, read_represents hb] using scaleRow_represents hb (b.coeff 0)⁻¹
  · simp [h₀]

/-- Reflect a dense row by index permutation alone. -/
def reflectRow (row : Dense K W) (m : ℕ) : Charged (Dense K W) :=
  input (Vector.ofFn (fun i ↦ read row (revAtFun m i.val)))

theorem reflectRow_operations (row : Dense K W) (m : ℕ) : (reflectRow row m).operations = 0 := rfl

theorem reflectRow_correct {row : Dense K W} {p : Polynomial K} (hp : Represents row p)
    (m : ℕ) (hm : m < W) : Represents (reflectRow row m).value (p.reflect m) := by
  constructor
  · intro i
    simp [reflectRow, input, read_represents hp]
  · by_cases h : p = 0
    · simp [h]
    · have hwidth : p.natDegree < W := Nat.cast_lt.mp ((degree_eq_natDegree h) ▸ hp.2)
      exact degree_le_natDegree.trans_lt
        (Nat.cast_lt.mpr (natDegree_reflect_le.trans_lt (max_lt_iff.mpr ⟨hm, hwidth⟩)))

end Cogentic.Randomized.PadeArithmetic
