import Cogentic.TryPair
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Int.GCD

namespace Cogentic.Construction

/-- Horner evaluation with coefficients in increasing degree order. -/
def eval {R : Type*} [Ring R] (x : R) : List R → R
  | [] => 0
  | a::as => a+x*eval x as

private theorem eval_append {R : Type*} [CommRing R] (x : R) (a c : List R) :
    eval x (a++c) = eval x a+x^a.length*eval x c := by
  induction a with
  | nil => simp [eval]
  | cons a as ih => simp [eval,ih,pow_succ]; ring

/-- Multiply ascending coefficients by X-r; the carry is the preceding coefficient. -/
def linear {R : Type*} [Ring R] (r : R) : R → List R → List R
  | prev, [] => [prev]
  | prev, c::cs => (prev-r*c)::linear r c cs

def fromRoots {R : Type*} [Ring R] (roots : List R) : List R :=
  roots.foldl (fun p r => linear r 0 p) [1]

theorem eval_linear {R : Type*} [CommRing R] (x r prev : R) (p : List R) :
    eval x (linear r prev p) = prev+(x-r)*eval x p := by
  induction p generalizing prev with
  | nil => simp [eval,linear]
  | cons a as ih => rw [linear,eval,ih,eval]; ring

def crt (n m a b : ℕ) : ℕ :=
  if co : n.Coprime m then (Nat.chineseRemainder co a b).val else 0

theorem crt_spec {n m : ℕ} (co : n.Coprime m) (a b : ℕ) :
    crt n m a b ≡ a [MOD n] ∧ crt n m a b ≡ b [MOD m] := by
  simpa only [crt,dif_pos co] using (Nat.chineseRemainder co a b).property

def bitCoeff (bits j : ℕ) : ℕ := (bits.testBit j).toNat

/-- Monic binary factors are enumerated by their lower bits. Comparing the
    coefficients of the product uses O(poly(d) 4^d) tests per polynomial. -/
def hasBinaryFactor (degree mask : ℕ) : Bool :=
  (List.range' 1 (degree-1)).any (fun k =>
    (List.range (2^k)).any (fun a =>
      (List.range (2^(degree-k))).any (fun b =>
        (List.range degree).all (fun i =>
          let c := (Finset.range (i+1)).sum (fun j =>
            bitCoeff (2^k+a) j * bitCoeff (2^(degree-k)+b) (i-j))
          c%2 == bitCoeff mask i))))

def binaryMask (degree : ℕ) : ℕ :=
  ((List.range (2^degree)).find? (fun mask => !(hasBinaryFactor degree mask))).getD 0

def targets (degree : ℕ) (second : Bool) : List ℚ :=
  (List.range degree).map (fun s => ((2*s + if second then 2 else 1 : ℕ):ℚ)/(4*degree))

def wanted (degree ell m : ℕ) : List ℕ :=
  ((List.range ell).filter (fun r => r != m%ell)).take degree

def missingShift (degree ell : ℕ) : ℕ :=
  let image := (List.range ell).map (fun a : ℕ => ((ModularPower.powMod a degree ell : ℤ)-a)%ell)
  ((List.range ell).find? (fun s : ℕ => !image.contains (s:ℤ))).getD 0

def localCoeffs (degree ell m leading : ℕ) (second : Bool) : List ℤ :=
  if second then
    (List.range (degree+1)).map (fun j =>
      if j=degree then leading else if j=0 then -(leading:ℤ)*missingShift degree ell
      else if j=1 then -(leading:ℤ) else 0)
  else (fromRoots ((wanted degree ell m).map Int.ofNat)).map ((leading:ℤ)*·)

def modulusResidue (z : ℤ) (q : ℕ) : ℕ := (z % (q:ℤ)).toNat

def nearest (step residue : ℕ) (target : ℚ) : ℤ :=
  residue + (step:ℤ)*⌊(target-residue)/step+1/2⌋

theorem nearest_error {step : ℕ} (positive : 0 < step) (residue : ℕ) (target : ℚ) :
    |(nearest step residue target : ℚ)-target| ≤ step/2 := by
  let y := (target-residue)/step+1/2
  have lo := Int.floor_le y
  have hi := Int.lt_floor_add_one y
  have stepQ : (0:ℚ) < step := by exact_mod_cast positive
  have id : (target-residue)/step*(step:ℚ) = target-residue := div_mul_cancel₀ _ stepQ.ne'
  have left := mul_le_mul_of_nonneg_right lo stepQ.le
  have right := mul_lt_mul_of_pos_right hi stepQ
  change |((residue:ℤ)+(step:ℤ)*⌊y⌋:ℤ)-target| ≤ (step:ℚ)/2
  push_cast
  dsimp [y] at left right ⊢
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def preliminary (degree A m P ell leading : ℕ) (second : Bool) : List ℤ :=
  let target := fromRoots ((targets degree second).map ((A:ℚ)*·))
  let localPolynomial := localCoeffs degree ell m leading second
  let mask := binaryMask degree
  (List.range degree).map (fun j =>
    let low := crt 2 (P/2) (bitCoeff mask j) (if j=0 then 1 else 0)
    let residue := crt P ell low (modulusResidue (localPolynomial.getD j 0) ell)
    nearest (P*ell) residue ((leading:ℚ)*target.getD j 0))

/-- Subtract step times the base-m digits of the least nonnegative correction. -/
def correctLower (m step : ℕ) : ℕ → List ℤ → List ℤ
  | _,[] => []
  | t,c::cs => (c-(step:ℤ)*(t%m:ℕ))::correctLower m step (t/m) cs

@[simp] theorem correctLower_length (m step t : ℕ) (p : List ℤ) :
    (correctLower m step t p).length = p.length := by
  induction p generalizing t <;> simp_all [correctLower]

theorem eval_correctLower {m : ℕ} (hm : 0 < m) (step t : ℕ) (p : List ℤ)
    (within : t < m^p.length) :
    eval (m:ℤ) (correctLower m step t p) = eval (m:ℤ) p-(step:ℤ)*t := by
  induction p generalizing t with
  | nil =>
    have : t = 0 := by simpa using within
    simp [this,eval,correctLower]
  | cons c cs ih =>
    have bound : t/m < m^cs.length := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.pow_succ] using within)
    have eq : (t%m:ℕ)+(m:ℤ)*(t/m:ℕ) = (t:ℤ) := by exact_mod_cast Nat.mod_add_div t m
    rw [correctLower,eval,ih _ bound,eval]
    linear_combination -(step:ℤ)*eq

def correction (step n : ℕ) (atBase : ℤ) : ℕ :=
  modulusResidue (Nat.gcdA step n * atBase) n

def corrected (n m step leading : ℕ) (low : List ℤ) : List ℤ :=
  let y := eval (m:ℤ) (low++[(leading:ℤ)])
  correctLower m step (correction step n y) low ++ [(leading:ℤ)]

theorem corrected_at_base {n m step leading : ℕ} (hn : 0 < n) (hm : 0 < m)
    (co : step.Coprime n) (low : List ℤ) (fits : n ≤ m^low.length) :
    (n:ℤ) ∣ eval (m:ℤ) (corrected n m step leading low) := by
  let y := eval (m:ℤ) (low++[(leading:ℤ)])
  have npos : (0:ℤ) < n := by exact_mod_cast hn
  have reduce : ((correction step n y : ℕ):ℤ) = (Nat.gcdA step n*y) % (n:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ npos.ne')
  have bound : correction step n y < n := by
    exact_mod_cast (reduce.trans_lt (Int.emod_lt_of_pos _ npos))
  have eq : eval (m:ℤ) (corrected n m step leading low) = y-(step:ℤ)*correction step n y := by
    unfold corrected
    rw [eval_append,correctLower_length,eval_correctLower hm _ _ _ (bound.trans_le fits)]
    dsimp [y]; rw [eval_append]; ring
  rw [eq,reduce,Int.emod_def]
  have bez := Nat.gcd_eq_gcd_ab step n
  rw [co.gcd_eq_one] at bez
  refine ⟨Nat.gcdB step n*y + step*((Nat.gcdA step n*y)/(n:ℤ)),?_⟩
  linear_combination y*bez

def perturb (step m u v : ℕ) : List ℤ → List ℤ
  | a::b::c::cs =>
    (a-(step:ℤ)*m*u)::(b+(step:ℤ)*((u:ℤ)-m*v))::(c+(step:ℤ)*v)::cs
  | other => other

theorem perturb_at_base (step m u v : ℕ) (p : List ℤ) :
    eval (m:ℤ) (perturb step m u v p) = eval (m:ℤ) p := by
  cases p with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons b bs => cases bs <;> simp [perturb,eval]; ring

def leadingCoefficient (n : ℕ) : ℕ :=
  let b := n.log2+1
  let degree := Fixed.d b
  let P := primorial degree
  let T := 6*Fixed.K₁ b*Fixed.B b*P*Fixed.rootBase n*(b^2*Fixed.U b*Fixed.A b)
  let base := (P/2)*(Fixed.A b)^degree
  (P/2) * 3^(max 1 (Nat.clog 3 ((T-1)/base+1)))

def onGrid (degree A width a : ℕ) : Bool :=
  let t := (a:ℚ)/A
  let w := (width:ℚ)⁻¹
  decide (3/4 ≤ t ∧ t ≤ 3/4+w) ||
    ((targets degree false)++(targets degree true)).any (fun r => decide (r+w ≤ t ∧ t ≤ r+2*w))

def construct (n ell u₀ u₁ v₀ v₁ : ℕ) : TryPair.PairData :=
  let b := n.log2+1
  let degree := Fixed.d b
  let A := Fixed.A b
  let B := Fixed.B b
  let m := Fixed.rootBase n
  let c := leadingCoefficient n
  let P := primorial degree
  let step := P*ell
  let base := fun side => corrected n m step c (preliminary degree A m P ell c side)
  let k := (eval (m:ℤ) (base false)/n).natAbs * (eval (m:ℤ) (base true)/n).natAbs
  { leading := c
    first := perturb step m u₀ u₁ (base false)
    second := perturb step m v₀ v₁ (base true)
    factorBase := (List.range' 2 (B-1)).filter (fun q => decide (q.Prime ∧ B < q^2 ∧ ¬q ∣ k))
    marks := (List.range' 1 A).filter (fun a => onGrid degree A (Fixed.invWidth b) a &&
        decide (((a:ℤ)-m).natAbs.Coprime k)) }

theorem constructed_root {n ell : ℕ} (hn : 2 ≤ n)
    (co : (primorial (Fixed.d (n.log2+1))*ell).Coprime n) (u₀ u₁ v₀ v₁ : ℕ) :
    let pair := construct n ell u₀ u₁ v₀ v₁
    (n:ℤ) ∣ eval (Fixed.rootBase n:ℤ) pair.first ∧ (n:ℤ) ∣ eval (Fixed.rootBase n:ℤ) pair.second := by
  let b := n.log2+1
  let step := primorial (Fixed.d b)*ell
  let c := leadingCoefficient n
  have mpos : 0 < Fixed.rootBase n := by simp [Fixed.rootBase]
  have fit := (Fixed.rootBase_spec hn).2.1
  simpa only [construct,perturb_at_base] using
    And.intro (corrected_at_base (leading := c) (by omega : 0 < n) mpos co
        (preliminary (Fixed.d b) (Fixed.A b) (Fixed.rootBase n) (primorial (Fixed.d b)) ell c false)
        (by simpa [preliminary,b] using fit))
      (corrected_at_base (leading := c) (by omega : 0 < n) mpos co
        (preliminary (Fixed.d b) (Fixed.A b) (Fixed.rootBase n) (primorial (Fixed.d b)) ell c true)
        (by simpa [preliminary,b] using fit))

/-- The trial stage disposes of every prime dividing the correction modulus.
    Thus the Bézout inverse needed by both fields exists on every survivor. -/
theorem surviving_coprime {n ell : ℕ} (hn : 2 ≤ n) (composite : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) :
    (primorial (Fixed.d (n.log2+1))*ell).Coprime n := by
  let b := n.log2+1
  have bp : 0 < b := by simp [b]
  have dp := Fixed.degree_pos bp
  have zpos : 0 < Fixed.z b := by simp [Fixed.z]
  have dSmall : Fixed.d b ≤ 2^Fixed.beta b := by
    have dh : Fixed.d b ≤ Fixed.h b := Nat.le_mul_of_pos_right _ zpos
    have hb := Nat.lt_two_pow_self (n := Fixed.beta b)
    change Fixed.d b ≤ 2^(1000*Fixed.h b)
    unfold Fixed.beta at hb; omega
  have bcap : 2^Fixed.beta b ≤ indexCap b (Fixed.beta b) :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))
  have ellInfo := mem_dyadicTargets.mp target
  apply Nat.coprime_of_dvd
  intro p prime divides pn
  have small : p ≤ 2^Fixed.beta b := by
    rcases prime.dvd_mul.mp divides with left | right
    · exact (prime.dvd_primorial_iff.mp left).trans dSmall
    · exact (Nat.le_of_dvd ellInfo.1.pos right).trans ellInfo.2.2
  have proper : TwoThirdsSearch.ProperDivisor n p := ⟨prime.one_lt,
    lt_of_le_of_ne (Nat.le_of_dvd (by omega) pn) (fun eq => composite (eq ▸ prime)),pn⟩
  exact presieve_hits proper (small.trans bcap) none

theorem roots_of_surviving_input {n ell : ℕ} (hn : 2 ≤ n) (composite : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1))
      (Fixed.rootBase n) = Option.none) (u₀ u₁ v₀ v₁ : ℕ) :
    let pair := construct n ell u₀ u₁ v₀ v₁
    (n:ℤ) ∣ eval (Fixed.rootBase n:ℤ) pair.first ∧ (n:ℤ) ∣ eval (Fixed.rootBase n:ℤ) pair.second :=
  constructed_root hn (surviving_coprime hn composite target none) u₀ u₁ v₀ v₁

def pairAttempt := TryPair.attempt construct

end Cogentic.Construction

#print axioms Cogentic.Construction.constructed_root
