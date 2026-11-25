import Cogentic.ScalarSteps
import Cogentic.GaussianCRT
import Cogentic.GaussianGeometry
import Cogentic.GaussianJoint

namespace Cogentic.Construction
open Cogentic.Window

private theorem value_perturb {cs : List ℤ} (len : 3≤cs.length) (step m u v a : ℕ) :
    eval (a:ℤ) (perturb step m u v cs) =
      eval (a:ℤ) (perturb step m 0 0 cs)+step*((a:ℤ)-m)*(u+a*v) := by
  rcases cs with _ | ⟨p,cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  rcases cs with _ | ⟨q,cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  rcases cs with _ | ⟨r,cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  simp [perturb,eval]; ring

/-- Signed lattice evaluation specializes exactly to the executable pair,
    for every allowed tensor coordinate and every integer grid mark. -/
theorem affine_at_constructed {n ell : ℕ} (big : 3≤Fixed.d (n.log2+1)) (a u v w z : ℕ) :
    let p := construct n ell u v w z
    eval (a:ℤ) p.first = affineValue n ell a false ((u:ℤ)+a*v) ∧
      eval (a:ℤ) p.second = affineValue n ell a true ((w:ℤ)+a*z) := by
  let b := n.log2+1; let d := Fixed.d b; let A := Fixed.A b; let m := Fixed.rootBase n
  let P := primorial d; let c := leadingCoefficient n
  let f := fun side => corrected n m (P*ell) c (preliminary d A m P ell c side)
  have len (side : Bool) : 3 ≤ (f side).length := by simp [f,corrected,preliminary]; change 3≤d at big; omega
  have law (side : Bool) (i j : ℕ) : eval (a:ℤ) (perturb (P*ell) m i j (f side)) =
      affineValue n ell a side ((i:ℤ)+a*j) := by
    have eq := value_perturb (len side) (P*ell) m i j a
    cases side <;> simpa only [Nat.cast_mul,basePolynomial,affineValue,construct,Bool.false_eq_true,if_false,if_true] using eq
  exact ⟨law false u v,law true w z⟩

theorem normalized_at_mark {A : ℕ} (ap : 0<A) (a : ℕ) (cs : List ℤ) :
    RootLogs.normalized A cs ((a:ℚ)/A) = (eval (a:ℤ) cs:ℤ) := by
  induction cs with
  | nil => simp [RootLogs.normalized,Marking.horner,eval]
  | cons t ts ih =>
    change (t:ℚ)+((A:ℚ)*((a:ℚ)/A))*RootLogs.normalized A ts ((a:ℚ)/A)=_
    rw [mul_div_cancel₀ (a:ℚ) (by exact_mod_cast ap.ne'),ih]; simp [eval]

/-- At its Gaussian center the signed mean uses exactly the affine
    evaluation law whose integers enter the character sums. -/
theorem mean_is_affine {n ell : ℕ} (big : 3≤Fixed.d (n.log2+1)) (a : ℕ) (side : Bool) :
    (exactMean n ell a side:ℝ)=(markSign n a side:ℝ)*affineValue n ell a side (lineCenter n a) := by
  let b := n.log2+1; let A := Fixed.A b; let U := Fixed.U b
  let μ := b^2*U*A; let ν := b^2*U
  let p := construct n ell μ ν μ ν
  have raw := normalized_at_mark (A := A) (Nat.pow_pos (by decide)) a
  have ⟨first,second⟩ := affine_at_constructed (ell := ell) big a μ ν μ ν
  have ctr := mean_polynomial_is_constructed n ell
  have eq : eval (a:ℤ) (meanPolynomial n ell side) = affineValue n ell a side (lineCenter n a) := by
    cases side
    · rw [←ctr.1]; simpa only [lineCenter,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,b,A,U,μ,ν] using first
    · rw [←ctr.2]; simpa only [lineCenter,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,b,A,U,μ,ν] using second
  have sign := markSign_eq n a side
  change ((orientation n a side*RootLogs.normalized A (meanPolynomial n ell side) ((a:ℚ)/A):ℚ):ℝ)=_
  rw [raw,eq,←sign]
  push_cast; rfl

/-- A genuine prescribed row of either polynomial is one affine equation
    in the coefficient lattice. The local slope is a unit by the actual
    band and root restrictions. -/
theorem PrescribedRows.linear_equations {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) :
    ∃ L : ℕ→ℤ, ∀ u v : ℤ, R.compatible side u v ↔
      ∀ q ∈ R.primes, (u:ZMod q)+(R.residue q:ZMod q)*v = L q := by
  classical
  let b := n.log2+1; let d := Fixed.d b; let P := primorial d; let m := Fixed.rootBase n
  have ep := (mem_dyadicTargets.mp target).1
  have ⟨_,bx,_,B,_,_,_⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have db : d ≤ dyadicUnit b := (Fixed.degree_le_bits b).trans bx
  have xp : 0<dyadicUnit b := Nat.pow_pos (by decide)
  have dsq : d^2 ≤ Fixed.B b := by rw [B]; exact (Nat.pow_le_pow_left db 2).trans (Nat.pow_le_pow_right xp (by decide))
  have localEq (q : ℕ) (hq : q ∈ R.primes) :
      ∃ c : ℤ, ∀ u v : ℤ, (q:ℤ)∣affineValue n ell (R.residue q) side (u+R.residue q*v) ↔
        (u:ZMod q)+(R.residue q:ZMod q)*v=c := by
    have pr := R.prime hq
    let : Fact q.Prime := ⟨pr⟩
    have band := (mem_primeBand.mp (Finset.mem_filter.mp (R.member hq)).1).2.2
    have small : d<q := by
      by_contra! bad
      exact band.not_ge ((Nat.pow_le_pow_left bad 2).trans dsq)
    have punit : (P:ZMod q) ≠ 0 := fun z => small.not_ge (pr.dvd_primorial_iff.mp ((ZMod.natCast_eq_zero_iff ..).mp z))
    have eunit : (ell:ZMod q) ≠ 0 := fun z => R.excluded (((Nat.prime_dvd_prime_iff_eq pr ep).mp ((ZMod.natCast_eq_zero_iff ..).mp z)) ▸ hq)
    have slope : ((((P:ℤ)*ell*((R.residue q:ℤ)-m):ℤ):ZMod q))≠0 := by
      push_cast; exact mul_ne_zero (mul_ne_zero punit eunit) (sub_ne_zero.mpr (R.away q hq))
    obtain ⟨c,h⟩ := linear_root_constraint q pr (eval (R.residue q:ℤ) (basePolynomial n ell side)) _ (R.residue q) slope
    refine ⟨c,fun u v => ?_⟩
    simpa only [affineValue,Int.modEq_zero_iff_dvd,Int.cast_natCast] using h u v
  have total (q : ℕ) : ∃ c : ℤ, ∀ hq : q∈R.primes, ∀ u v : ℤ,
      (q:ℤ)∣affineValue n ell (R.residue q) side (u+R.residue q*v) ↔
        (u:ZMod q)+(R.residue q:ZMod q)*v=c := by
    by_cases h : q∈R.primes
    · obtain ⟨c,w⟩ := localEq q h; exact ⟨c,fun _ => w⟩
    · exact ⟨0,fun g => (h g).elim⟩
  choose L spec using total
  exact ⟨L,fun u v => ⟨fun h q hq => (spec q hq u v).mp (h q hq),fun h q hq => (spec q hq u v).mpr (h q hq)⟩⟩

/-- Every compatible coefficient pair is parameterized uniquely by the
    first projection and the remaining conditional coefficient. -/
theorem PrescribedRows.polynomial_lattice {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool) (a : ℕ) :
    let C := {v : ℤ×ℤ // R.compatible side v.1 v.2}
    ∃ (c : ℤ) (t : ℤ→ℤ) (e : (ℤ×ℤ) ≃ C), ∀ i j : ℤ,
      let H : ℤ := R.hitProduct a
      let M : ℤ := prodPrimes (R.miss a)
      (e (i,j)).val=(c+H*i-a*(t i+M*j),t i+M*j) := by
  classical
  obtain ⟨L,hL⟩ := R.linear_equations target side
  obtain ⟨c,t,e,law⟩ := polynomial_root_lattice R.primes (fun _ h => R.prime h) (fun q => (R.residue q:ℤ)) L a
  let ident := Equiv.subtypeEquivRight (fun v : ℤ×ℤ => show (∀ q ∈ R.primes, (v.1:ZMod q)+((R.residue q:ℤ):ZMod q)*v.2=L q) ↔ R.compatible side v.1 v.2 from by simpa only [Int.cast_natCast] using (hL v.1 v.2).symm)
  have castH : (R.hitProduct a:ℤ) = ∏ q ∈ R.primes.filter (fun q => (((R.residue q:ℕ):ℤ):ZMod q)=((a:ℤ):ZMod q)), (q:ℤ) := by
    simp [hitProduct,prodPrimes,hit]
  have eq : R.miss a = R.primes.filter (fun q => (R.residue q:ZMod q)≠a) := by
    ext q; simp [miss,hit]; tauto
  have castM : (prodPrimes (R.miss a):ℤ) = ∏ q ∈ R.primes.filter (fun q => (((R.residue q:ℕ):ℤ):ZMod q)≠((a:ℤ):ZMod q)), (q:ℤ) := by
    simp [eq,prodPrimes]
  refine ⟨c,t,e.trans ident,fun i j => ?_⟩
  dsimp only [Equiv.trans_apply,ident,Equiv.subtypeEquivRight_apply]
  simp only [castH,castM]
  exact law i j

end Cogentic.Construction

#print axioms Cogentic.Construction.affine_at_constructed
#print axioms Cogentic.Construction.PrescribedRows.polynomial_lattice
