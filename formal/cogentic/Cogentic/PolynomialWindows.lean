import Cogentic.ScalarSteps

namespace Cogentic.Construction
open Cogentic.Window

/-- The normalized scalar sum and its reduced principal window for the
    integer progression of a prescribed polynomial evaluation. -/
def ScalarEstimate (n ell pre : ℕ) (c s : ℤ) (Y S C : ℝ) : Prop :=
  let J := sieveBand n ell pre
  ‖scalarMass J c s (Y/pre) (S/pre)-scalarPrincipal J c s (Y/pre) (S/pre)‖ ≤
    C*(Y/(pre*(commonDivisor c s:ℝ)))^(-3/1000:ℝ)

theorem PrescribedRows.first_divisor {n ell a : ℕ} (R : PrescribedRows n ell) (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    commonDivisor (R.intercept a side u v) (firstStep n ell a side) = 1 := by
  have p := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  have ⟨sz,nz⟩ := firstStep_size (mark_range hn big p.2.1) (mem_dyadicTargets.mp target).1.pos side
  have cop := R.intercept_coprime hn big comp target none mark side u v ok
  obtain ⟨first,modulus⟩ := gcd_dvd_intercept (R.intercept a side u v) (firstStep n ell a side) nz
  exact Nat.eq_one_of_dvd_coprimes cop first (sz ▸ modulus)

theorem PrescribedRows.second_divisor {n ell a a' : ℕ} (R : PrescribedRows n ell) (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (cap : a≤Fixed.A (n.log2+1)) (mark : a'∈(construct n ell 0 0 0 0).marks)
    (ne : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
    let both := prodPrimes (R.hit a ∩ R.hit a')
    let free := prodPrimes (R.miss a \ R.hit a')
    g ∣ ((a'.dist a)/both)*free ∧ g ≤ Fixed.A (n.log2+1)*(Fixed.B (n.log2+1))^2 := by
  let b := n.log2+1; let A := Fixed.A b; let B := Fixed.B b
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let free := prodPrimes (R.miss a \ R.hit a')
  let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
  have p := (constructed_marks_iff n ell 0 0 0 0 a').mp mark
  have ⟨sz,nz⟩ := R.secondStep_size (a := a) (mark_range hn big p.2.1) (mem_dyadicTargets.mp target).1.pos ne side
  have ⟨_,_,bothDiv,bp,_,fp,fc⟩ := R.second_factors a a'
  have cop := R.intercept_coprime hn big comp target none mark side u v ok
  have ⟨ig,modulus⟩ := gcd_dvd_intercept (R.intercept a' side u v) (R.secondStep a a' side) nz
  have step : g ∣ (firstModulus n ell a' (hitsTarget n ell a' side))*(((a'.dist a)/both)*free) := by
    rw [←Nat.mul_assoc]
    rw [sz] at modulus; exact modulus
  have dividend := (Nat.Coprime.of_dvd_left ig cop).dvd_of_dvd_mul_left step
  have cap' := p.2.1
  have dcap : a'.dist a ≤ A := by rw [Nat.dist_eq_max_sub_min]; exact (Nat.sub_le ..).trans (max_le cap' cap)
  have qpos : 0 < (a'.dist a)/both := by
    have nonzero : firstModulus n ell a' (hitsTarget n ell a' side)*((a'.dist a)/both)*free ≠ 0 :=
      (by have p := (Int.natAbs_pos.mpr nz).ne'; rw [sz] at p; exact p)
    exact Nat.pos_of_ne_zero (fun zero => nonzero (by rw [zero,mul_zero,zero_mul]))
  exact ⟨dividend,(Nat.le_of_dvd (Nat.mul_pos qpos fp) dividend).trans (Nat.mul_le_mul ((Nat.div_le_self _ _).trans dcap) fc)⟩

theorem total_prefactor {n ell a g : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (gp : 0<g) (bound : g≤Fixed.A (n.log2+1)*(Fixed.B (n.log2+1))^2) :
    1 ≤ (R.prefactor a side:ℝ)*g ∧ (R.prefactor a side:ℝ)*g ≤ (Fixed.A (n.log2+1):ℝ)*(Fixed.B (n.log2+1):ℝ)^40 := by
  let b := n.log2+1; let B := Fixed.B b; let A := Fixed.A b
  have bp : 0<B := Nat.pow_pos (by decide)
  obtain ⟨pre,ub⟩ := R.pre_bounds target a side
  constructor
  · exact_mod_cast Nat.mul_pos pre gp
  · have h := Nat.mul_le_mul ub bound
    calc (R.prefactor a side:ℝ)*g ≤ (B:ℝ)^3*(A*(B:ℝ)^2) := by exact_mod_cast h
         _ = (A:ℝ)*(B:ℝ)^5 := by ring
         _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_left A (Nat.pow_le_pow_right bp (by decide : 5≤40))

/-- Checked numerical and arithmetic prerequisites of a normalized scalar
    Fourier or character estimate. -/
structure ScalarReady (n pre : ℕ) (c s : ℤ) (Y S : ℝ) : Prop where
  prepos : 0 < pre
  prebound : pre ≤ (Fixed.B (n.log2+1))^3
  nonzero : s ≠ 0
  cap : s.natAbs ≤ conductorCap n
  width : 0 < S
  window : InWindow (n.log2+1) (Y/(pre*(commonDivisor c s:ℝ))) (S/(pre*(commonDivisor c s:ℝ)))

/-- For every surviving grid mark and every compatible polynomial
    coefficient pair, the first signed scalar progression is already
    reduced. Its full squarefree Gaussian sum obeys the progression bound. -/
theorem first_polynomial_data :
    ∀ {n ell a : ℕ} (R : PrescribedRows n ell), 2≤n →
    10004≤Fixed.d (n.log2+1) → ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let c := R.intercept a side u v; let s := firstStep n ell a side; let pre := R.prefactor a side
    commonDivisor c s = 1 ∧
      (∀ j : ℤ, markSign n a side*affineValue n ell a side (u+a*v+R.hitProduct a*j)/(pre:ℤ) = c+s*j) ∧
      ScalarReady n pre c s (exactMean n ell a side) (oneWidth n ell a) := by
  intro n ell a R hn big comp target none mark side u v ok
  let b := n.log2+1; let B := Fixed.B b; let A := Fixed.A b
  let c := R.intercept a side u v; let s := firstStep n ell a side
  let g := commonDivisor c s; let pre := R.prefactor a side
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  have gcd1 : g=1 := R.first_divisor hn big comp target none mark side u v ok
  have ⟨size,nz⟩ := firstStep_size (mark_range hn big cap) (mem_dyadicTargets.mp target).1.pos side
  have ⟨pp,preCap⟩ := R.pre_bounds target a side
  have bp : 0<B := Nat.pow_pos (by decide)
  have ap : 0<A := Nat.pow_pos (by decide)
  have gp : 0<g := gcd1 ▸ Nat.zero_lt_one
  have fb := total_prefactor R side target gp (by change g≤A*B^2; rw [gcd1]; exact Nat.mul_pos ap (Nat.pow_pos bp)) (a := a)
  have win := one_point_window hn big target cap grid side _ fb
  have sc := (actual_conductor_caps (both := 1) (free := 1) (aux := 1) target cap cap
    (show 1≤B^2 from Nat.pow_pos bp) (show 1≤B^7 from Nat.pow_pos bp) (hitsTarget n ell a side)).1
  have sCap : s.natAbs ≤ conductorCap n := size ▸ (by simpa using sc)
  have pos : 0 < oneWidth n ell a := (div_pos_iff_of_pos_right
    (mul_pos (by exact_mod_cast pp) (by exact_mod_cast gp))).mp win.1
  exact ⟨gcd1,R.first_quotient target a side u v ok,⟨pp,preCap,nz,sCap,pos,win⟩⟩

/-- For a clean separated pair and a central first observation, every second
    polynomial progression either has zero supported mass or has the stated
    reduced principal term. The common divisor divides the actual remaining
    hit-prime and diagonal factors. -/
theorem second_polynomial_data :
    ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), 2≤n →
    10004≤Fixed.d (n.log2+1) → ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    a≤Fixed.A (n.log2+1) → a'∈(construct n ell 0 0 0 0).marks →
    (Fixed.A (n.log2+1):ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit (n.log2+1):ℝ)^50 →
    ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let obs : ℝ := u+(a:ℝ)*v
    |obs-lineCenter n a| ≤ ((n.log2+1:ℕ):ℝ)^3*projectionScale n a →
    let c := R.intercept a' side u v; let s := R.secondStep a a' side; let pre := R.prefactor a' side
    let g := commonDivisor c s; let both := prodPrimes (R.hit a ∩ R.hit a'); let free := prodPrimes (R.miss a \ R.hit a')
    g ∣ ((a'.dist a)/both)*free ∧ g ≤ Fixed.A (n.log2+1)*(Fixed.B (n.log2+1))^2 ∧
      (∀ j : ℤ, markSign n a' side*affineValue n ell a' side (u+a'*v+((a':ℤ)-a)*prodPrimes (R.miss a)*j)/(pre:ℤ)=c+s*j) ∧
      ScalarReady n pre c s (conditionalMean n ell a a' side obs) (twoWidth n ell a a') := by
  intro n ell a a' R hn big comp target none cap mark clean side u v ok obs central
  let b := n.log2+1; let B := Fixed.B b; let A := Fixed.A b
  let c := R.intercept a' side u v; let s := R.secondStep a a' side
  let g := commonDivisor c s; let pre := R.prefactor a' side
  obtain ⟨_,cap',grid',_⟩ := (constructed_marks_iff n ell 0 0 0 0 a').mp mark
  have bp : 0<B := Nat.pow_pos (by decide); have ap : 0<A := Nat.pow_pos (by decide)
  have diff : a'≠a := by
    intro eq; rw [eq,sub_self,abs_zero,zero_mul] at clean
    have : 0 < (A:ℝ) := by exact_mod_cast ap
    exact this.not_ge clean
  have ⟨size,nz⟩ := R.secondStep_size (mark_range hn big cap') (mem_dyadicTargets.mp target).1.pos diff side
  have gp : 0<g := Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr nz)
  have ⟨divides,ub⟩ := R.second_divisor hn big comp target none cap mark diff side u v ok
  have fb := total_prefactor R side target gp ub (a := a')
  have win := two_point_window hn big target cap cap' grid' clean side obs _ central fb
  have ⟨pp,preCap⟩ := R.pre_bounds target a' side
  have h := R.second_factors a a'
  have sc := (actual_conductor_caps (both := prodPrimes (R.hit a ∩ R.hit a')) (aux := 1) target cap cap'
    h.2.2.2.2.2.2 (show 1≤B^7 from Nat.pow_pos bp) (hitsTarget n ell a' side)).2
  have sCap : s.natAbs ≤ conductorCap n := size ▸ (by simpa using sc)
  have pos : 0 < twoWidth n ell a a' := (div_pos_iff_of_pos_right
    (mul_pos (by exact_mod_cast pp) (by exact_mod_cast gp))).mp win.1
  exact ⟨divides,ub,R.second_quotient target a a' side u v ok,⟨pp,preCap,nz,sCap,pos,win⟩⟩

theorem polynomial_progression_discrepancy (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∀ {n ell pre : ℕ} {c s : ℤ} {Y S : ℝ}, 2≤n →
    10004≤Fixed.d (n.log2+1) → ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    ScalarReady n pre c s Y S → ScalarEstimate n ell pre c s Y S C := by
  obtain ⟨C,Cp,main⟩ := scalar_progression_discrepancy line
  refine ⟨C,Cp,?_⟩
  intro n ell pre c s Y S hn big comp target none ready
  exact main c s Y S hn big comp target none ready.prepos ready.prebound ready.nonzero ready.cap ready.width ready.window

end Cogentic.Construction

#print axioms Cogentic.Construction.first_polynomial_data
#print axioms Cogentic.Construction.second_polynomial_data
