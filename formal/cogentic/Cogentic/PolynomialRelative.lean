import Cogentic.PolynomialWindows
import Cogentic.RelativeAffine

namespace Cogentic.Construction
open Real Cogentic.Window

/-- The true tilted model for one surviving signed residue class. -/
def PositiveScalarModel (n ell pre : ℕ) (c s : ℤ) (Y S K C α : ℝ) : Prop :=
  let b := n.log2+1
  let H := log (Fixed.B b)
  let J := sieveBand n ell pre
  let band := J.filter (fun p => ¬p ∣ s.natAbs)
  let D := primeBand b \ band
  let g := commonDivisor c s
  let q := s.natAbs/g
  let y := Y/(pre*(g:ℝ))
  let M := omittedMass (primeBand b) D (primeProbability α) (fun p => log p) H 0
  let model := ((q:ℝ)/q.totient)*(y^(α-1)*eulerMass band α)*M
  α ∈ Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) α=log y ∧
    0 < model ∧ ‖(2*π:ℝ) • scalarMass J c s (Y/pre) (S/pre)-(model:ℂ)‖ ≤
      C*model*exp (-K*(Fixed.z b:ℝ)^2)

/-- The true window vanishes when the class gcd is ineligible. In the
    supported case the saddle model is positive with a relative error. -/
def ScalarAlternative (n ell pre : ℕ) (c s : ℤ) (Y S K C : ℝ) : Prop :=
  let J := sieveBand n ell pre
  let g := commonDivisor c s
  (g ∉ squarefreeSupport J → scalarMass J c s (Y/pre) (S/pre) = 0) ∧
  (g ∈ squarefreeSupport J → ∃ α, PositiveScalarModel n ell pre c s Y S K C α)

private theorem scalar_relative_at_center (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell pre : ℕ} {c s : ℤ} {Y S : ℝ}, b₀≤n.log2+1 →
    2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    ScalarReady n pre c s Y S → ScalarAlternative n ell pre c s Y S K C := by
  obtain ⟨C,Cp,b₀,estimate⟩ := scalar_progression_relative line K hk
  refine ⟨C,Cp,b₀,?_⟩
  intro n ell pre c s Y S threshold hn comp target none ready
  let b := n.log2+1; let H := log (Fixed.B b)
  let y := Y/(pre*(commonDivisor c s:ℝ))
  let u := log y/H
  have dp := Fixed.degree_pos (b := b) (Nat.succ_pos _)
  have bet : 0<Fixed.beta b := Nat.mul_pos (by decide) (Nat.mul_pos dp (Nat.succ_pos _))
  have base : 1<Fixed.B b := Nat.one_lt_pow bet.ne' (by decide)
  have pos : 0<H := Real.log_pos (by exact_mod_cast base)
  have eq : H*u=log y := by dsimp [u]; field_simp
  have w := ready.window
  have shift : |H*u-log y| ≤ 2*H := by rw [eq,sub_self,abs_zero]; positivity
  obtain ⟨zero,positive⟩ := estimate c s Y S u threshold hn comp target none ready.prepos ready.prebound
    ready.nonzero ready.cap ready.width w w.2.2.1 w.2.2.2.1 shift
  refine ⟨zero,?_⟩
  intro supported
  obtain ⟨α,ha,mean,h⟩ := positive supported
  change saddleMean (primeBand b) α = H*u at mean
  rw [eq] at mean
  refine ⟨α,ha,mean,?_⟩
  have zeroShift : log (Fixed.B (n.log2+1))*u-log (Y/(pre*(commonDivisor c s:ℝ)))=0 := by
    change H*u-log y=0; rw [eq,sub_self]
  dsimp only at h
  simpa only [zeroShift] using h

/-- The first evaluation on every admissible polynomial coefficient lattice
    has a positive relative saddle model. Its prescribed integer quotient
    covers precisely the indicated signed progression. -/
theorem first_polynomial_progression (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), b₀≤n.log2+1 → 2≤n →
    ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let c := R.intercept a side u v; let s := firstStep n ell a side; let pre := R.prefactor a side
    commonDivisor c s=1 ∧
      (∀ j : ℤ, markSign n a side*affineValue n ell a side (u+a*v+R.hitProduct a*j)/(pre:ℤ)=c+s*j) ∧
      ∃ α, PositiveScalarModel n ell pre c s (exactMean n ell a side) (oneWidth n ell a) K C α := by
  obtain ⟨C,Cp,b₁,estimate⟩ := scalar_relative_at_center line K hk
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨C,Cp,max b₁ b₂,?_⟩
  intro n ell a R bs hn comp target none mark side u v ok
  obtain ⟨bhi,bdeg⟩ := max_le_iff.mp bs
  obtain ⟨one,law,ready⟩ := first_polynomial_data R hn (degree _ bdeg) comp target none mark side u v ok
  have relative := estimate bhi hn comp target none ready
  refine ⟨one,law,relative.2 ?_⟩
  rw [one]
  let J := sieveBand n ell (R.prefactor a side)
  have pg (q : ℕ) (hq : q∈J) := (mem_primeBand.mp (Finset.mem_filter.mp hq).1).1
  exact (mem_squarefreeSupport J pg 1).mpr ⟨squarefree_one,by simp⟩

/-- The second evaluation on a clean separated pair admits exact gcd
    reduction and the full signed relative saddle estimate, including the
    zero branch for unsupported classes. -/
theorem second_polynomial_progression (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), b₀≤n.log2+1 → 2≤n →
    ¬n.Prime → ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
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
      ScalarAlternative n ell pre c s (conditionalMean n ell a a' side obs) (twoWidth n ell a a') K C := by
  obtain ⟨C,Cp,b₁,estimate⟩ := scalar_relative_at_center line K hk
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨C,Cp,max b₁ b₂,?_⟩
  intro n ell a a' R bs hn comp target none cap mark clean side u v ok obs central
  obtain ⟨bhi,bdeg⟩ := max_le_iff.mp bs
  obtain ⟨dv,capg,law,ready⟩ := second_polynomial_data R hn (degree _ bdeg) comp target none cap mark clean side u v ok central
  exact ⟨dv,capg,law,estimate bhi hn comp target none ready⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.first_polynomial_progression
#print axioms Cogentic.Construction.second_polynomial_progression
