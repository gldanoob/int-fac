import Cogentic.RestrictedPairUpper

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- Union bound for events in the prescribed coefficient distribution. Only
compatible coefficient pairs enter its pointwise covering hypothesis. -/
theorem PrescribedRows.probability_cover_sum {ι : Type*} {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (S : Finset ι) (A : ℤ×ℤ→Prop) [DecidablePred A]
    (B : ι→ℤ×ℤ→Prop) [∀ i,DecidablePred (B i)]
    (cover : ∀ k, R.compatible side k.1 k.2 → A k → ∃ i∈S,B i k) :
    prescribedProbability R side A ≤ ∑ i∈S,prescribedProbability R side (B i) := by
  classical
  have left := R.point_event side target A
  have right := hasSum_sum (s:=S) (fun i _ => R.point_event side target (B i))
  rw [←left.tsum_eq,←right.tsum_eq]
  apply left.summable.tsum_le_tsum _ right.summable
  intro k
  by_cases h : A k.val
  · obtain ⟨i,hi,yes⟩ := cover k.val k.property h
    rw [if_pos h]
    calc R.pointMass side k = (if B i k.val then R.pointMass side k else 0) := (if_pos yes).symm
         _ ≤ _ := single_le_sum (f:=fun i => if B i k.val then R.pointMass side k else 0)
           (fun i _=>by split <;> first | exact R.pointMass_nonneg side k | rfl) hi
  · rw [if_neg h]
    exact sum_nonneg (fun i _ => by split <;> first | exact R.pointMass_nonneg side k | rfl)

/-- A first quotient is exceptional for p if some compatible coefficients
with that quotient have a second quotient divisible by p. -/
def PrescribedRows.badFirstQuotient {n ell : ℕ} (R : PrescribedRows n ell)
    (a y : ℕ) (side : Bool) (p : ℕ) (z : ℤ) : Prop :=
  ∃ u v : ℤ, R.compatible side u v ∧ R.intercept a side u v=z ∧ p∣(R.intercept y side u v).natAbs

/-- These are the only possible primes obstructing a unit fiber after
removing ordinary prescribed prime squares from the difference. -/
def PrescribedRows.exceptionPrimes {n ell : ℕ} (R : PrescribedRows n ell) (a y : ℕ) (side : Bool) : Finset ℕ :=
  (R.miss a \ R.hit y) ∪ (if hitsTarget n ell a side ∧ hitsTarget n ell y side ∧ (a:ZMod ell)=(y:ZMod ell)
    then {ell} else ∅)

theorem PrescribedRows.exceptionPrimes_card {n ell : ℕ} (R : PrescribedRows n ell) (a y : ℕ) (side : Bool) :
    (R.exceptionPrimes a y side).card ≤ 3 := by
  have sub : (R.miss a \ R.hit y)⊆R.primes := sdiff_subset.trans sdiff_subset
  have le := (card_le_card sub).trans R.limit
  unfold PrescribedRows.exceptionPrimes
  split
  · exact (card_union_le ..).trans (by simp; omega)
  · simp; omega

theorem PrescribedRows.unit_gcd_after_all_exclusions {n ell a y : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : y∈(construct n ell 0 0 0 0).marks) (neq : y≠a) (side : Bool)
    (squareClean : ∀ p∈R.hit a, ¬p^2∣((y:ℤ)-a).natAbs)
    (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side)
    let K := J \ bandDifferencePrimes (n.log2+1) a y
    let z := R.intercept a side u v
    supportedValue K z → (∀ p∈R.exceptionPrimes a y side, ¬R.badFirstQuotient a y side p z) →
      commonDivisor (R.intercept y side u v) (R.secondStep a y side)=1 := by
  intro J K z smooth avoid
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p pp pg
  have nz := (R.secondStep_size (mark_range hn big ((constructed_marks_iff ..).mp mark).2.1)
    (mem_dyadicTargets.mp target).1.pos neq side).2
  have bad : R.badFirstQuotient a y side p z := ⟨u,v,ok,rfl,pg.trans (gcd_dvd_intercept _ _ nz).1⟩
  apply (avoid p _) bad
  rcases R.prime_dvd_after_difference_exclusion hn big comp target absent mark neq side u v ok smooth p pp pg with free|both
  · exact mem_union_left _ free
  obtain ⟨pa,py,pd,wherein⟩ := both
  by_cases pe : p=ell
  · subst p
    have hit (i : ℕ) (dvd : ell∣R.prefactor i side) : hitsTarget n ell i side := by
      have mem := Nat.mem_primeFactors.mpr ⟨pp,dvd,(R.pre_bounds target i side).1.ne'⟩
      rw [R.prefactor_primeFactors target] at mem
      split at mem
      · assumption
      · exact (R.excluded (mem_filter.mp mem).1).elim
    have eq : (a:ZMod ell)=y := (ZMod.natCast_eq_natCast_iff ..).mpr
      (Nat.modEq_iff_dvd.mpr (Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using pd)))
    exact mem_union_right _ (by simp [hit a pa,hit y py,eq])
  · have pm := Nat.mem_primeFactors.mpr ⟨pp,pa,(R.pre_bounds target a side).1.ne'⟩
    rw [R.prefactor_primeFactors target] at pm
    have hit : p∈R.hit a := by split at pm <;> simpa [pe] using pm
    exact (squareClean p hit (wherein.resolve_left pe)).elim

/-- At most three exceptional congruences add three times their individual
relative cost to the loss from prime divisors of the difference. -/
theorem PrescribedRows.clean_observation_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y≤Fixed.A b → a≠y → ∀ (side : Bool) (δ : ℝ), 0≤δ →
    let J := sieveBand n ell (R.prefactor a side)
    let K := J \ bandDifferencePrimes b a y
    let z := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue J (z k)
    let S := R.exceptionPrimes a y side
    let bad := R.badFirstQuotient a y side
    let keep := fun v => supportedValue K v ∧ ∀ p∈S, ¬bad p v
    let P := prescribedProbability R side smooth
    (∀ p∈S, prescribedProbability R side (fun k => smooth k ∧ bad p (z k)) ≤ δ*P) →
    let η := 720*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ))
    P - prescribedProbability R side (fun k=>keep (z k)) ≤ (η+3*δ)*P := by
  classical
  obtain ⟨b₀,loss⟩ := PrescribedRows.difference_exclusion_loss line
  refine ⟨b₀,?_⟩
  intro n ell a y R b large hn comp target absent am cap diff side δ dp J K z smooth S bad keep P rates η
  let clean := fun k : ℤ×ℤ => supportedValue K (z k)
  let result := fun k : ℤ×ℤ => keep (z k)
  have sub (k : ℤ×ℤ) (h : clean k) : smooth k := by
    obtain ⟨x,hx,eq⟩ := mem_image.mp h
    obtain ⟨ps,hp,eqp⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨x,mem_image.mpr ⟨ps,mem_powerset.mpr ((mem_powerset.mp hp).trans sdiff_subset),eqp⟩,eq⟩
  have pr : 0≤P := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun _=>mul_nonneg (exp_pos _).le (exp_pos _).le)
  have omitted := loss R large hn comp target absent am cap diff side
  change P-prescribedProbability R side clean≤η*P at omitted
  have part := R.deleted_probability target side clean result (fun _ h=>h.1)
  have cover := R.probability_cover_sum target side S (fun k => clean k ∧ ¬result k)
    (fun p k => smooth k ∧ bad p (z k)) (fun k _ h=>by
      by_contra! none
      exact h.2 ⟨h.1,fun p hp hit=>none p hp (sub k h.1) hit⟩)
  rw [part] at cover
  have sumRate := sum_le_sum rates
  rw [sum_const,nsmul_eq_mul] at sumRate
  have sc : (S.card:ℝ)≤3 := by exact_mod_cast R.exceptionPrimes_card a y side
  have total := cover.trans (sumRate.trans (mul_le_mul_of_nonneg_right sc (mul_nonneg dp pr)))
  change P-prescribedProbability R side result ≤ _
  linarith only [omitted,total]


end
end Cogentic.Construction
