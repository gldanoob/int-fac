import Cogentic.CoprimeFamilies

namespace Cogentic.Construction
open Finset Cogentic.Window
open scoped Classical

noncomputable def bandDifferencePrimes (b a a' : ℕ) := (((a':ℤ)-a).natAbs.primeFactors) ∩ primeBand b

theorem bandDifferencePrimes_card {b a a' : ℕ} (bp : 0<b)
    (ac : a≤Fixed.A b) (bc : a'≤Fixed.A b) (diff : a≠a') :
    (bandDifferencePrimes b a a').card ≤ 20 := by
  let h := Fixed.h b; let L := 2^(500*h)
  let D := ((a':ℤ)-a).natAbs; let P := bandDifferencePrimes b a a'
  have dn : D≠0 := by dsimp only [D]; omega
  have dcap : D≤Fixed.A b := by dsimp only [D]; omega
  have hp : 0<h := Nat.mul_pos (Fixed.degree_pos bp) (Nat.succ_pos _)
  have lower (p) (pm : p∈P) : L≤p := by
    have top := (mem_primeBand.mp (mem_inter.mp pm).2).2.2
    by_contra! sm
    have bb : Fixed.B b=L^2 := by change 2^(1000*h)=(2^(500*h))^2; rw [←pow_mul]; congr 1; ring
    exact top.not_ge (bb ▸ Nat.pow_le_pow_left sm.le 2)
  have div := (prod_dvd_prod_of_subset P D.primeFactors id inter_subset_left).trans (Nat.prod_primeFactors_dvd D)
  have count : 2^(500*h*P.card) ≤ 2^(10000*h) := calc
    _ = ∏ _p∈P, L := by rw [pow_mul]; simp [L]
    _ ≤ ∏ p∈P,p := prod_le_prod' lower
    _ ≤ _ := (Nat.le_of_dvd (Nat.pos_of_ne_zero dn) div).trans dcap
  have k := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp count
  change P.card≤20
  exact Nat.le_of_mul_le_mul_left (a:=P.card) (c:=500*h)
    (by nlinarith only [k]) (by omega)

/-- At a prime dividing the mark difference, vanishing of the second
signed quotient forces the same prime into the first quotient unless
it was already forced into the first prefactor. -/
theorem PrescribedRows.difference_divides_first {n ell a a' p : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (prime : p.Prime)
    (diff : p∣((a':ℤ)-a).natAbs) (side : Bool) (u v : ℤ) (ok : R.compatible side u v)
    (away : ¬p∣R.prefactor a side) :
    p∣(R.intercept a' side u v).natAbs → p∣(R.intercept a side u v).natAbs := by
  let val (i : ℕ) := affineValue n ell i side (u+i*v)
  have eq (i : ℕ) : (R.intercept i side u v).natAbs*(R.prefactor i side)=(val i).natAbs := by
    have div := dvd_mul_of_dvd_right (R.pre_dvd target i side u v ok) (markSign n i side)
    have h := congrArg Int.natAbs (Int.ediv_mul_cancel div)
    have sig : (markSign n i side).natAbs=1 := by unfold markSign; split <;> decide
    simpa only [PrescribedRows.intercept,val,Int.natAbs_mul,Int.natAbs_natCast,sig,one_mul] using h
  have congruence : (a:ZMod p)=(a':ZMod p) := (ZMod.natCast_eq_natCast_iff ..).mpr
    (Nat.modEq_iff_dvd.mpr (Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using diff)))
  have congrVal := affine_mark_congr (n:=n) (ell:=ell) side u v congruence
  intro hit
  have dv := dvd_mul_of_dvd_left hit (R.prefactor a' side)
  rw [eq] at dv
  have zd : (p:ℤ)∣val a' := Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using dv)
  have first : (p:ℤ)∣val a := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    (congrVal.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr zd))
  have dv' : p ∣ (val a).natAbs := by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr first
  rw [←eq] at dv'
  exact (prime.dvd_mul.mp dv').resolve_right away

private theorem prefactor_dvd_at_congruent_marks {n ell a a' p : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (pp : p.Prime) (eq : (a:ZMod p)=a') (side : Bool) :
    p∣R.prefactor a side → p∣R.prefactor a' side := by
  intro dvd
  have sourceMem := Nat.mem_primeFactors.mpr ⟨pp,dvd,(R.pre_bounds target a side).1.ne'⟩
  apply Nat.dvd_of_mem_primeFactors
  rw [R.prefactor_primeFactors target] at sourceMem ⊢
  have hit (hp : p∈R.hit a) : p∈R.hit a' := mem_filter.mpr
    ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans eq⟩
  by_cases pe : p=ell
  · subst p
    have same : hitsTarget n ell a side = hitsTarget n ell a' side := by
      apply Bool.eq_iff_iff.mpr
      rw [target_hits_iff n ell a side 0,target_hits_iff n ell a' side 0]
      have mod := affine_mark_congr (n:=n) (ell:=ell) side 0 0 eq
      simp only [mul_zero,add_zero] at mod
      rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd,mod]
    rw [←same]
    split at sourceMem <;> simp_all [R.excluded,PrescribedRows.hit]
  · split at sourceMem <;> split <;> simp_all

/-- Every prime in the second class gcd either misses both prescribed rows or
was forced in both prefactors and divides the mark difference. This also
covers second classes with zero squarefree mass. -/
theorem PrescribedRows.prime_dvd_after_difference_exclusion {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a'∈(construct n ell 0 0 0 0).marks) (neq : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side)
    let P := bandDifferencePrimes (n.log2+1) a a'
    let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
    supportedValue (J \ P) (R.intercept a side u v) → ∀ p, p.Prime → p∣g →
      p∈R.miss a \ R.hit a' ∨
        (p∣R.prefactor a side ∧ p∣R.prefactor a' side ∧ p∣((a':ℤ)-a).natAbs ∧
          (p=ell ∨ p^2∣((a':ℤ)-a).natAbs)) := by
  classical
  intro J P g clean p pp qg
  let both := prodPrimes (R.hit a ∩ R.hit a')
  let free := prodPrimes (R.miss a \ R.hit a')
  have cap := ((constructed_marks_iff ..).mp mark).2.1
  have size := R.secondStep_size (mark_range hn big cap) (mem_dyadicTargets.mp target).1.pos neq side
  have gd := gcd_dvd_intercept (R.intercept a' side u v) (R.secondStep a a' side) size.2
  have freepr (p) (hp : p∈R.miss a \ R.hit a') := R.prime (mem_sdiff.mp (mem_sdiff.mp hp).1).1
  have pval := qg.trans gd.1
  have pq := qg.trans gd.2
  rw [size.1] at pq
  change p ∣ (firstModulus n ell a' (hitsTarget n ell a' side)*(a'.dist a/both))*free at pq
  have avoid := R.intercept_coprime hn big comp target absent mark side u v ok
  rcases pp.dvd_mul.mp pq with early|last
  · rcases pp.dvd_mul.mp early with old|delta
    · exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt pval old avoid).elim
    · have bothD := (R.second_factors a a').2.2.1
      have dist : ((a':ℤ)-a).natAbs=a'.dist a := by simp [Nat.dist]; omega
      have denom : both∣a'.dist a := by
        rw [←dist]
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr bothD
      have pd := delta.trans (Nat.div_dvd_of_dvd denom)
      rw [←dist] at pd
      have mod : (a:ZMod p)=a' := (ZMod.natCast_eq_natCast_iff ..).mpr
        (Nat.modEq_iff_dvd.mpr (Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using pd)))
      by_cases forced : p∣R.prefactor a side
      · have other := prefactor_dvd_at_congruent_marks R target pp mod side forced
        refine Or.inr ⟨forced,other,pd,?_⟩
        by_cases pe : p=ell
        · exact Or.inl pe
        right
        have hit (i : ℕ) (hi : p∣R.prefactor i side) : p∈R.hit i := by
          have pm := Nat.mem_primeFactors.mpr ⟨pp,hi,(R.pre_bounds target i side).1.ne'⟩
          rw [R.prefactor_primeFactors target] at pm
          split at pm <;> simpa [pe] using pm
        have pb : p∣both := Finset.dvd_prod_of_mem id (mem_inter.mpr ⟨hit a forced,hit a' other⟩)
        rw [pow_two,dist,←Nat.div_mul_cancel denom]
        exact Nat.mul_dvd_mul delta pb
      have val := R.difference_divides_first target pp pd side u v ok forced pval
      obtain ⟨x,xm,xx⟩ := mem_image.mp clean
      have xp := (mem_squarefreeSupport _ (fun t h => (mem_primeBand.mp (mem_filter.mp (mem_sdiff.mp h).1).1).1) x).mp xm
      rw [←xx] at val
      have px := xp.2 (Nat.mem_primeFactors.mpr ⟨pp,val,xp.1.ne_zero⟩)
      have ordinary := (mem_filter.mp (mem_sdiff.mp px).1).1
      exact ((mem_sdiff.mp px).2 (mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp,pd,by omega⟩,ordinary⟩)).elim
  · have pf : free.primeFactors=R.miss a \ R.hit a' := Nat.primeFactors_prod freepr
    left
    rw [←pf]
    exact Nat.mem_primeFactors.mpr ⟨pp,last,(R.second_factors a a').2.2.2.2.2.1.ne'⟩

/-- After deleting the band primes of the mark difference from the first
quotient, a supported second class gcd can contain only prescribed primes
that miss both marks. There are at most two such primes. -/
theorem PrescribedRows.supported_gcd_after_difference_exclusion {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a'∈(construct n ell 0 0 0 0).marks) (neq : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side); let J' := sieveBand n ell (R.prefactor a' side)
    let P := bandDifferencePrimes (n.log2+1) a a'
    let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
    supportedValue (J \ P) (R.intercept a side u v) → g∈squarefreeSupport J' →
      g∈squarefreeSupport (R.miss a \ R.hit a') := by
  classical
  intro J J' P g clean supported
  have freepr (p) (hp : p∈R.miss a \ R.hit a') := R.prime (mem_sdiff.mp (mem_sdiff.mp hp).1).1
  have sf := (mem_squarefreeSupport J' (fun p h => (mem_primeBand.mp (mem_filter.mp h).1).1) g).mp supported
  apply (mem_squarefreeSupport _ freepr _).mpr
  refine ⟨sf.1,?_⟩
  intro p hp
  have cases := R.prime_dvd_after_difference_exclusion hn big comp target absent mark neq side u v ok
    clean p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  exact cases.resolve_right (fun h => (mem_filter.mp (sf.2 hp)).2.2 h.2.1)

/-- When the two prefactors are coprime and every prescribed prime hits
at least one mark, the cleaned first observation forces the second
class to be a unit class. -/
theorem PrescribedRows.unit_gcd_after_difference_exclusion {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a'∈(construct n ell 0 0 0 0).marks) (neq : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side)
    let P := bandDifferencePrimes (n.log2+1) a a'
    let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
    (R.miss a \ R.hit a')=∅ → (R.prefactor a side).Coprime (R.prefactor a' side) →
    supportedValue (J \ P) (R.intercept a side u v) → g=1 := by
  intro J P g empty co clean
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p pp pg
  rcases R.prime_dvd_after_difference_exclusion hn big comp target absent mark neq side u v ok clean p pp pg with hit|both
  · simp [empty] at hit
  · exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt both.1 both.2.1 co

/-- If no residual prescribed prime is free, removing prescribed prime
squares from the difference suffices even when ordinary prefactors overlap.
A common target hit is the only remaining exception. -/
theorem PrescribedRows.unit_gcd_on_clean_pair {n ell a a' : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a'∈(construct n ell 0 0 0 0).marks) (neq : a'≠a) (side : Bool) (u v : ℤ) (ok : R.compatible side u v) :
    let J := sieveBand n ell (R.prefactor a side)
    let P := bandDifferencePrimes (n.log2+1) a a'
    let g := commonDivisor (R.intercept a' side u v) (R.secondStep a a' side)
    (R.miss a \ R.hit a')=∅ →
    (¬ell∣R.prefactor a side ∨ ¬ell∣R.prefactor a' side) →
    (∀ p∈R.hit a, ¬p^2∣((a':ℤ)-a).natAbs) →
    supportedValue (J \ P) (R.intercept a side u v) → g=1 := by
  intro J P g empty targetMiss squareClean clean
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p pp pg
  rcases R.prime_dvd_after_difference_exclusion hn big comp target absent mark neq side u v ok clean p pp pg with hit|both
  · simp [empty] at hit
  · obtain ⟨ha,hb,_,cases⟩ := both
    by_cases pe : p=ell
    · subst p; exact targetMiss.elim (· ha) (· hb)
    have pm := Nat.mem_primeFactors.mpr ⟨pp,ha,(R.pre_bounds target a side).1.ne'⟩
    rw [R.prefactor_primeFactors target] at pm
    have ordinary : p∈R.hit a := by split at pm <;> simpa [pe] using pm
    exact squareClean p ordinary (cases.resolve_left pe)

/-- At two different marks, deleting all large prime factors of their
difference from the first smooth quotient has uniformly small relative
cost on the actual coefficient distribution. -/
theorem PrescribedRows.difference_exclusion_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → a'≤Fixed.A b → a≠a' → ∀ side : Bool,
    let J := sieveBand n ell (R.prefactor a side)
    let prob := fun T => prescribedProbability R side (fun k => supportedValue T (R.intercept a side k.1 k.2))
    prob J - prob (J \ bandDifferencePrimes b a a') ≤
      (720*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*Real.exp (-(Fixed.U b:ℝ)))*prob J := by
  obtain ⟨b₀,h⟩ := PrescribedRows.smooth_probability_avoid_sharp line 1
  refine ⟨max b₀ 20,?_⟩
  intro n ell a a' R b large hn comp target absent mark cap diff side J prob
  obtain ⟨one,two⟩ := max_le_iff.mp large
  let P := bandDifferencePrimes b a a'
  have c : P.card≤20 := bandDifferencePrimes_card (Nat.succ_pos _) ((constructed_marks_iff ..).mp mark).2.1 cap diff
  have del := (h R one hn comp target absent mark side P (by simpa only [pow_one] using c.trans two)).2.2
  apply del.trans
  have pos : 0≤prob J := by
    apply div_nonneg
    · apply tsum_nonneg; intro x; split <;> first | exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le | rfl
    · exact tsum_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  apply mul_le_mul_of_nonneg_right _ pos
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith only [show (P.card:ℝ) ≤ 20 by exact_mod_cast c]

end Cogentic.Construction
