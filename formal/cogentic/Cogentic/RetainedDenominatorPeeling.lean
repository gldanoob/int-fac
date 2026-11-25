import Cogentic.RetainedDenominator
import Cogentic.RejectedColumnPeeling
import Cogentic.PooledResidueMoment

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The prior on individual marks induced by a mixture of constructor cells.
In the event of overlap both cell contributions belong to the mark. -/
def constructorMixturePrior (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ) : ℕ→ℝ :=
  pooledMarkWeight univ (constructorCellMarks n ell) (fun c _=>mix c/(constructorCellMarks n ell c).card)

/-- Finite integration against the single prior is exactly the mixture of
the within-cell averages. This identity also covers empty cells. -/
theorem constructor_mixture_prior_sum (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (f : ℕ→ℝ) :
    (∑ a∈univ.biUnion (constructorCellMarks n ell),constructorMixturePrior n ell mix a*f a) =
    ∑ c,mix c*((∑ a∈constructorCellMarks n ell c,f a)/(constructorCellMarks n ell c).card) := by
  simp only [constructorMixturePrior,pooledMarkWeight,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (subset_biUnion_of_mem _ (mem_univ c)),←mul_sum]
  ring

theorem constructor_mixture_prior_nonneg (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (pos : ∀ c, 0 ≤ mix c) (a : ℕ) : 0≤constructorMixturePrior n ell mix a := by
  unfold constructorMixturePrior pooledMarkWeight
  exact sum_nonneg (fun c _=>by split <;> first | exact div_nonneg (pos c) (Nat.cast_nonneg _) | rfl)

theorem constructor_mixture_prior_mass_le (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (pos : ∀ c, 0 ≤ mix c) (norm : (∑ c,mix c)=1) :
    (∑ a∈univ.biUnion (constructorCellMarks n ell),|constructorMixturePrior n ell mix a|)≤1 := by
  simp_rw [abs_of_nonneg (constructor_mixture_prior_nonneg n ell mix pos _)]
  have law := constructor_mixture_prior_sum n ell mix (fun _=>1)
  simp only [sum_const,nsmul_one,mul_one] at law
  rw [law,←norm]
  apply sum_le_sum
  intro c _
  exact mul_le_of_le_one_right (pos c) (div_self_le_one _)

/-- The denominator on the actual draw uses the identical physical weights
as the discarded-column energy. -/
theorem retained_denominator_eq_prior (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (x y : ℤ×ℤ) :
    let O := PrescribedRows.unrestricted n ell
    retainedCommonDenominator n ell mix x y =
    ∑ a∈(univ.biUnion (constructorCellMarks n ell)).filter (fun a=>keptSmoothMark O O a x y),
      constructorMixturePrior n ell mix a/smoothMarkProbability O O a := by
  intro O
  have law := constructor_mixture_prior_sum n ell mix (fun a=>if keptSmoothMark O O a x y then
    (smoothMarkProbability O O a)⁻¹ else 0)
  apply law.symm.trans
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  split <;> simp_all only [mul_zero,div_eq_mul_inv]

set_option maxHeartbeats 800000 in
/-- A single successful stage-one draw has a substantial physical denominator,
small discarded mass, a small initial set of ordinary rows with large lost
diagonals, and low lost quadratic energy on the remaining ordinary rows.
A further family of tests can spend the remaining expectation budget. -/
theorem retained_denominator_rejection_peeling (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let e := exp (-(Fixed.z b:ℝ)^2)
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c, 0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ mass scale : Marking.Row→ℝ, (∀ i,i.q.Prime → mass i*scale i^2=1) →
    ∀ (cost : Ω→ℝ) (budget : ℝ), (∀ t,0≤cost t) →
    HasSum (fun t=>twoFieldWeight O O t*cost t) budget →
    budget+256/(Fixed.d b:ℝ)+5*e+1/(Fixed.B b:ℝ)<1 →
    ∃ t : Ω, let x := t.1.val; let y := t.2.val
      let input := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
      let rows := input.rows.toFinset.filter (fun i=>i.q≠ell)
      let X := univ.biUnion (constructorCellMarks n ell)
      let Y := X.filter (fun a=>rejectedSmoothMark O O a x y)
      let wt := fun a=>constructorMixturePrior n ell mix a/smoothMarkProbability O O a
      let z := fun (i : Marking.Row) (a : ℕ)=>if a%i.q=i.r then scale i else 0
      let bad := rows.filter (fun i=>e ≤ ∑ a∈Y,wt a*(z i a)^2)
      retainedDenominatorGood n ell mix x y ∧ cost t<1 ∧
      (∑ a∈Y,wt a)<e^3 ∧ (∑ i∈bad,mass i)≤b*e^2 ∧
      ∀ v : Marking.Row→ℝ, (∑ a∈Y,wt a*(∑ i∈rows\bad,z i a*v i)^2)≤
        (b:ℝ)*e*(∑ i∈rows\bad,(v i)^2) := by
  classical
  obtain ⟨n₁,chooseDraw⟩ := retained_denominator_with_tests line
  obtain ⟨b₁,lossLaw⟩ := rejected_score_loss line 4 (by norm_num)
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 130000
  refine ⟨max n₁ (max 2 (2^(max b₁ b₂))),?_⟩
  intro n large ell target comp absent b e O Ω mix pos norm mass scale unit cost budget nonneg ex fit
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp more
  obtain ⟨bl,bd⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  have deg := degree b bd
  have ep : 0<e := exp_pos _
  let X := univ.biUnion (constructorCellMarks n ell)
  let prior := constructorMixturePrior n ell mix
  let Y (t : Ω) := X.filter (fun a=>rejectedSmoothMark O O a t.1.val t.2.val)
  let wt (a : ℕ) := prior a/smoothMarkProbability O O a
  let loss (t : Ω) := ∑ a∈Y t,wt a
  have marks (a) (ha : a∈X) : a∈(construct n ell 0 0 0 0).marks := by
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp hc).2
  have cop (a : ℕ) (_ : a∈X) : (O.prefactor a false).Coprime (O.prefactor a true) :=
    (O.prefactors_coprime_iff O ((by decide : 3≤130000).trans deg) target a).mpr (by simp [O,PrescribedRows.unrestricted,PrescribedRows.hit])
  have pn (a) : 0≤prior a := constructor_mixture_prior_nonneg n ell mix pos a
  have wn (a) : 0≤wt a := div_nonneg (pn a) (mul_nonneg (O.probability_unit target false _).1 (O.probability_unit target true _).1)
  have ln (t) : 0≤loss t := sum_nonneg (fun a _=>wn a)
  obtain ⟨μ,law,rate⟩ := lossLaw O O bl hn comp target absent X prior marks cop
  have priorBound := constructor_mixture_prior_mass_le n ell mix pos norm
  change (∑ a∈X,|prior a|)≤1 at priorBound
  have ee : exp (-4*(Fixed.z b:ℝ)^2)=e^4 := by rw [←exp_nat_mul];congr 1;ring
  rw [ee] at rate
  have tiny : μ/e^3 ≤ e := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact rate.trans ((mul_le_mul_of_nonneg_left priorBound (by positivity)).trans_eq (by ring))
  simp_rw [abs_of_nonneg (pn _)] at law
  simp only [←sum_filter] at law
  have raw : HasSum (fun t:Ω=>twoFieldWeight O O t*loss t) μ := law
  have both : HasSum (fun t:Ω=>twoFieldWeight O O t*(cost t+loss t/e^3)) (budget+μ/e^3) := by
    apply (ex.add (raw.div_const (e^3))).congr_fun
    intro t;ring
  have fits : budget+μ/e^3+(256/(Fixed.d b:ℝ)+4*e+1/(Fixed.B b:ℝ))<1 := by linarith only [fit,tiny]
  obtain ⟨t,good,small⟩ := chooseDraw n old ell target comp absent mix pos norm
    (fun t=>cost t+loss t/e^3) _ (fun t=>add_nonneg (nonneg t) (div_nonneg (ln t) (by positivity))) both fits
  have cheap : cost t<1 := (le_add_of_nonneg_right (div_nonneg (ln t) (by positivity))).trans_lt small
  have lost : loss t<e^3 := (div_lt_one (by positivity)).mp ((le_add_of_nonneg_left (nonneg t)).trans_lt small)
  let x := t.1.val; let y := t.2.val
  let s := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
  let rows := s.rows.toFinset.filter (fun i=>i.q≠ell)
  have prime (i) (hi : i∈rows) : i.q.Prime :=
    (Marking.mem_base.mp (Marking.mem_rows.mp (List.mem_toFinset.mp (mem_filter.mp hi).1)).1).2.1
  have peel := peel_lost_mark_columns s rows (filter_subset ..) (Y t) mass scale wt b e
    (fun a _=>wn a) (fun i hi=>unit i (prime i hi)) (by
      intro a ha
      obtain ⟨ax,sm,sm',bx,by',_⟩ := mem_filter.mp ha
      have l := boxed_smooth_factor_bound O false hn deg comp target absent (marks a ax) t.1 bx sm
      have r := boxed_smooth_factor_bound O true hn deg comp target absent (marks a ax) t.2 by' sm'
      change Marking.value s.first a≠0 ∧ 4*(Marking.value s.first a).primeFactors.card≤b at l
      change Marking.value s.second a≠0 ∧ 4*(Marking.value s.second a).primeFactors.card≤b at r
      exact ⟨by intro side;cases side <;> first | exact l.1 | exact r.1,by omega⟩)
  refine ⟨t,good,cheap,lost,?_,peel.2⟩
  apply (le_of_mul_le_mul_left _ ep)
  apply peel.1.trans
  exact (mul_le_mul_of_nonneg_left lost.le (Nat.cast_nonneg b)).trans_eq (by ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.retained_denominator_rejection_peeling
