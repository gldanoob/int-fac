import Cogentic.MarkIntervals

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- The actual executable mark set in a fixed cell. -/
def constructorCellMarks (n ell : ℕ) (cell : Option (Bool × Fin (Fixed.d (n.log2+1)))) : Finset ℕ :=
  let b := n.log2+1
  let lo := firstCellMark b cell
  (Ico lo (lo+cellMarkCount b)).filter (fun a=>a∈(construct n ell 0 0 0 0).marks)

/-- Weights at repeated marks add before the second moment is taken. -/
def pooledMarkWeight {ι : Type*} (S : Finset ι) (Y : ι→Finset ℕ) (f : ι→ℕ→ℝ) (a : ℕ) : ℝ :=
  ∑ i∈S, if a∈Y i then f i a else 0

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

def meshMix (n ell : ℕ) (c : Option (Bool×Fin (Fixed.d (n.log2+1)))) : ℝ :=
  let X := constructorCellMarks n ell
  ((X c).card:ℝ)/(∑ k,((X k).card:ℝ))

/-- Weight cells by their eligible counts so that each occurrence of a mark
has the same weight in the physical prior and the pooled mesh observable. -/
theorem pooled_mesh_prior (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    let X := constructorCellMarks n ell
    let total := ∑ c,((X c).card:ℝ)
    let mix := fun c=>((X c).card:ℝ)/total
    let raw := (2*(Fixed.d b:ℝ)+1)*(cellMarkCount b:ℝ)
    raw/8≤total ∧ total≤raw ∧ (∀ c,0 ≤ mix c) ∧ (∑ c,mix c)=1 ∧
      ∀ f : ℕ→ℝ, (∑ a∈univ.biUnion X,constructorMixturePrior n ell mix a*f a) =
        (∑ c,∑ a∈X c,f a)/total := by
  obtain ⟨n₀,count⟩ := grid_cells_have_marks line
  refine ⟨n₀,?_⟩
  intro n big ell target comp absent b X total mix raw
  let C := Option (Bool×Fin (Fixed.d b))
  have cellCard : (Fintype.card C:ℝ)=2*(Fixed.d b:ℝ)+1 := by simp [C]
  let M := (cellMarkCount b:ℝ)
  have mp : 0<M := by dsimp [M,cellMarkCount];positivity
  have lo (c : C) : M/8≤((X c).card:ℝ) := by
    have count' := count n big ell target comp absent 1 0 0 0 0 0 c (by decide)
      (Nat.one_le_pow _ _ (Nat.pow_pos (by decide)))
      (fun p hp h=>((Nat.prime_of_mem_primeFactors hp).not_dvd_one h).elim)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at count'
    exact count'
  have hi (c : C) : ((X c).card:ℝ)≤M := by
    have sub := card_le_card (filter_subset (fun a=>a∈(construct n ell 0 0 0 0).marks)
      (Ico (firstCellMark b c) (firstCellMark b c+cellMarkCount b)))
    simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at sub
    change ((X c).card:ℝ)≤(cellMarkCount b:ℝ)
    exact Nat.cast_le.mpr sub
  have lower := sum_le_sum (s:=univ) (fun (c:C) _=>lo c)
  have upper := sum_le_sum (s:=univ) (fun (c:C) _=>hi c)
  simp only [sum_const,card_univ,nsmul_eq_mul,cellCard] at lower upper
  have fit : raw/8≤total := by simpa only [raw,mul_div_assoc,M,total] using lower
  have tp : 0<total := (by dsimp [raw];positivity : 0<raw/8).trans_le fit
  refine ⟨fit,upper,fun c=>div_nonneg (Nat.cast_nonneg _) tp.le,?_,?_⟩
  · simp only [mix,←sum_div];exact div_self tp.ne'
  · intro f
    rw [constructor_mixture_prior_sum,sum_div]
    apply sum_congr rfl
    intro c _
    have pos : 0<((X c).card:ℝ) := (by positivity : 0<M/8).trans_le (lo c)
    change ((X c).card:ℝ)/total*((∑ a∈X c,f a)/(X c).card)=(∑ a∈X c,f a)/total
    field_simp

end
end Cogentic.Construction

#print axioms Cogentic.Construction.pooled_mesh_prior
