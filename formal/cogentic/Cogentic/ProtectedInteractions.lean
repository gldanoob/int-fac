import Cogentic.ConstructorPriorDensity
import Cogentic.SmoothOverlapPeeling

namespace Cogentic.Construction
open Finset Real Window
noncomputable section
open scoped Classical

def OrdinaryAdmissible {n ell : ℕ} (i : BandRow (n.log2+1)) : Prop :=
  bandRowPrime i∈sieveBand n ell 1 ∧ bandRowPrime i≠ell ∧
    (i.2.2.val:ZMod (bandRowPrime i))≠Fixed.rootBase n

/-- One ordinary root is prescribed on its own field. -/
def singleOrdinaryPrescription {n ell : ℕ} (i : BandRow (n.log2+1)) (side : Bool) : PrescribedRows n ell :=
  if h : OrdinaryAdmissible (n:=n) (ell:=ell) i ∧ i.1=side then
    { primes := {bandRowPrime i}, residue := fun _=>i.2.2.val
      member := singleton_subset_iff.mpr h.1.1
      limit := by simp
      excluded := by simp [Ne.symm h.1.2.1]
      away := by intro q qm;obtain rfl := mem_singleton.mp qm;exact h.1.2.2 }
  else PrescribedRows.unrestricted n ell

theorem single_modulus {n ell : ℕ} (i : BandRow (n.log2+1)) (valid : OrdinaryAdmissible (n:=n) (ell:=ell) i) :
    prodPrimes (singleOrdinaryPrescription (n:=n) (ell:=ell) i false).primes *
    prodPrimes (singleOrdinaryPrescription (n:=n) (ell:=ell) i true).primes = bandRowPrime i := by
  cases color : i.1 <;> simp [singleOrdinaryPrescription,valid,color,prodPrimes,PrescribedRows.unrestricted]

/-- On a nonnegative integer tuple, admission of the single ordinary
prescription is exactly membership in the executable uncleaned row list. -/
theorem single_admission_listed {n ell : ℕ} (i : BandRow (n.log2+1)) (valid : OrdinaryAdmissible (n:=n) (ell:=ell) i)
    (hn : 2≤n) (big : 3≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (u v w z : ℕ) :
    let R := singleOrdinaryPrescription (n:=n) (ell:=ell) i false; let T := singleOrdinaryPrescription (n:=n) (ell:=ell) i true
    R.compatible false u v ∧ T.compatible true w z ↔
      Marking.Row.mk i.1 (bandRowPrime i) i.2.2.val∈(TryPair.fixedInput n ell (construct n ell u v w z)).rows := by
  intro R T
  have l := R.compatible_iff_listed hn big comp absent u v w z false
  have r := T.compatible_iff_listed hn big comp absent u v w z true
  simp at l r
  rw [l,r]
  cases color : i.1 <;> simp [R,T,singleOrdinaryPrescription,valid,color,PrescribedRows.unrestricted,Nat.mod_eq_of_lt i.2.2.isLt,bandRowPrime]

/-- The unrestricted coefficient expectation of the squared protected-to-
ordinary CRT errors, summed over all requested target rows and all admissible
ordinary candidates. Squared Gram normalization followed by the inverse
target mass leaves exactly q^(-alpha) on a candidate ordinary prime q. -/
theorem protected_interaction_error_budget (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (α u : ℝ), 0≤α → saddleMean (primeBand b) α=log (Fixed.B b)*u →
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    let X := constructorCellMarks n ell; let rows := (wanted (Fixed.d b) ell (Fixed.rootBase n)).toFinset
    let I := (univ : Finset (BandRow b)).filter (OrdinaryAdmissible (n:=n) (ell:=ell))
    let R := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i false
    let T := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i true
    let err := fun c r i (k : Ω)=>twoFieldScore (X c)
      (overlapContrast (R i) (T i) ell (bandRowPrime i) r i.2.2.val (fun _=>1))
      (fun a g=>(R i).compatible false g.1 g.2 ∧ smoothMarkEvent (R i) false a g)
      (fun a g=>(T i).compatible true g.1 g.2 ∧ smoothMarkEvent (T i) true a g) k.1.val k.2.val
    let cost := fun k : Ω=>∑ c,mix c*(∑ r∈rows,∑ i∈I,(bandRowPrime i:ℝ)^(-α)*(err c r i k/(X c).card)^2)
    ∃ μ : ℝ, HasSum (fun k : Ω=>twoFieldWeight O O k*cost k) μ ∧
      μ≤2048*u*(Fixed.d b:ℝ)*overlapError b K C 1 1 := by
  classical
  obtain ⟨C,cp,n₁,one⟩ := admitted_distinct_prime_overlap line K hK
  obtain ⟨n₂,counts⟩ := grid_cells_have_marks line
  obtain ⟨b₀,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max (max n₁ n₂) (max 2 (2^b₀)),?_⟩
  intro n large ell target comp absent b α u ap saddle mix hnMix norm O Ω X rows I R T err cost
  obtain ⟨fst,snd⟩ := max_le_iff.mp large
  obtain ⟨bone,bcount⟩ := max_le_iff.mp fst
  obtain ⟨hn,lim⟩ := max_le_iff.mp snd
  have deg := degrees b (((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _))
  have ep := (mem_dyadicTargets.mp target).1
  have ec := (Nat.coprime_mul_iff_right.mp (markModulus_spec hn deg comp target absent).2.2.1).2
  have ein : ell∈sieveBand n ell 1 := mem_filter.mpr ⟨dyadic_target_in_primeBand (Nat.succ_pos n.log2) target,
    ep.coprime_iff_not_dvd.mp ec.symm,ep.not_dvd_one⟩
  have B1 : 1<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  let M := (cellMarkCount b:ℝ)
  have Mp : 0<M := by dsimp [M,cellMarkCount];positivity
  have cells (c) : M≤8*((X c).card:ℝ) := by
    have c4 : 1≤(Fixed.B b)^4 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
    have den := counts n bcount ell target comp absent 1 0 0 0 0 0 c (by decide) c4
      (fun p hp dvd=>((Nat.prime_of_mem_primeFactors hp).not_dvd_one dvd).elim)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at den
    change M/8≤(X c).card at den
    linarith only [den]
  let U := overlapError b K C 1 1
  have Up : 0≤U := by dsimp [U,overlapError];positivity
  let m := fun i : BandRow b=>(bandRowPrime i:ℝ)^(-α)
  have mn (i) : 0 ≤ m i := rpow_nonneg (Nat.cast_nonneg _) _
  let Ev := fun c r i=>twoFieldSecond O O (X c)
    (overlapContrast (R i) (T i) ell (bandRowPrime i) r i.2.2.val (fun _=>1))
    (fun a g=>(R i).compatible false g.1 g.2 ∧ smoothMarkEvent (R i) false a g)
    (fun a g=>(T i).compatible true g.1 g.2 ∧ smoothMarkEvent (T i) true a g)
  let val := fun c r i=>m i*(Ev c r i/((X c).card:ℝ)^2)
  have law c r i : HasSum (fun k : Ω=>twoFieldWeight O O k*(m i*(err c r i k/(X c).card)^2)) (val c r i) := by
    have h := (twoField_score_second O O target (X c)
      (overlapContrast (R i) (T i) ell (bandRowPrime i) r i.2.2.val (fun _=>1))
      (fun a g=>(R i).compatible false g.1 g.2 ∧ smoothMarkEvent (R i) false a g)
      (fun a g=>(T i).compatible true g.1 g.2 ∧ smoothMarkEvent (T i) true a g)).mul_left (m i/((X c).card:ℝ)^2)
    have scaled : HasSum (fun k : Ω=>(m i/((X c).card:ℝ)^2)*(twoFieldWeight O O k*(err c r i k)^2)) (m i/((X c).card:ℝ)^2*Ev c r i) := h
    have eqv : m i/((X c).card:ℝ)^2*Ev c r i=val c r i := by dsimp only [val];ring
    rw [←eqv]
    apply scaled.congr_fun
    intro k
    rw [div_pow];ring
  have rate c r i (hi : i∈I) : val c r i ≤256*U*bandRowWeight α i := by
    have valid := (mem_filter.mp hi).2
    have pr : (0:ℝ)<bandRowPrime i := by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.pos
    have qid : (prodPrimes (R i).primes:ℝ)*(prodPrimes (T i).primes:ℝ)=(bandRowPrime i:ℝ) := by exact_mod_cast single_modulus i valid
    have est := one n bone ell target comp absent (R i) (T i) c ell (bandRowPrime i) r i.2.2.val ein valid.1 valid.2.1.symm
      (fun _=>1) 1 zero_le_one (by simp)
    simp only [meshVariation,sub_self,abs_zero,sum_const_zero,add_zero,abs_one,qid] at est
    change Ev c r i ≤ 4*(U*M^2)/(bandRowPrime i:ℝ) at est
    have cpos : 0<((X c).card:ℝ) := by have := cells c;linarith
    have sq := pow_le_pow_left₀ Mp.le (cells c) 2
    have rel : M^2≤64*((X c).card:ℝ)^2 := by nlinarith only [sq]
    have sm : Ev c r i/((X c).card:ℝ)^2≤256*U/(bandRowPrime i:ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos cpos)).mpr
      apply est.trans
      apply (div_le_iff₀ pr).mpr
      have eq : 256*U/(bandRowPrime i:ℝ)*((X c).card:ℝ)^2*(bandRowPrime i:ℝ) =
          256*U*((X c).card:ℝ)^2 := by field_simp
      rw [eq]
      linarith only [mul_le_mul_of_nonneg_left rel Up]
    exact (mul_le_mul_of_nonneg_left sm (mn i)).trans_eq (by dsimp [m,bandRowWeight];ring)
  let V := fun c=> ∑ r∈rows,∑ i∈I, val c r i
  have cellLaw c : HasSum (fun k : Ω=>twoFieldWeight O O k*(mix c*(∑ r∈rows,∑ i∈I,m i*(err c r i k/(X c).card)^2))) (mix c*V c) := by
    have h := (hasSum_sum (s:=rows) (fun r _=>hasSum_sum (s:=I) (fun i _=>law c r i))).mul_left (mix c)
    apply h.congr_fun;intro k
    simp only [mul_sum];apply sum_congr rfl;intro r _;apply sum_congr rfl;intro i _;ring
  have sum := hasSum_sum (s:=univ) (fun c _=>cellLaw c)
  refine ⟨∑ c,mix c*V c,by simpa only [cost,m,mul_sum] using sum,?_⟩
  have mass : (∑ i∈I,bandRowWeight α i)≤8*u := (sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun i _ _=>div_nonneg (mn i) (Nat.cast_nonneg _))).trans
    (band_row_weight_sum B1 ap saddle)
  have card : (rows.card:ℝ)≤Fixed.d b := by exact_mod_cast (List.toFinset_card_le _).trans_eq (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
  have each (c) : V c≤2048*u*(Fixed.d b:ℝ)*U := by
    have entry r := (sum_le_sum (s:=I) (fun i hi=>rate c r i hi)).trans_eq (mul_sum ..).symm
    have inner (r) := (entry r).trans (mul_le_mul_of_nonneg_left mass (by positivity : 0≤256*U))
    have agg := sum_le_sum (s:=rows) (fun r _=>inner r)
    rw [sum_const,nsmul_eq_mul] at agg
    have un : 0≤u := by
      have u0 : 0≤∑ i∈I,bandRowWeight α i := sum_nonneg (fun i _=>div_nonneg (mn i) (Nat.cast_nonneg _))
      linarith only [u0,mass]
    exact agg.trans ((mul_le_mul_of_nonneg_right card (by positivity : 0≤256*U*(8*u))).trans_eq (by ring))
  have global := sum_le_sum (s:=univ) (fun c _=>mul_le_mul_of_nonneg_left (each c) (hnMix c))
  rwa [←sum_mul,norm,one_mul] at global

end
end Cogentic.Construction
#print axioms Cogentic.Construction.protected_interaction_error_budget
