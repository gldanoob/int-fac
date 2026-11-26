import Cogentic.RetainedCellSelection
import Cogentic.OrdinaryPeeling

namespace Cogentic.Construction
open Finset Real
noncomputable section
open scoped Classical

theorem hit_rows_count (s : Marking.Input) (rows : Finset Marking.Row) (sub : rows⊆s.rows.toFinset)
    (a : ℕ) (nz : ∀ side,Marking.value (s.coeffs side) a≠0) :
    (rows.filter (fun i=>a%i.q=i.r)).card ≤
      (Marking.value s.first a).primeFactors.card + (Marking.value s.second a).primeFactors.card := by
  let Z := ({false} ×ˢ (Marking.value s.first a).primeFactors) ∪ ({true} ×ˢ (Marking.value s.second a).primeFactors)
  have sends (i : Marking.Row) (hi : i∈rows.filter (fun i=>a%i.q=i.r)) : (i.second,i.q)∈Z := by
    obtain ⟨im,hit⟩ := mem_filter.mp hi
    obtain ⟨base,lt,root⟩ := Marking.mem_rows.mp (List.mem_toFinset.mp (sub im))
    have eqr : (a:ZMod i.q)=i.r := (ZMod.natCast_eq_natCast_iff ..).mpr (by
      change a%i.q=i.r%i.q;rw [Nat.mod_eq_of_lt lt];exact hit)
    have cast (f : List ℤ) : ((Marking.horner (a:ℤ) f).1:ZMod i.q)=(Marking.horner (a:ZMod i.q) f).1 := by
      induction f with
      | nil => simp [Marking.horner]
      | cons c cs ih => simp [Marking.horner,ih]
    have zero : (((Marking.horner (a:ℤ) (s.coeffs i.second)).1:ℤ):ZMod i.q)=0 := by
      rw [cast,eqr,Marking.horner_correct];exact root
    have dvd := Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp zero)
    have member : i.q∈(Marking.value (s.coeffs i.second) a).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨(Marking.mem_base.mp base).2.1,by simpa only [Marking.value,Int.natAbs_natCast] using dvd,nz _⟩
    cases side : i.second <;> simp_all [Z,Marking.Input.coeffs]
  have injection : Set.InjOn (fun i : Marking.Row=>(i.second,i.q)) ↑(rows.filter (fun i=>a%i.q=i.r)) := by
    rintro ⟨l,p,r⟩ hi ⟨l',p',r'⟩ hj eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have u := (mem_filter.mp hi).2;have v := (mem_filter.mp hj).2
    exact congrArg (Marking.Row.mk l p) (u.symm.trans v)
  exact (card_le_card_of_injOn _ sends injection).trans ((card_union_le ..).trans_eq (by simp))

/-- Diagonal loss and ordinary-row mass are reciprocal under the incidence
normalization. A single sparse removed column therefore charges only its
number of row hits. Thresholding those diagonals gives a simultaneous
quadratic-form bound on the remaining row coordinates. -/
theorem peel_lost_mark_columns (s : Marking.Input) (rows : Finset Marking.Row) (sub : rows⊆s.rows.toFinset)
    (Y : Finset ℕ) (mass scale : Marking.Row→ℝ) (weight : ℕ→ℝ) (k : ℕ) (δ : ℝ)
    (weights : ∀ a∈Y,0≤weight a) (unit : ∀ i∈rows,mass i*scale i^2=1)
    (sparse : ∀ a∈Y,(∀ side,Marking.value (s.coeffs side) a≠0) ∧
      (Marking.value s.first a).primeFactors.card + (Marking.value s.second a).primeFactors.card≤k) :
    let z := fun i : Marking.Row => fun a : ℕ => if a%i.q=i.r then scale i else 0
    let loss := fun i=>∑ a∈Y,weight a*(z i a)^2
    let bad := rows.filter (fun i=>δ≤loss i)
    δ*(∑ i∈bad,mass i) ≤ k*(∑ a∈Y,weight a) ∧
    ∀ v : Marking.Row→ℝ, (∑ a∈Y,weight a*(∑ i∈rows\bad,z i a*v i)^2) ≤
      (k:ℝ)*δ*(∑ i∈rows\bad,(v i)^2) := by
  classical
  intro z loss bad
  have mp (i) (hi : i∈rows) : 0 ≤ mass i := by
    by_contra! neg
    have := mul_nonpos_of_nonpos_of_nonneg neg.le (sq_nonneg (scale i))
    linarith only [this,unit i hi]
  have lp (i) : 0≤loss i := sum_nonneg fun a ha=>mul_nonneg (weights a ha) (sq_nonneg _)
  have hit (a) (ha : a∈Y) : (rows.filter (fun i=>a%i.q=i.r)).card≤k :=
    (hit_rows_count s rows sub a (sparse a ha).1).trans (sparse a ha).2
  have charge : (∑ i∈rows, mass i*loss i)≤k*(∑ a∈Y,weight a) := by
    dsimp only [loss]
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_le_sum
    intro a ha
    have calcHit : (∑ i∈rows,mass i*(weight a*z i a^2)) =
        (rows.filter (fun i=>a%i.q=i.r)).card*weight a := by
      rw [←nsmul_eq_mul,←sum_const,sum_filter]
      apply sum_congr rfl;intro i hi
      dsimp only [z]
      split
      · rw [mul_left_comm,mul_comm (mass i),mul_comm (scale i^2),unit i hi,mul_one]
      · ring
    rw [calcHit]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hit a ha) (weights a ha)
  constructor
  · rw [mul_sum]
    apply (sum_le_sum (fun i hi=>show δ*mass i ≤ mass i*loss i by
      rw [mul_comm];exact mul_le_mul_of_nonneg_left (mem_filter.mp hi).2 (mp i (mem_filter.mp hi).1))).trans
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i hi _=>mul_nonneg (mp i hi) (lp i))).trans charge
  · intro v
    let G := rows\bad
    let support := fun a=> (univ : Finset G).filter (fun i=>a%i.val.q=i.val.r)
    have bound (a) (ha : a∈Y) : (support a).card≤k := by
      apply (card_le_card_of_injOn (fun i : G=>i.val) (t := rows.filter (fun i=>a%i.q=i.r)) ?_ Subtype.val_injective.injOn).trans (hit a ha)
      intro i hi;exact mem_filter.mpr ⟨(mem_sdiff.mp i.property).1,(mem_filter.mp hi).2⟩
    let F := fun a : Y=> fun i : G=>z i.val a.val
    have energy := sparse_discard_energy (fun a : Y=>weight a.val) F (fun a : Y=>support a.val) (fun i : G=>v i.val)
      k δ (fun a=>weights _ a.property) (fun a=>bound _ a.property)
      (by intro a i away;dsimp only [F,z];exact if_neg fun eq=>away (mem_filter.mpr ⟨mem_univ _,eq⟩))
      (by
        intro i
        have hi := mem_sdiff.mp i.property
        have small : loss i.val < δ := lt_of_not_ge (fun h=>hi.2 (mem_filter.mpr ⟨hi.1,h⟩))
        change (∑ a : Y,weight a.val*(z i.val a.val)^2)≤δ
        rw [sum_coe_sort Y (fun a=>weight a*(z i.val a)^2)]
        exact small.le)
    have row (a : ℕ) : (∑ i : G,z i.val a*v i.val)=∑ i∈G,z i a*v i := sum_coe_sort G (fun i=>z i a*v i)
    simp only [F,row] at energy
    rw [sum_coe_sort Y (fun a=>weight a*(∑ i∈G,z i a*v i)^2),sum_coe_sort G (fun i=>(v i)^2)] at energy
    exact energy

theorem boxed_smooth_factor_bound {n ell a : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (x : R.CoeffPoint side) (box : inCoefficientBox n x.val)
    (smooth : smoothMarkEvent R side a x.val) :
    let m := boxedFieldValue n ell a side x.val
    m≠0 ∧ 4*m.primeFactors.card≤n.log2+1 := by
  let b := n.log2+1
  have uu := Int.toNat_of_nonneg box.1.le
  have vv := Int.toNat_of_nonneg box.2.2.1.le
  have bounds : x.val.1.toNat≤2*b^2*Fixed.U b*Fixed.A b ∧ x.val.2.toNat≤2*b^2*Fixed.U b :=
    ⟨by exact_mod_cast uu.trans_le box.2.1,by exact_mod_cast vv.trans_le box.2.2.2⟩
  have ok : R.compatible side x.val.1.toNat x.val.2.toNat := by rw [uu,vv];exact x.property
  obtain ⟨amin,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have law := R.box_smooth_iff hn (by omega) comp target absent cap grid bounds side ok
  rw [uu,vv] at law
  have sf := law.mp smooth
  exact ⟨sf.1,mark_sparsity hn big comp target absent amin cap ⟨bounds.1,bounds.2,bounds⟩ side sf⟩

/-- Work on one original coefficient draw, before prescribing any ordinary
row. The bad row set depends on the tuple. Its expected saddle mass is
exponentially small for each fixed threshold up to the displayed factors.
After these rows are dropped, the raw Gram loss on all remaining ordinary
coordinates obeys the simultaneous sparse energy bound. -/
theorem actual_rejection_peeling (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (X : Finset ℕ), (∀ a∈X,a∈(construct n ell 0 0 0 0).marks) →
    ∀ (prior : ℕ→ℝ) (mass scale : Marking.Row→ℝ), (∀ i,i.q.Prime → mass i*scale i^2=1) → ∀ δ : ℝ, 0<δ →
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    let input := fun k : Ω=>TryPair.fixedInput n ell
      (construct n ell k.1.val.1.toNat k.1.val.2.toNat k.2.val.1.toNat k.2.val.2.toNat)
    let rows := fun k=> (input k).rows.toFinset.filter (fun i=>i.q≠ell)
    let Y := fun k : Ω=> X.filter (fun a=>rejectedSmoothMark O O a k.1.val k.2.val)
    let wt := fun a=>|prior a|/smoothMarkProbability O O a
    let z := fun i : Marking.Row=>fun a : ℕ=>if a%i.q=i.r then scale i else 0
    let loss := fun k i=>∑ a∈Y k, wt a*(z i a)^2
    let bad := fun k=>(rows k).filter (fun i=>δ≤loss k i)
    (∑' k : Ω, twoFieldWeight O O k*(∑ i∈bad k,mass i))≤
      (b:ℝ)*exp (-K*(Fixed.z b:ℝ)^2)*(∑ a∈X, |prior a|)/δ ∧
    ∀ (k : Ω) (v : Marking.Row→ℝ),
      (∑ a∈Y k,wt a*(∑ i∈rows k\bad k,z i a*v i)^2)≤
        (b:ℝ)*δ*(∑ i∈rows k\bad k,(v i)^2) := by
  classical
  obtain ⟨b₁,lossLaw⟩ := rejected_score_loss line K hK
  obtain ⟨b₂,degrees⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b large hn comp target absent X marks prior mass scale unit δ dp O Ω input rows Y wt z loss bad
  obtain ⟨bg,bd⟩ := max_le_iff.mp large
  have deg := degrees b bd
  have wpos (a) : 0≤wt a := by
    have nonn side : 0 ≤ prescribedProbability O side (smoothMarkEvent O side a) := by
      rw [←(O.point_event side target (smoothMarkEvent O side a)).tsum_eq]
      exact tsum_nonneg (fun x=>by split <;> first | exact O.pointMass_nonneg side x | rfl)
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nonn false) (nonn true))
  have prime (k : Ω) (i) (hi : i∈rows k) : i.q.Prime :=
    (Marking.mem_base.mp (Marking.mem_rows.mp (List.mem_toFinset.mp (mem_filter.mp hi).1)).1).2.1
  have unitPos (k : Ω) (i) (hi : i∈rows k) : 0 ≤ mass i := by
    by_contra! neg;have bound := mul_nonpos_of_nonpos_of_nonneg neg.le (sq_nonneg (scale i))
    linarith only [bound,unit i (prime k i hi)]
  have peel (k : Ω) :
      δ*(∑ i∈bad k,mass i)≤b*(∑ a∈Y k,wt a) ∧
      ∀ v : Marking.Row→ℝ,(∑ a∈Y k,wt a*(∑ i∈rows k\bad k,z i a*v i)^2)≤
        (b:ℝ)*δ*(∑ i∈rows k\bad k,(v i)^2) := by
    apply peel_lost_mark_columns (input k) (rows k) (filter_subset ..) (Y k) mass scale wt b δ
      (fun a _=>wpos a) (fun i hi=>unit i (prime k i hi))
    intro a ha
    obtain ⟨inX,smoothL,smoothR,boxL,boxR,_⟩ := mem_filter.mp ha
    have l := boxed_smooth_factor_bound O false hn deg comp target absent (marks a inX) k.1 boxL smoothL
    have r := boxed_smooth_factor_bound O true hn deg comp target absent (marks a inX) k.2 boxR smoothR
    change Marking.value (input k).first a≠0 ∧ 4*(Marking.value (input k).first a).primeFactors.card≤b at l
    change Marking.value (input k).second a≠0 ∧ 4*(Marking.value (input k).second a).primeFactors.card≤b at r
    exact ⟨by intro side;cases side <;> first | exact l.1 | exact r.1,by omega⟩
  refine ⟨?_,fun k=>(peel k).2⟩
  have cop (a : ℕ) (_ : a∈X) : (O.prefactor a false).Coprime (O.prefactor a true) :=
    (O.prefactors_coprime_iff O ((by decide : 3≤130000).trans deg) target a).mpr (by simp [O,PrescribedRows.unrestricted,PrescribedRows.hit])
  obtain ⟨μ,law,rate⟩ := lossLaw O O bg hn comp target absent X prior marks cop
  simp only [←sum_filter] at law
  let F := fun k : Ω=>twoFieldWeight O O k*(∑ i∈bad k,mass i)
  let G := fun k : Ω=>twoFieldWeight O O k*(∑ a∈Y k,wt a)
  have hs : HasSum G μ := law
  have wp (k : Ω) : 0≤twoFieldWeight O O k := mul_nonneg (O.pointMass_nonneg false k.1) (O.pointMass_nonneg true k.2)
  have fp (k : Ω) : 0≤F k := mul_nonneg (wp k) (sum_nonneg (fun i hi=>unitPos k i (mem_filter.mp hi).1))
  have cmp (k : Ω) : F k≤((b:ℝ)/δ)*G k := by
    have p := (le_div_iff₀ dp).mpr ((by rw [mul_comm];exact (peel k).1) :
      (∑ i∈bad k,mass i)*δ≤b*(∑ a∈Y k,wt a))
    exact (mul_le_mul_of_nonneg_left p (wp k)).trans_eq (by dsimp only [G];ring)
  have upper := hs.mul_left ((b:ℝ)/δ)
  have total := (Summable.of_nonneg_of_le fp cmp upper.summable).tsum_le_tsum cmp upper.summable
  rw [upper.tsum_eq] at total
  exact total.trans ((mul_le_mul_of_nonneg_left rate (by positivity : 0≤(b:ℝ)/δ)).trans_eq (by ring))


end
end Cogentic.Construction

#print axioms Cogentic.Construction.actual_rejection_peeling
