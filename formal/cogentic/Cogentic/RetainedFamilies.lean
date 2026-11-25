import Cogentic.CoprimeFamilies
import Cogentic.SmoothDerivative
import Cogentic.SimpleMark

namespace Cogentic.Construction
open Finset Real Cogentic.Window

private theorem probability_cover {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (E F G : ℤ×ℤ→Prop) [DecidablePred E] [DecidablePred F] [DecidablePred G]
    (cover : ∀ k, E k → F k ∨ G k) :
    prescribedProbability R side E ≤ prescribedProbability R side F + prescribedProbability R side G := by
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let W (k : C) := coefficientWeight n k.val
  let Z := ∑' k, W k
  let V (A : ℤ×ℤ→Prop) [DecidablePred A] (k : C) := if A k.val then W k else 0
  have zp : 0<Z := (R.weight_normalizer target side).1
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have wn (k : C) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have vs (A : ℤ×ℤ→Prop) [DecidablePred A] : Summable (V A) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact wn k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact wn k | rfl) ws
  change (∑' k,V E k)/Z ≤ (∑' k,V F k)/Z+(∑' k,V G k)/Z
  rw [←add_div,div_le_div_iff_of_pos_right zp,←(vs F).tsum_add (vs G)]
  apply (vs E).tsum_le_tsum _ ((vs F).add (vs G))
  intro k
  by_cases e : E k.val <;> by_cases f : F k.val <;> by_cases g : G k.val <;>
    first | exact ((cover k.val e).elim f g).elim | simp [V,e,f,g,wn]

private theorem miss_factors {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) :
    (prodPrimes (R.miss a)).primeFactors=R.miss a :=
  Nat.primeFactors_prod (fun _ h => R.prime (mem_sdiff.mp h).1)

private theorem miss_coprime_prefactor {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (s : Bool) :
    (prodPrimes (R.miss a)).Coprime (R.prefactor a s) := by
  have nz := (R.subprod_bounds (s := R.miss a) sdiff_subset).1.ne'
  rw [←Nat.disjoint_primeFactors nz (R.pre_bounds target a s).1.ne',miss_factors,R.prefactor_primeFactors target]
  have dis : Disjoint (R.miss a) (R.hit a) := disjoint_left.mpr (fun p h hp => (mem_sdiff.mp h).2 hp)
  have out : ell∉R.miss a := fun h => R.excluded (mem_sdiff.mp h).1
  split <;> simp [dis,out]

private theorem supportedValue_mono {J K : Finset ℕ} (pr : ∀ p∈K, p.Prime) (sub : J⊆K) (z : ℤ)
    (ev : supportedValue J z) : supportedValue K z := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp ev
  obtain ⟨sf,fac⟩ := (mem_squarefreeSupport J (fun p h => pr p (sub h)) _).mp hv
  exact mem_image.mpr ⟨v,(mem_squarefreeSupport K pr _).mpr ⟨sf,fac.trans sub⟩,rfl⟩


/-- At a boxed point every ordinary factor avoids the slope modulus and
its residue is simple for the polynomial in this field. -/
def ordinaryRegular {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (a u v : ℕ) : Prop :=
  let inp := TryPair.fixedInput n ell (construct n ell u v u v)
  let val := Marking.value (inp.coeffs side) a
  let M := prodPrimes (R.miss a)
  val.Coprime M ∧ ∀ p∈val.primeFactors, p≠ell → ¬p∣M →
    ¬p∣(Marking.horner (a:ℤ) (inp.coeffs side)).2.natAbs

/-- The same coefficient tuple gives many coprime smooth pairs whose
ordinary factor primes have simple roots on both sides. -/
theorem many_regular_smooth_at_marks (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ X : Finset ℕ, X.Nonempty → (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    (∀ a∈X, (R.prefactor a false).Coprime (T.prefactor a true)) →
    ∃ (u v w z : ℕ) (Y : Finset ℕ), Y⊆X ∧ (X.card:ℝ)/(4*(Fixed.B b:ℝ)^2)≤Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧ 1≤u ∧ 1≤v ∧ 1≤w ∧ 1≤z ∧
      let inp := TryPair.fixedInput n ell (construct n ell u v w z)
      ∀ a∈Y, Marking.SquarefreeSmooth inp.base (Marking.value inp.first a) ∧
        Marking.SquarefreeSmooth inp.base (Marking.value inp.second a) ∧
        (Marking.value inp.first a).Coprime (Marking.value inp.second a) ∧
        ordinaryRegular R false a u v ∧ ordinaryRegular T true a w z := by
  classical
  obtain ⟨b₁,avoid⟩ := PrescribedRows.smooth_probability_avoid line 2
  obtain ⟨b₂,margin⟩ := PrescribedRows.smooth_probability_margin line
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ (max b₂ (max b₃ 1000)),?_⟩
  intro n ell R T b huge hn comp target absent X nonempty marks forced
  obtain ⟨one,rest⟩ := max_le_iff.mp huge
  obtain ⟨two,rest⟩ := max_le_iff.mp rest
  obtain ⟨three,big⟩ := max_le_iff.mp rest
  have large := degree b three
  let B : ℝ := Fixed.B b
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  apply many_coprime_of_selection R T hn large comp target absent X nonempty marks forced ordinaryRegular
  intro A non sub Q s other nz size cop
  let M := fun a => prodPrimes (Q.miss a)
  let m := fun a => other a*M a
  let J := fun a => sieveBand n ell (Q.prefactor a s)
  let event := fun a (x : ℤ×ℤ) => supportedValue (J a \ (m a).primeFactors) (Q.intercept a s x.1 x.2)
  let E := fun a (x : ℤ×ℤ) => event a x ∧ ¬boxedOrdinarySingular Q s a x
  have mp (a : ℕ) : 0<M a := (Q.subprod_bounds (s:=Q.miss a) sdiff_subset).1
  have mn (a : ℕ) (ha : a∈A) := Nat.mul_ne_zero (nz a ha) (mp a).ne'
  have mc (a : ℕ) (ha : a∈A) : (m a).Coprime (Q.prefactor a s) :=
    Nat.coprime_mul_iff_left.mpr ⟨cop a ha,miss_coprime_prefactor Q target a s⟩
  have lower (a : ℕ) (ha : a∈A) : 1/B ≤ prescribedProbability Q s (E a) := by
    have mark := marks a (sub ha)
    have fits : (m a).primeFactors.card≤b^2 := by
      dsimp only [m,M]
      rw [Nat.primeFactors_mul (nz a ha) (mp a).ne',miss_factors]
      have mc := (card_le_card (show Q.miss a⊆Q.primes from sdiff_subset)).trans Q.limit
      have h := (card_union_le _ _).trans (Nat.add_le_add (size a ha) mc)
      have bound : b+2≤b^2 := by nlinarith only [show 2≤b by omega,Nat.mul_le_mul_left b (show 2≤b by omega)]
      exact h.trans bound
    have keep := (avoid Q one hn comp target absent mark s (m a).primeFactors fits).2
    let full := fun x : ℤ×ℤ => supportedValue (J a) (Q.intercept a s x.1 x.2)
    let bad := fun x => full x ∧ boxedOrdinarySingular Q s a x
    have ok (x : ℤ×ℤ) (yes : event a x) : full x :=
      supportedValue_mono (fun p h => (mem_primeBand.mp (mem_filter.mp h).1).1) sdiff_subset _ yes
    have split := probability_cover Q target s (event a) (E a) bad (fun x hx => by
      by_cases singular : boxedOrdinarySingular Q s a x
      · exact Or.inr ⟨ok x hx,singular⟩
      · exact Or.inl ⟨hx,singular⟩)
    have deriv := Q.boxed_ordinary_singular_loss hn large comp target absent mark s (fun _ => True)
    simp only [true_and] at deriv
    change prescribedProbability Q s bad≤(1/16)*prescribedProbability Q s full at deriv
    change prescribedProbability Q s full/2 ≤ prescribedProbability Q s (event a) at keep
    have lb : 8/B≤prescribedProbability Q s full := margin Q two hn comp target absent mark s
    rw [show 8/B=8*(1/B) by ring] at lb
    linarith only [keep,split,deriv,lb,div_pos zero_lt_one bp]
  obtain ⟨x,ok,box,count⟩ := many_events_in_box Q target s A non E big lower
  obtain ⟨x₀,hx,x₁,hy⟩ := box
  let u := x.1.toNat; let v := x.2.toNat
  have uu : (u:ℤ)=x.1 := Int.toNat_of_nonneg x₀.le
  have vv : (v:ℤ)=x.2 := Int.toNat_of_nonneg x₁.le
  have ub : u≤2*b^2*Fixed.U b*Fixed.A b := by exact_mod_cast (uu.trans_le hx)
  have vb : v≤2*b^2*Fixed.U b := by exact_mod_cast (vv.trans_le hy)
  have cp : Q.compatible s u v := by rwa [uu,vv]
  refine ⟨u,v,A.filter (fun i => E i x),filter_subset ..,count,⟨ub,vb⟩,cp,
    (by dsimp [u];omega),(by dsimp [v];omega),?_⟩
  intro a h
  obtain ⟨ha,ev,notSingular⟩ := mem_filter.mp h
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp (marks a (sub ha))
  let inp := TryPair.fixedInput n ell (construct n ell u v u v)
  let value := Marking.value (inp.coeffs s) a
  have smooth := (Q.box_smooth_coprime_iff hn ((by decide : 10004≤130000).trans large) comp target absent
    cap grid ⟨ub,vb⟩ s cp (mn a ha) (mc a ha)).mp (by rw [uu,vv];exact ev)
  have factors := Nat.coprime_mul_iff_left.mp smooth.2
  refine ⟨smooth.1,factors.1,factors.2.symm,?_⟩
  intro p hp diff free deriv
  exact notSingular ⟨⟨x₀,hx,x₁,hy⟩,p,hp,diff,free,deriv⟩


/-- For every admissible family of marks with compatible forced factors,
one enumerated coefficient tuple retains at least its 1/(4B²) share in
the relation matrix actually returned by the first stage. -/
theorem many_retained_at_marks (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ X : Finset ℕ, X.Nonempty → (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    (∀ a∈X, (R.prefactor a false).Coprime (T.prefactor a true)) →
    ∃ (u v w z : ℕ) (Y : Finset ℕ) (rel : Marking.Relations),
      Y⊆X ∧ (X.card:ℝ)/(4*(Fixed.B b:ℝ)^2)≤Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧ 1≤u ∧ 1≤v ∧ 1≤w ∧ 1≤z ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel ∧
      ∀ a∈Y, a∈rel.marks := by
  obtain ⟨b₁,regular⟩ := many_regular_smooth_at_marks line
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ b₂,?_⟩
  intro n ell R T b huge hn comp target absent X nonempty marks forced
  obtain ⟨one,two⟩ := max_le_iff.mp huge
  have big := degree b two
  have hd : 3≤Fixed.d b := (by decide : 3≤130000).trans big
  obtain ⟨u,v,w,z,Y,sub,card,ub,vb,wb,zb,l,r,up,vp,wp,zp,points⟩ :=
    regular R T one hn comp target absent X nonempty marks forced
  have box := And.intro ub (And.intro vb (And.intro wb zb))
  obtain ⟨rel,stage⟩ := stageOne_succeeds hn big comp target absent box
  refine ⟨u,v,w,z,Y,rel,sub,card,ub,vb,wb,zb,l,r,up,vp,wp,zp,stage,?_⟩
  intro a ha
  obtain ⟨ls,rs,shared,lop,rop⟩ := points a ha
  have mark := (constructed_marks_iff n ell u v w z a).mpr
    ((constructed_marks_iff n ell 0 0 0 0 a).mp (marks a (sub ha)))
  apply retained_of_regular_smooth R T hn big comp target absent mark box l r stage ls rs shared
  intro side
  cases side
  · exact derivative_coprime_of_ordinary hd target u v w z a false _ ls lop.1 lop.2
  · exact derivative_coprime_of_ordinary hd target u v w z a true _ rs rop.1 rop.2

end Cogentic.Construction

#print axioms Cogentic.Construction.many_retained_at_marks
