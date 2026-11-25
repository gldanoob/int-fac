import Cogentic.SharedPrimeLoss
import Cogentic.SmoothFamilies
import Cogentic.PolynomialRetained

namespace Cogentic.Construction
open Finset Real

theorem PrescribedRows.prefactor_primeFactors {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool) :
    (R.prefactor a side).primeFactors =
      if hitsTarget n ell a side then insert ell (R.hit a) else R.hit a := by
  let H := R.hit a
  have sub : H⊆R.primes := filter_subset ..
  have fac : (R.hitProduct a).primeFactors=H := Nat.primeFactors_prod (fun p hp => R.prime (sub hp))
  have prime := (mem_dyadicTargets.mp target).1
  have nz : R.hitProduct a≠0 := (R.subprod_bounds sub).1.ne'
  unfold PrescribedRows.prefactor targetPart
  split
  · rw [Nat.primeFactors_mul prime.ne_zero nz,prime.primeFactors,fac,singleton_union]
  · rw [one_mul,fac]

theorem PrescribedRows.prefactor_primeFactors_card_le_three {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool) :
    (R.prefactor a side).primeFactors.card≤3 := by
  have sub : R.hit a⊆R.primes := filter_subset ..
  have hc := (card_le_card sub).trans R.limit
  rw [R.prefactor_primeFactors target]
  split
  · exact (card_insert_le ..).trans (by omega)
  · omega

/-- The second field has no root at the target prime, so the two forced
prefactors are coprime exactly when their sets of prescribed hits are disjoint. -/
theorem PrescribedRows.prefactors_coprime_iff {n ell : ℕ} (R T : PrescribedRows n ell)
    (degree : 3≤Fixed.d (n.log2+1)) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) :
    (R.prefactor a false).Coprime (T.prefactor a true) ↔ Disjoint (R.hit a) (T.hit a) := by
  let : Fact ell.Prime := ⟨(mem_dyadicTargets.mp target).1⟩
  have cast (f : List ℤ) : ((eval (a:ℤ) f:ℤ):ZMod ell) =
      ((Marking.polynomial f).map (Int.castRingHom (ZMod ell))).eval (a:ZMod ell) := by
    induction f with
    | nil => simp [eval,Marking.polynomial]
    | cons c f ih => simp [eval,Marking.polynomial,ih]
  have noRoot := (target_roots degree target 0 0 0 0).2.2.2 (a:ZMod ell)
  have miss : hitsTarget n ell a true = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    have dvd : (ell:ℤ) ∣ eval (a:ℤ) (basePolynomial n ell true) := of_decide_eq_true hit
    exact noRoot ((cast _).symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr dvd))
  rw [←Nat.disjoint_primeFactors (R.pre_bounds target a false).1.ne' (T.pre_bounds target a true).1.ne',
    R.prefactor_primeFactors target,T.prefactor_primeFactors target,miss]
  have excluded : ell∉T.hit a := fun h => T.excluded (mem_filter.mp h).1
  by_cases hit : hitsTarget n ell a false <;> simp [hit,excluded]

/-- Select one coefficient pair per field in sequence. The second selection
can remove every prime divisor of the first value separately at each mark. -/
theorem many_coprime_of_selection {n ell : ℕ} (R T : PrescribedRows n ell) (hn : 2≤n)
    (large : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (X : Finset ℕ) (nonempty : X.Nonempty) (marks : ∀ a∈X, a∈(construct n ell 0 0 0 0).marks)
    (forced : ∀ a∈X, (R.prefactor a false).Coprime (T.prefactor a true))
    (good : PrescribedRows n ell→Bool→ℕ→ℕ→ℕ→Prop) :
    let b := n.log2+1; let B : ℝ := Fixed.B b
    (∀ (A : Finset ℕ), A.Nonempty → A⊆X → ∀ (Q : PrescribedRows n ell) (s : Bool) (other : ℕ→ℕ),
      (∀ a∈A, other a≠0) → (∀ a∈A, (other a).primeFactors.card≤b) →
      (∀ a∈A, (other a).Coprime (Q.prefactor a s)) →
      ∃ (u v : ℕ) (Y : Finset ℕ), Y⊆A ∧ (A.card:ℝ)/(2*B)≤Y.card ∧
        (u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) ∧ Q.compatible s u v ∧ 1≤u ∧ 1≤v ∧
        ∀ a∈Y, let inp := TryPair.fixedInput n ell (construct n ell u v u v)
          let val := Marking.value (inp.coeffs s) a
          Marking.SquarefreeSmooth inp.base val ∧ (other a).Coprime val ∧ good Q s a u v) →
    ∃ (u v w z : ℕ) (Y : Finset ℕ), Y⊆X ∧ (X.card:ℝ)/(4*B^2)≤Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧ 1≤u ∧ 1≤v ∧ 1≤w ∧ 1≤z ∧
      let inp := TryPair.fixedInput n ell (construct n ell u v w z)
      ∀ a∈Y, Marking.SquarefreeSmooth inp.base (Marking.value inp.first a) ∧
        Marking.SquarefreeSmooth inp.base (Marking.value inp.second a) ∧
        (Marking.value inp.first a).Coprime (Marking.value inp.second a) ∧
        good R false a u v ∧ good T true a w z := by
  intro b B select
  have bits : 3≤b := (by decide : 3≤130000).trans (large.trans (Fixed.degree_le_bits _))
  have bp : 0<B := by dsimp [B,Fixed.B]; positivity
  obtain ⟨u,v,S,subS,first,boxR,r,up,vp,lh⟩ := select X nonempty Subset.rfl R false
    (fun a => T.prefactor a true) (fun a _ => (T.pre_bounds target a true).1.ne')
    (fun a _ => (T.prefactor_primeFactors_card_le_three target a true).trans bits)
    (fun a ha => (forced a ha).symm)
  have spos : S.Nonempty := by
    have xp : (0:ℝ)<X.card := by exact_mod_cast card_pos.mpr nonempty
    have pos := (div_pos xp (show 0<2*B by positivity)).trans_le first
    exact card_pos.mp (by exact_mod_cast pos)
  let inp := TryPair.fixedInput n ell (construct n ell u v u v)
  let val := fun a => Marking.value inp.first a
  have size (a : ℕ) (ha : a∈S) : (val a).primeFactors.card≤b := by
    obtain ⟨amin,cap,_,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp (marks a (subS ha))
    have count := mark_sparsity hn large comp target absent amin cap
      (u:=u) (v:=v) (w:=u) (z:=v) ⟨boxR.1,boxR.2,boxR⟩ false (lh a ha).1
    change 4*(val a).primeFactors.card≤b at count
    omega
  obtain ⟨w,z,Y,subY,second,boxT,t,wp,zp,rh⟩ := select S spos subS T true val
    (fun a ha => (lh a ha).1.1) size (fun a ha => (lh a ha).2.1.symm)
  refine ⟨u,v,w,z,Y,subY.trans subS,?_,boxR.1,boxR.2,boxT.1,boxT.2,r,t,up,vp,wp,zp,
    fun a h => ⟨(lh a (subY h)).1,(rh a h).1,(rh a h).2.1,(lh a (subY h)).2.2,(rh a h).2.2⟩⟩
  refine le_trans ?_ ((div_le_div_of_nonneg_right first (by positivity : 0≤2*B)).trans second)
  change (X.card:ℝ)/(4*B^2) ≤ X.card/(2*B)/(2*B)
  rw [div_div,show (2*B)*(2*B)=4*B^2 by ring]

/-- One enumerated tuple gives squarefree smooth values with coprime
absolute values in both fields at a positive fraction of any eligible
family whose forced prefactors are relatively prime at each mark. -/
theorem many_coprime_smooth_at_marks (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ X : Finset ℕ, X.Nonempty → (∀ a∈X, a∈(construct n ell 0 0 0 0).marks) →
    (∀ a∈X, (R.prefactor a false).Coprime (T.prefactor a true)) →
    ∃ (u v w z : ℕ) (Y : Finset ℕ), Y ⊆ X ∧ (X.card:ℝ)/(4*(Fixed.B b:ℝ)^2) ≤ Y.card ∧
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b ∧
      R.compatible false u v ∧ T.compatible true w z ∧
      let inp := TryPair.fixedInput n ell (construct n ell u v w z)
      ∀ a∈Y, Marking.SquarefreeSmooth inp.base (Marking.value inp.first a) ∧
        Marking.SquarefreeSmooth inp.base (Marking.value inp.second a) ∧
        (Marking.value inp.first a).Coprime (Marking.value inp.second a) := by
  classical
  obtain ⟨b₁,avoid⟩ := PrescribedRows.smooth_probability_avoid line 1
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
  have select (A : Finset ℕ) (non : A.Nonempty) (sub : A⊆X) (Q : PrescribedRows n ell) (s : Bool)
      (other : ℕ→ℕ) (nz : ∀ a∈A, other a≠0) (size : ∀ a∈A, (other a).primeFactors.card≤b)
      (cop : ∀ a∈A, (other a).Coprime (Q.prefactor a s)) :
      ∃ (u v : ℕ) (Y : Finset ℕ), Y⊆A ∧ (A.card:ℝ)/(2*B)≤Y.card ∧
      (u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) ∧ Q.compatible s u v ∧ 1≤u ∧ 1≤v ∧
      ∀ a∈Y, let inp := TryPair.fixedInput n ell (construct n ell u v u v)
        let val := Marking.value (inp.coeffs s) a
        Marking.SquarefreeSmooth inp.base val ∧ (other a).Coprime val := by
    let J := fun a => sieveBand n ell (Q.prefactor a s)
    let E := fun a (x : ℤ×ℤ) => supportedValue (J a \ (other a).primeFactors) (Q.intercept a s x.1 x.2)
    have lower (a : ℕ) (ha : a∈A) : 1/B ≤ prescribedProbability Q s (E a) := by
      have mark := marks a (sub ha)
      have keep := (avoid Q one hn comp target absent mark s (other a).primeFactors
        (by simpa only [pow_one] using size a ha)).2
      let full := prescribedProbability Q s (fun x => supportedValue (J a) (Q.intercept a s x.1 x.2))
      have lb : 8/B≤full := margin Q two hn comp target absent mark s
      change full/2 ≤ prescribedProbability Q s (E a) at keep
      have positive : 0 < 1/B := div_pos zero_lt_one bp
      rw [show 8/B=8*(1/B) by ring] at lb
      linarith only [keep,lb,positive]
    obtain ⟨x,ok,box,count⟩ := many_events_in_box Q target s A non E big lower
    obtain ⟨x₀,hx,x₁,hy⟩ := box
    let u := x.1.toNat; let v := x.2.toNat
    have uu : (u:ℤ)=x.1 := Int.toNat_of_nonneg x₀.le
    have vv : (v:ℤ)=x.2 := Int.toNat_of_nonneg x₁.le
    have ub : u≤2*b^2*Fixed.U b*Fixed.A b := by exact_mod_cast (uu.trans_le hx)
    have vb : v≤2*b^2*Fixed.U b := by exact_mod_cast (vv.trans_le hy)
    have cp : Q.compatible s u v := by rwa [uu,vv]
    refine ⟨u,v,A.filter (fun i => E i x),filter_subset ..,count,⟨ub,vb⟩,cp,(by dsimp [u];omega),(by dsimp [v];omega),?_⟩
    intro a h
    obtain ⟨ha,ev⟩ := mem_filter.mp h
    obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp (marks a (sub ha))
    apply (Q.box_smooth_coprime_iff hn ((by decide : 10004≤130000).trans large) comp target absent
      cap grid ⟨ub,vb⟩ s cp (nz a ha) (cop a ha)).mp
    rw [uu,vv]; exact ev
  obtain ⟨u,v,w,z,Y,sub,count,boxR,boxR',boxT,boxT',r,t,_,_,_,_,ev⟩ :=
    many_coprime_of_selection R T hn large comp target absent X nonempty marks forced (fun _ _ _ _ _ => True)
      (fun A non sub Q s other nz size cop => by
        obtain ⟨u,v,Y,subY,low,box,cp,up,vp,hs⟩ := select A non sub Q s other nz size cop
        exact ⟨u,v,Y,subY,low,box,cp,up,vp,fun a ha => ⟨(hs a ha).1,(hs a ha).2,trivial⟩⟩)
  exact ⟨u,v,w,z,Y,sub,count,boxR,boxR',boxT,boxT',r,t,
    fun a h => ⟨(ev a h).1,(ev a h).2.1,(ev a h).2.2.1⟩⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.many_coprime_smooth_at_marks
