import Cogentic.SelectedMinor
import Cogentic.TargetUnits
import Cogentic.ExponentBounds
import Cogentic.VerifiedCandidate
import Cogentic.FieldSpecialization
import Cogentic.ColumnAccuracy
import Cogentic.ConstructedFields

/-! Transfer of the exact finite and real rank conclusions to the executable candidate. -/

open NumberField Polynomial
open scoped Matrix BigOperators NumberField
namespace Cogentic
open Marking TwoThirdsSearch

/-- Helmert coordinates in the row and mark ordering of the executable. -/
noncomputable def bracketMarkMatrix (s : Input) (rel : Relations) (x : Bool → Fin s.degree → ℝ) :
    Matrix (Fin (2*s.degree-2)) (Fin rel.marks.length) ℝ :=
  fun i j => helmertCoordinate (Construction.markLogAt x (rel.marks.get j) s.A
    (decide (s.degree-1 ≤ i.val))) (i.val%(s.degree-1)+1)

theorem bracketMarkMatrix_eq_field {s : Input} (rel : Relations) (x : Bool → Fin s.degree → ℝ)
    {K₁ K₂ : Type*} [Field K₁] [Field K₂] (θ₁ : K₁) (θ₂ : K₂)
    (σ₁ : Fin s.degree → K₁ →+* ℝ) (σ₂ : Fin s.degree → K₂ →+* ℝ)
    (image₁ : ∀ i, x false i = σ₁ i θ₁ / s.A) (image₂ : ∀ i, x true i = σ₂ i θ₂ / s.A) :
    bracketMarkMatrix s rel x = pairedHelmertMatrix (concreteRowCode s.degree) *
      markLogs σ₁ σ₂ (fun j => (rel.marks.get j : K₁)-θ₁) (fun j => (rel.marks.get j : K₂)-θ₂) s.A := by
  ext i j
  let logs := markLogs σ₁ σ₂ (fun j : Fin rel.marks.length => (rel.marks.get j : K₁)-θ₁)
    (fun j => (rel.marks.get j : K₂)-θ₂) s.A
  change _ = (pairedHelmertMatrix (concreteRowCode s.degree) *ᵥ (fun k => logs k j)) i
  rw [pairedHelmertMatrix_apply]
  have left : (fun k => if h : k<s.degree then logs (Sum.inl ⟨k,h⟩) j else 0) =
      Construction.markLogAt x (rel.marks.get j) s.A false := by
    funext k
    by_cases h : k<s.degree
    · simp [h,logs,markLogs,Construction.markLogAt,image₁,← sub_div,abs_div]
    · simp [h,Construction.markLogAt]
  have right : (fun k => if h : k<s.degree then logs (Sum.inr ⟨k,h⟩) j else 0) =
      Construction.markLogAt x (rel.marks.get j) s.A true := by
    funext k
    by_cases h : k<s.degree
    · simp [h,logs,markLogs,Construction.markLogAt,image₂,← sub_div,abs_div]
    · simp [h,Construction.markLogAt]
  rw [left,right]
  exact (concreteRowCode_elim s.degree (fun side => helmertCoordinate
    (Construction.markLogAt x (rel.marks.get j) s.A side)) i).symm

private theorem clear_class_coordinates {L ι : Type*} [AddCommGroup L] [Module ℤ L] [Fintype ι]
    (basis : Module.Basis ι ℤ L) (t : L) (v : ι → L) (x : ι → ℚ)
    (sol : ∀ i, (basis.repr t i:ℚ)+∑ j, (basis.repr (v j) i:ℚ)*x j=0) :
    let m := Finset.univ.lcm (fun i => (x i).den)
    0 < m ∧ ∃ c, latticeRelation (m:ℤ) t c v := by
  intro m
  obtain ⟨positive,c,_,eq⟩ := Reconstruction.clear_linear_system _ _ x sol
  refine ⟨positive,c,?_⟩
  unfold latticeRelation
  apply basis.equivFun.injective
  ext i
  simpa [Module.Basis.equivFun_apply,mul_comm,m] using eq i

set_option maxHeartbeats 900000 in
private theorem candidate_of_fields {K₁ K₂ : Type} [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [IsTotallyReal K₁] [IsTotallyReal K₂] {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 300 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell a b c d)
    ∀ {rel : Relations}, stageOne s = some rel →
    ∀ {out : Elimination.IntegerFamily rel.marks.length}, Elimination.stageTwo rel = some out →
    ∀ (p₁ : Fin s.degree ≃ InfinitePlace K₁) (p₂ : Fin s.degree ≃ InfinitePlace K₂) (θ₁ : K₁) (θ₂ : K₂),
    (polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0 →
    (polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0 →
    Construction.MarkRing K₁ N θ₁ s.m (fun j : Fin rel.marks.length => (rel.marks.get j:ℤ)) →
    Construction.MarkRing K₂ N θ₂ s.m (fun j : Fin rel.marks.length => (rel.marks.get j:ℤ)) →
    let M := pairedHelmertMatrix (concreteRowCode s.degree) *
      markLogs (orderedRealEmbeddings p₁) (orderedRealEmbeddings p₂)
        (fun j : Fin rel.marks.length => (rel.marks.get j : K₁)-θ₁)
        (fun j => (rel.marks.get j : K₂)-θ₂) s.A
    Submodule.span ℝ {y : Fin (2*s.degree-2) → ℝ | ∃ z : Fin rel.marks.length → ℤ,
      (∀ i, ∑ j, rel.matrix i j*z j=0) ∧ y=M *ᵥ (fun j => (z j:ℝ))} = ⊤ →
    ∀ cols, Concrete.markColumns s rel = some cols →
    (∀ j i, |((cols.get j).get i:ℝ)-M i j| ≤ (1/2:ℝ)^(TryPair.localBits s rel) ∧
      |M i j| ≤ 2*s.degree*((s.L₀:ℝ)+1)) →
    verify N ell (Concrete.candidate N ell a b c d) ≠ none := by
  classical
  intro s rel marked out solved p₁ p₂ θ₁ θ₂ r₁ r₂ D E M span cols columns colBound
  let n := 2*s.degree-2
  let P := TryPair.localBits s rel
  let Q := TryPair.denominatorCap s rel
  let basis := concreteUnitBasis p₁ p₂
  let σ₁ := orderedRealEmbeddings p₁
  let σ₂ := orderedRealEmbeddings p₂
  let H := pairedHelmertMatrix (concreteRowCode s.degree)
  let obs := observeUnitPair σ₁ σ₂ H
  obtain ⟨guard,idx,sub,len,u,v,hu,hv,nz,vobs⟩ := computed_sorted_unit_minor marked solved p₁ p₂ θ₁ θ₂ r₁ r₂ span
  let sel := (Vector.ofFn idx.get).cast len
  let w := fun j : Fin n => out.directions.get (sel.get j)
  let cls := fun j => (unitClass (u j),unitClass (v j))
  obtain ⟨t₁,t₂,ht₁,ht₂,tobs⟩ := constructed_target_observation (by omega) target marked solved θ₁ θ₂
    σ₁ σ₂ (concreteRowCode s.degree) r₁ r₂
  let t := (unitClass t₁,unitClass t₂)
  let rhs := Concrete.observation cols out.particular P
  let Z := Concrete.minorMatrix (out.directions.map (fun z => Concrete.observation cols z P)) sel
  let den := (2:ℝ)^P
  let C := den⁻¹ • Z.map (Rat.castHom ℝ)
  let S := fun i : Fin n => -((rhs.get i:ℝ)/den)
  have cij (i j : Fin n) : C i j = ((Concrete.observation cols (w j) P).get i:ℝ)/den := by
    simp [C,Z,w,Concrete.minorMatrix,Vector.get_eq_getElem,div_eq_inv_mul,sel]
  have estimates (z : Vector ℤ rel.marks.length) (hz : z=out.particular ∨ ∃j, z=out.directions.get j) (i : Fin n) :=
    ArchPrecision.retained_observation (s:=s) solved (ArchPrecision.fixed_envelope marked big)
      cols i z hz (M i) (fun j => (colBound j i).2) (fun j => (colBound j i).1)
  have dir (i j : Fin n) : obs (cls j) i = ∑ k, ((w j).get k:ℝ)*M i k := by
    simpa only [M,Matrix.mulVec,dotProduct,mul_comm] using congrFun (vobs j) i
  have part (i : Fin n) : obs t i = ∑ k, (out.particular.get k:ℝ)*M i k := by
    have teq : obs t = M *ᵥ (fun j => (out.particular.get j:ℝ)) := tobs
    rw [teq]
    simp only [Matrix.mulVec,dotProduct,mul_comm]
  obtain ⟨cn,recover⟩ := ArchPrecision.fixed_selected_reconstruction marked big p₁ p₂ (concreteRowCode s.degree)
    basis cls t nz C S (fun i j => by
      change |obs (cls j) i| ≤ _
      rw [dir]; exact (estimates (w j) (.inr ⟨_,rfl⟩) i).1)
    (fun i j => by
      change |C i j-obs (cls j) i| ≤ _
      rw [dir,cij]; exact (estimates (w j) (.inr ⟨_,rfl⟩) i).2.1)
    (fun i => by
      change |-((rhs.get i:ℝ)/den)+obs t i| ≤ _
      rw [part,neg_add_eq_sub,abs_sub_comm]; exact (estimates _ (.inl rfl) i).2.1)
    (fun i => by
      change |-((rhs.get i:ℝ)/den)| ≤ _
      rw [abs_neg]; exact (estimates _ (.inl rfl) i).2.2)
  have zn : Z.det ≠ 0 := by
    intro zero
    apply cn
    rw [show C = den⁻¹ • Z.map (Rat.castHom ℝ) by rfl, Matrix.det_smul]
    have dz : (Z.map (Rat.castHom ℝ)).det = (Z.det:ℝ) := (Rat.cast_det Z).symm
    rw [dz,zero,Rat.cast_zero,mul_zero]
  apply Concrete.candidate_of_minor marked solved guard columns idx sub len zn
  intro y hy
  have cy : C *ᵥ (fun j => (y j:ℝ)) = S := by
    rw [show C = den⁻¹ • Z.map (Rat.castHom ℝ) by rfl,Matrix.smul_mulVec]
    funext i
    change den⁻¹*((Z.map (Rat.castHom ℝ)) *ᵥ ((Rat.castHom ℝ) ∘ y)) i = _
    rw [← RingHom.map_mulVec,show Z *ᵥ y = fun j => -(rhs.get j:ℚ) from hy]
    simp [S,div_eq_inv_mul]
  obtain ⟨x,unitEq,_,_,reconstructed,cap⟩ := recover y cy
  let m := Finset.univ.lcm (fun i => (x i).den)
  obtain ⟨positive,coeff,hc⟩ := clear_class_coordinates basis t cls x unitEq
  have dp : 0 < s.degree := by change 0 < Fixed.d (N.log2+1); omega
  obtain ⟨epos,kill⟩ := Construction.MarkRing.order_from_affine_classes D E (σ₁ ⟨0,dp⟩) (σ₂ ⟨0,dp⟩)
    ell out.scale (Elimination.stageTwo_verified solved).1 out.particular.get (fun j => (w j).get)
    t₁ t₂ u v (by simpa only [Int.cast_natCast] using ht₁) (by simpa only [Int.cast_natCast] using ht₂)
    (by simpa only [Int.cast_natCast] using hu) (by simpa only [Int.cast_natCast] using hv) m coeff hc positive
  let : NeZero N := ⟨by omega⟩
  have modOne : ModularPower.powMod ell (2*(out.scale*m)) N = 1 := by
    have h := congrArg ZMod.val kill
    rw [ModularPower.powMod_def]
    simpa only [← Nat.cast_pow,ZMod.val_natCast,ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (by omega : 1<N)] using h
  rw [reconstructedProposal,reconstructed]
  change verify N ell (if 2*(out.scale*m) ≤ 2^_ then some (.exponent (2*(out.scale*m))) else none) ≠ none
  rw [if_pos (fixed_exponent_fits marked solved big m cap)]
  exact verify_exponent ⟨by omega,dvd_mul_right _ _,modOne⟩

/-- The finite target equation and real span for the retained mark matrix are
sufficient for an actual verified candidate at this perturbation tuple. -/
theorem candidate_of_concrete_spans {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 130000 ≤ Fixed.d (N.log2+1)) (composite : ¬N.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1)))
    (sieved : presieve N (N.log2+1) (Fixed.beta (N.log2+1)) (Fixed.A (N.log2+1))
      (Fixed.rootBase N) = none)
    (box : let bits := N.log2+1
      a ≤ 2*bits^2*Fixed.U bits*Fixed.A bits ∧ b ≤ 2*bits^2*Fixed.U bits ∧
      c ≤ 2*bits^2*Fixed.U bits*Fixed.A bits ∧ d ≤ 2*bits^2*Fixed.U bits) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell a b c d)
    (∀ rel, stageOne s = some rel →
      (∃ t : Fin rel.marks.length → ℚ, ∀ i, ∑ j, (rel.matrix i j:ℚ)*t j = -(rel.rhs i:ℚ)) ∧
      ∃ x : Bool → Fin s.degree → ℝ, (∀ side i, x side i ∈
        Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
        RootLogs.normalized s.A (s.coeffs side) (x side i) = 0) ∧
      Submodule.span ℝ {y : Fin (2*s.degree-2) → ℝ | ∃ z : Fin rel.marks.length → ℤ,
        (∀ i, ∑ j, rel.matrix i j*z j = 0) ∧ y = bracketMarkMatrix s rel x *ᵥ
          (fun j => (z j:ℝ))} = ⊤) →
    verify N ell (Concrete.candidate N ell a b c d) ≠ none := by
  classical
  intro s premises
  obtain ⟨rel,marked⟩ := Construction.stageOne_succeeds hn big composite target sieved box
  obtain ⟨feasible,x,roots,span⟩ := premises rel marked
  have someOut : ∃ out, Elimination.stageTwo rel = some out := by
    cases h : Elimination.stageTwo rel with
    | none => exact False.elim ((Elimination.stageTwo_inconsistent rel).mp h feasible)
    | some out => exact ⟨out,rfl⟩
  obtain ⟨out,solved⟩ := someOut
  let f₁ := Construction.fieldPolynomial s false
  let f₂ := Construction.fieldPolynomial s true
  obtain ⟨irr₁,real₁,places₁,root₁,images₁⟩ := Construction.constructed_field_places hn (by omega) target box false
  let : Fact (Irreducible f₁) := ⟨irr₁⟩
  let : IsTotallyReal (AdjoinRoot f₁) := real₁
  obtain ⟨irr₂,real₂,places₂,root₂,images₂⟩ := Construction.constructed_field_places hn (by omega) target box true
  let : Fact (Irreducible f₂) := ⟨irr₂⟩
  let : IsTotallyReal (AdjoinRoot f₂) := real₂
  let θ₁ := AdjoinRoot.root f₁
  let θ₂ := AdjoinRoot.root f₂
  have image₁ (i) : x false i = orderedRealEmbeddings places₁ i θ₁/s.A :=
    ((images₁ i).2 _ (roots false i).1).mp (roots false i).2
  have image₂ (i) : x true i = orderedRealEmbeddings places₂ i θ₂/s.A :=
    ((images₂ i).2 _ (roots true i).1).mp (roots true i).2
  have eq := bracketMarkMatrix_eq_field rel x θ₁ θ₂ (orderedRealEmbeddings places₁)
    (orderedRealEmbeddings places₂) image₁ image₂
  obtain ⟨x',cols,roots',columns,accuracy⟩ := Construction.constructed_column_accuracy hn (by omega) target box marked
  have same : x' = x := by
    funext side i
    cases side
    · exact (((images₁ i).2 _ (roots' false i).1).mp (roots' false i).2).trans (image₁ i).symm
    · exact (((images₂ i).2 _ (roots' true i).1).mp (roots' true i).2).trans (image₂ i).symm
  subst x'
  apply candidate_of_fields hn (by omega) target marked solved places₁ places₂ θ₁ θ₂ root₁ root₂
    (Construction.markedRing marked false) (Construction.markedRing marked true) (eq ▸ span) cols columns
  intro j i
  rw [← eq]
  exact accuracy j i

end Cogentic

#print axioms Cogentic.candidate_of_concrete_spans
