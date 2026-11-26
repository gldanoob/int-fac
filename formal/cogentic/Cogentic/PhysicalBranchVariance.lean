import Cogentic.PhysicalProfileVariance
import Cogentic.OrdinaryBranchMasks

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

private theorem sum_get_map (l : List α) (f : α→ℝ) :
    (∑ j : Fin l.length, f (l.get j))=(l.map f).sum := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum=_
  rw [←List.map_ofFn,List.ofFn_get]

private theorem meshVariation_scale (L M : ℕ) (c : ℝ) (f : ℕ→ℝ) :
    meshVariation L M (fun a=>c*f a)=|c| * meshVariation L M f := by
  simp only [meshVariation,←mul_sub,abs_mul,mul_add,mul_sum]

/-- Second moment of a physical score over the two ordinary hit/miss bits and
the protected target hit/miss bit. The signed raw mean uses the exact independent
CRT probabilities on every mesh point. The two unsigned error terms pay only
the total variations of the signed class expansions. -/
theorem physical_pair_branch_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C H : ℝ, 0<C ∧ 0<H ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ {p q : ℕ}, p∈sieveBand n ell 1 → q∈sieveBand n ell 1 → p≠q → p≠ell → q≠ell →
    ∀ r s : ℕ, let b := n.log2+1
    let Cell := Option (Bool×Fin (Fixed.d b)); let Bit := Bool×Bool×Bool
    let branch := fun a=>(decide (a ≡ r [MOD p]),decide (a ≡ s [MOD q]),hitsTarget n ell a false)
    let μ := fun (g : ℝ→Bool→ℝ) (h : Bit)=>g (p:ℝ)⁻¹ h.1*g (q:ℝ)⁻¹ h.2.1*g ((Fixed.d b:ℝ)/ell) h.2.2
    let X := univ.biUnion (constructorCellMarks n ell)
    ∃ α β : ℕ→ℝ, (∀ a∈X, saddleMean (primeBand b) (α a)=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      saddleMean (primeBand b) (β a)=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      α a∈Set.Icc (199/200:ℝ) 1 ∧ β a∈Set.Icc (199/200:ℝ) 1) ∧
    ∀ (R T : PrescribedRows n ell) (w : ℕ→ℝ) (f : Cell→Bit→ℕ→ℝ) (D : Cell→Bit→ℝ),
    (∀ c h, 0≤D c h ∧ ∀ a∈constructorCellMarks n ell c, |f c h a|≤D c h) →
    let J := fun a=>fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)
    (∀ a∈X, w a*J a=∑ c : Cell,if a∈constructorCellMarks n ell c then f c (branch a) a else 0) →
    let O := PrescribedRows.unrestricted n ell
    let L := firstCellMark b; let M := cellMarkCount b
    let A := ∑ c : Cell,∑ h : Bit, μ residueBranchEnvelope h*D c h
    let V := fun (g : Cell→Bit→ℕ→ℝ)=>∑ c : Cell,∑ h : Bit, μ residueBranchEnvelope h*meshVariation (L c) M (g c h)
    let δ := fun (m : ℝ→Bool→ℝ) (g : Cell→Bit→ℕ→ℝ)=>∑ c : Cell,∑ h : Bit, μ m h*∑ j∈range M,g c h (L c+j)
    let B := fun m g=>profileMomentBound b K C A (δ m g) (V g)
    twoFieldSecond R T X (fun a=>w a/smoothMarkProbability O O a) (smoothMarkEvent R false) (smoothMarkEvent T true) ≤
      2*B residueBranchMass f+2*(H*exp (-K*(Fixed.z b:ℝ)^2))^2*B residueBranchEnvelope (fun c h a=>|f c h a|) := by
  obtain ⟨C,H,cp,hp,n₁,physical⟩ := physical_profile_second line K hk
  obtain ⟨b₀,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨C,H,cp,hp,max n₁ (max 2 (2^b₀)),?_⟩
  intro n big ell target comp sieve p q pm qm pq pe qe r s b Cell Bit branch μ X
  obtain ⟨old,large⟩ := max_le_iff.mp big
  obtain ⟨hn,lg⟩ := max_le_iff.mp large
  have hd := degrees b (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  let roots := wanted (Fixed.d b) ell (Fixed.rootBase n)
  let masks := fun h : Bit=>ordinaryTargetBranchMasks p q ell r s roots h.1 h.2.1 h.2.2
  let I := (ch : Cell×Bit) × Fin (masks ch.2).length
  let t := fun i : I=>(masks i.1.2).get i.2
  let cells := fun i : I=>constructorCellMarks n ell i.1.1
  let Y := fun i : I=>(cells i).filter (fun a=>a ≡ (t i).residue [MOD (t i).modulus])
  have properties (h : Bit) := ordinary_target_branch_masks hn hd comp target sieve pm qm pq pe qe r s h.1 h.2.1 h.2.2
  have prop (i : I) := (properties i.1.2).2.1 _ (List.get_mem (masks i.1.2) i.2)
  have forms (a : ℕ) (c : Cell) (g : Bit→ℝ) :
      (∑ h : Bit,∑ j : Fin (masks h).length, (if a∈Y ⟨(c,h),j⟩ then (((masks h).get j).sign:ℝ)*g h else 0))=
        if a∈constructorCellMarks n ell c then g (branch a) else 0 := by
    have inner (h : Bit) (inside : a∈constructorCellMarks n ell c) :
        (∑ j : Fin (masks h).length, (if a∈Y ⟨(c,h),j⟩ then (((masks h).get j).sign:ℝ)*g h else 0)) =
          (if branch a=h then 1 else 0)*g h := by
      calc _ = (∑ j : Fin (masks h).length, ((masks h).get j).weight a)*g h := by
             rw [sum_mul]
             apply sum_congr rfl; intro j _
             simp only [Y,cells,t,mem_filter,inside,true_and,SignedResidueMask.weight,residueEntry]
             split_ifs <;> ring
           _ = _ := by
             rw [sum_get_map (masks h) (fun v=>v.weight a),(properties h).2.2 a]
             rcases h with ⟨h₁,h₂,h₃⟩
             simp only [branch,Prod.mk.injEq,and_assoc]
    by_cases inside : a∈constructorCellMarks n ell c
    · simp only [inner _ inside,if_pos inside,ite_mul,one_mul,zero_mul]
      exact Fintype.sum_ite_eq (branch a) g
    · simp [Y,cells,inside]
  have cover : univ.biUnion Y=X := by
    apply Subset.antisymm
    · intro a ha
      obtain ⟨i,_,hm⟩ := mem_biUnion.mp ha
      exact mem_biUnion.mpr ⟨i.1.1,mem_univ _,(mem_filter.mp hm).1⟩
    · intro a ha
      obtain ⟨c,_,ac⟩ := mem_biUnion.mp ha
      by_contra no
      have none (i : I) : a∉Y i := fun h=>no (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
      have eq := forms a c (fun _=>1)
      simp [none,ac] at eq
  obtain ⟨α,β,law,model⟩ := physical n old ell target comp sieve (univ : Finset I) (fun i=>i.1.1)
    (fun i=>(t i).modulus) (fun i=>(t i).residue) (fun i _=>prop i)
  refine ⟨α,β,fun a ha=>law a (cover ▸ ha),?_⟩
  intro R T w f D bd J obs O L M A V δ B
  let k := fun i : I=>maskMass false (t i)
  let g := fun (i : I) a=>k i*f i.1.1 i.1.2 a
  have mass (i : I) : |k i|=maskMass true (t i) := by
    simp [k,maskMass,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (t i).modulus)]
  have bounded (i : I) (hi : i∈(univ : Finset I)) :
      0≤|k i| * D i.1.1 i.1.2 ∧ ∀ a∈cells i, |g i a|≤|k i| * D i.1.1 i.1.2 := by
    refine ⟨mul_nonneg (abs_nonneg _) (bd _ _).1,fun a ha=>?_⟩
    dsimp only [g];rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((bd _ _).2 a ha) (abs_nonneg _)
  have eq (a) (ha : a∈univ.biUnion Y) :
      w a*J a=pooledMarkWeight univ Y (fun i a=>((t i).modulus:ℝ)*g i a) a := by
    have mag (i : I) : ((t i).modulus:ℝ)*g i a=((t i).sign:ℝ)*f i.1.1 i.1.2 a := by
      simp only [g,k,maskMass,Bool.false_eq_true,if_false]
      field_simp [(Nat.cast_pos.mpr (prop i).1 : (0:ℝ)<(t i).modulus).ne'] <;> ring
    rw [obs a (cover ▸ ha)]
    simp only [pooledMarkWeight,mag]
    rw [Fintype.sum_sigma,Fintype.sum_prod_type]
    apply sum_congr rfl;intro c _
    exact (forms a c (fun h=>f c h a)).symm
  have combine (z : Bool) (F : Cell→Bit→ℝ) :
      (∑ i : I, maskMass z (t i)*F i.1.1 i.1.2)=
        ∑ c : Cell,∑ h : Bit, μ (if z then residueBranchEnvelope else residueBranchMass) h*F c h := by
    rw [Fintype.sum_sigma,Fintype.sum_prod_type]
    apply sum_congr rfl;intro c _
    apply sum_congr rfl;intro h _
    change (∑ j : Fin (masks h).length, maskMass z ((masks h).get j)*F c h)=_
    rw [←sum_mul,sum_get_map (masks h) (maskMass z)]
    have m := branch_class_mass p q ell r s roots h.1 h.2.1 h.2.2 z
    have len : roots.length=Fixed.d b := (wanted_spec (target_gt_degree target) (Fixed.rootBase n)).1
    dsimp only at m
    rw [len] at m
    exact congrArg (fun x : ℝ=>x*F c h) m
  have compA := combine true D
  have rawMean (f : Cell→Bit→ℕ→ℝ) (z : Bool) :
      (∑ i : I,∑ j∈range M,maskMass z (t i)*f i.1.1 i.1.2 (L i.1.1+j)) =
        δ (if z then residueBranchEnvelope else residueBranchMass) f := by
    simp only [←mul_sum]
    exact combine z (fun c h=>∑ j∈range M,f c h (L c+j))
  have variation (g : Cell→Bit→ℕ→ℝ) (z : Bool) :
      (∑ i : I,meshVariation (L i.1.1) M (fun a=>maskMass z (t i)*g i.1.1 i.1.2 a))=V g := by
    simp only [meshVariation_scale]
    have ab (i : I) : |maskMass z (t i)|=maskMass true (t i) := by
      cases z <;> simp [maskMass,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (t i).modulus)]
    simp only [ab]
    exact combine true (fun c h=>meshVariation (L c) M (g c h))
  have bound := model R T w g (fun i=>|k i| * D i.1.1 i.1.2) bounded eq
  change twoFieldSecond R T (univ.biUnion Y) _ _ _ ≤ _ at bound
  rw [cover] at bound
  simp only [g,abs_mul,mass,k,compA] at bound
  let af := fun c h a=>|f c h a|
  rw [rawMean f false,rawMean af true,variation f false,variation af true] at bound
  exact bound

end
end Cogentic.Construction
#print axioms Cogentic.Construction.physical_pair_branch_second
