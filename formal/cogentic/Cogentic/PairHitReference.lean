import Cogentic.OrdinaryMass
import Cogentic.OrdinaryBranchNormalizer
import Cogentic.TargetBranchEnergy

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- Averaging the two-hit numerator under the two independent ordinary
residue masks gives precisely the positive model's raw Gram entry. Both
ordinary rows are prescribed on their actual fields before this averaging. -/
theorem ordinary_pair_hit_reference :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ∀ (i j : BandRow b)
    (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i) (hj : OrdinaryAdmissible (n:=n) (ell:=ell) j)
    (pq : bandRowPrime i≠bandRowPrime j),
    let p := bandRowPrime i; let q := bandRowPrime j
    let R := ordinaryPairPrescription i j hi hj pq
    ∀ (α : Bool→ℝ) (β : ℝ), (∀ k, 199/200≤α k) →
    (∀ k, InMarkSaddleRange n (saddleMean (primeBand b) (α k))) →
    let μ := fun p : ℕ=>(p:ℝ)^(-β)
    let w := fun a : BandRow b=>sqrt (μ (bandRowPrime a))
    let I := fun k (Q : ℕ)=>fullBandInsertion b Q (α k)/((Q:ℝ)*μ Q)
    let F := fun hp hq=>fullBandInsertion b ((R false).pairBranchProduct p q hp hq) (α false)*
      fullBandInsertion b ((R true).pairBranchProduct p q hp hq) (α true)
    (∑ hp : Bool,∑ hq : Bool,residueBranchMass (p:ℝ)⁻¹ hp*residueBranchMass (q:ℝ)⁻¹ hq*
      (if hp && hq then (w i*w j)⁻¹ else 0)*F hp hq)=
      ordinaryRawEntry bandRowPrime Prod.fst w I i j := by
  obtain ⟨b₀,empty⟩ := grid_empty_insertion
  refine ⟨b₀,?_⟩
  intro n ell b big i j hi hj pq p q R α β aa ma μ w I F
  have pm := i.2.1.property
  have qm := j.2.1.property
  have pp : (0:ℝ)<p := by exact_mod_cast (mem_primeBand.mp pm).1.pos
  have qp : (0:ℝ)<q := by exact_mod_cast (mem_primeBand.mp qm).1.pos
  have nz (k : Bool) : fullBandInsertion b 1 (α k)=1 := empty big (α k) (aa k) (ma k) p pm
  have vals (k : Bool) : (R k).pairBranchProduct p q true true =
      (if i.1=k then p else 1)*(if j.1=k then q else 1) := by
    change p≠q at pq
    cases si : i.1 <;> cases sj : j.1 <;> cases k <;>
      simp [R,ordinaryPairPrescription,PrescribedRows.pairBranchProduct,p,q,si,sj,pq,Ne.symm pq]
  have ww (a : BandRow b) : (w a)^2=μ (bandRowPrime a) := sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _)
  have wi : 0<w i := sqrt_pos.mpr (rpow_pos_of_pos pp _)
  have wj : 0<w j := sqrt_pos.mpr (rpow_pos_of_pos qp _)
  have mpair : μ (p*q)=(w i)^2*(w j)^2 := by
    rw [ww,ww];dsimp only [μ,p,q];rw [Nat.cast_mul,mul_rpow pp.le qp.le]
  have norm (k : Bool) : (p:ℝ)⁻¹*(q:ℝ)⁻¹*(w i*w j)⁻¹*fullBandInsertion b (p*q) (α k)=
      w i*w j*I k (p*q) := by
    dsimp only [I];rw [mpair,Nat.cast_mul];field_simp
  have splitNorm (k l : Bool) :
      (p:ℝ)⁻¹*(q:ℝ)⁻¹*(w i*w j)⁻¹*(fullBandInsertion b p (α k)*fullBandInsertion b q (α l))=
      (w i*I k p)*(w j*I l q) := by
    dsimp only [I];rw [show μ p=(w i)^2 from (ww i).symm,show μ q=(w j)^2 from (ww j).symm];field_simp
  simp only [Fintype.sum_bool,residueBranchMass,if_true,if_false,Bool.false_eq_true,Bool.true_and,
    Bool.and_true,Bool.false_and,Bool.and_false,zero_mul,mul_zero,zero_add,add_zero]
  dsimp only [ordinaryRawEntry,F]
  rw [if_neg pq,vals,vals]
  cases si : i.1 <;> cases sj : j.1 <;>
    simp only [si,sj,Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,one_mul,mul_one,nz]
  · exact norm false
  · exact splitNorm false true
  · rw [mul_comm (fullBandInsertion b q (α false))]
    exact splitNorm true false
  · exact norm true

/-- One ordinary row and one unused auxiliary prime. Taking `c = 1 / sqrt μ`
gives the normalized first moment, and `c = 1 / μ` gives the diagonal. -/
theorem ordinary_single_hit_reference :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ∀ (i : BandRow b) (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i)
    (q : ℕ), bandRowPrime i≠q →
    let p := bandRowPrime i; let R := singleOrdinaryPrescription (n:=n) (ell:=ell) i
    ∀ (α : Bool→ℝ) (β c : ℝ), (∀ k, 199/200≤α k) →
    (∀ k, InMarkSaddleRange n (saddleMean (primeBand b) (α k))) →
    let μ := (p:ℝ)^(-β)
    let I := fullBandInsertion b p (α i.1)/((p:ℝ)*μ)
    let F := fun hp hq=>fullBandInsertion b ((R false).pairBranchProduct p q hp hq) (α false)*
      fullBandInsertion b ((R true).pairBranchProduct p q hp hq) (α true)
    (∑ hp : Bool,∑ hq : Bool,residueBranchMass (p:ℝ)⁻¹ hp*residueBranchMass (q:ℝ)⁻¹ hq*
      (if hp then c else 0)*F hp hq)=c*μ*I := by
  obtain ⟨b₀,empty⟩ := grid_empty_insertion
  refine ⟨b₀,?_⟩
  intro n ell b big i hi q pq p R α β c aa ma μ I F
  have pp : (0:ℝ)<p := by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.pos
  have mp : 0<μ := rpow_pos_of_pos pp _
  have nz (k : Bool) : fullBandInsertion b 1 (α k)=1 := empty big (α k) (aa k) (ma k) p i.2.1.property
  have vals (k hq : Bool) : (R k).pairBranchProduct p q true hq=if i.1=k then p else 1 := by
    cases si : i.1 <;> cases k <;> cases hq <;>
      simp [R,singleOrdinaryPrescription,PrescribedRows.pairBranchProduct,p,si,hi,pq,Ne.symm pq,PrescribedRows.unrestricted]
  have fTrue (hq : Bool) : F true hq=fullBandInsertion b p (α i.1) := by
    dsimp only [F];rw [vals,vals]
    cases si : i.1 <;> simp only [Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,nz,one_mul,mul_one]
  simp only [Fintype.sum_bool,residueBranchMass,if_true,if_false,Bool.false_eq_true,mul_zero,zero_mul,
    add_zero,zero_add,fTrue]
  dsimp only [I];field_simp;ring

end
end Cogentic.Construction

#print axioms Cogentic.Construction.ordinary_pair_hit_reference
#print axioms Cogentic.Construction.ordinary_single_hit_reference
