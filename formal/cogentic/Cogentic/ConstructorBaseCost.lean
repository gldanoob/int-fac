import Cogentic.TargetBaseAssembly
import Cogentic.LocalCoeffsCost

namespace Cogentic.BinaryConstructorBase
open BinaryDivision BinaryPivot BinaryTargetBase Construction

/-- Generate the residue and target polynomials and return the two corrected
base lists. Only the fixed schedule and the current target are passed in. -/
def run (n d A m P ell leading mask : List Bool) : (List SignedWord × List SignedWord) × ℕ :=
  let l := BinaryLocalCoeffs.localWord d ell m leading false
  let r := BinaryLocalCoeffs.localWord d ell m leading true
  let pair := BinaryTargetBase.run n d A m P ell leading mask l.1 r.1
  (pair.1,l.2+r.2+pair.2+1)

theorem fixed_base {n ell : ℕ} (hn : 2 ≤ n) (big : 3 ≤ Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let b := n.log2+1
    let d := Fixed.d b
    let out := run n.bits d.bits (Fixed.A b).bits (Fixed.rootBase n).bits (primorial d).bits ell.bits
      (leadingCoefficient n).bits (binaryMask d).bits
    out.1=(((BinaryPerturbation.correctedBase n ell false).map encode),
      ((BinaryPerturbation.correctedBase n ell true).map encode)) ∧
      out.2 ≤ 2^(614044*TwoThirdsCost.scale b) := by
  intro b d out
  let S := TwoThirdsCost.scale b
  let m := Fixed.rootBase n
  let c := leadingCoefficient n
  let localResult (s : Bool) := BinaryLocalCoeffs.localWord d.bits ell.bits m.bits c.bits s
  have spec (s : Bool) := BinaryLocalCoeffs.fixed_localCoeffs hn target s
  obtain ⟨le,_,lc⟩ := spec false
  obtain ⟨re,_,rc⟩ := spec true
  change (localResult false).1=(localBase n ell false).map encode at le
  change (localResult true).1=(localBase n ell true).map encode at re
  change (localResult false).2 ≤ _ at lc
  change (localResult true).2 ≤ _ at rc
  obtain ⟨p,pc⟩ := fixed_corrected hn big comp target sieved (k:=1010) (fun s=>(spec s).2.1)
  rw [←le,←re] at p pc
  let pair := BinaryTargetBase.run n.bits d.bits (Fixed.A b).bits m.bits (primorial d).bits ell.bits c.bits
    (binaryMask d).bits (localResult false).1 (localResult true).1
  change pair.1=_ at p
  change pair.2 ≤ 2^(614042*S) at pc
  have sp : 0<S := (Nat.succ_pos _ : 0<Fixed.z b).trans_le ((Nat.le_mul_of_pos_left _
    (Fixed.degree_pos (Nat.succ_pos _))).trans ((Nat.le_mul_of_pos_left _
    (Fixed.degree_pos (Nat.succ_pos _))).trans (Fixed.scale_bounds (Nat.succ_pos _)).1))
  have more : 2^(5200*S) ≤ 2^(614042*S) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have xp := Nat.two_pow_pos (614042*S)
  have total := Nat.add_le_add (Nat.add_le_add (lc.trans more) (rc.trans more)) pc
  change pair.1=_ ∧ (localResult false).2+(localResult true).2+pair.2+1 ≤ _
  refine ⟨p,?_⟩
  calc _ ≤ 4*2^(614042*S) := by omega
       _ = 2^(2+614042*S) := by rw [pow_add]; rfl
       _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryConstructorBase

#print axioms Cogentic.BinaryConstructorBase.fixed_base
