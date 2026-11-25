import Cogentic.BadRowGcd
import Cogentic.PolynomialLattice

namespace Cogentic.Construction
open Marking

private theorem derivative_perturb {cs : List ℤ} (len : 3 ≤ cs.length) (A m u v a : ℕ) :
    (horner (a:ℤ) (perturb A m u v cs)).2 =
      (horner (a:ℤ) (perturb A m 0 0 cs)).2+
      (A:ℤ)*((u:ℤ)+a*v+((a:ℤ)-m)*v) := by
  rcases cs with _ | ⟨c,cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  rcases cs with _ | ⟨c',cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  rcases cs with _ | ⟨c'',cs⟩ <;> simp only [List.length_nil,List.length_cons] at len
  · omega
  simp only [perturb,horner,Int.cast_id,Nat.cast_zero,mul_zero,sub_zero,add_zero]
  ring

/-- Once the polynomial value at a mark is fixed, each ordinary prime
dividing it excludes exactly one residue of the free slope for simplicity. -/
theorem one_singular_slope {n ell a p : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (x : ℤ)
    (pp : p.Prime) (ordinary : p≠ell) (divp : p∣(affineValue n ell a side x).natAbs) :
    ∃ r : ZMod p, ∀ u v : ℕ, (u:ℤ)+a*v=x →
      let s := TryPair.fixedInput n ell (construct n ell u v u v)
      (p ∣ (horner (a:ℤ) (s.coeffs side)).2.natAbs ↔ (v:ZMod p)=r) := by
  let b := n.log2+1; let d := Fixed.d b; let A := Fixed.A b; let m := Fixed.rootBase n
  let P := primorial d
  let K := P*ell
  let f := corrected n m K (leadingCoefficient n) (preliminary d A m P ell (leadingCoefficient n) side)
  let F := (horner (a:ℤ) (perturb K m 0 0 f)).2
  let : Fact p.Prime := ⟨pp⟩
  have len : 3≤f.length := by simp [f,corrected,preliminary]; change 10004≤d at big; omega
  have gap := affine_fixed_coprime hn big comp target absent mark side x
  have clean : ¬p∣P*(m-a) := fun h => Nat.not_coprime_of_dvd_of_dvd pp.one_lt divp h gap
  have kp : ¬p∣K := by
    intro h
    rcases pp.dvd_mul.mp h with h|h
    · exact clean (dvd_mul_of_dvd_left h _)
    · exact ordinary ((Nat.prime_dvd_prime_iff_eq pp (mem_dyadicTargets.mp target).1).mp h)
  have am : a ≤ m := (mark_range hn big ((constructed_marks_iff ..).mp mark).2.1).le
  have kpz : (K:ZMod p)≠0 := fun h => kp ((ZMod.natCast_eq_zero_iff ..).mp h)
  have gapz : (a:ZMod p)-(m:ZMod p)≠0 := by
    intro h
    have e : ((m-a:ℕ):ZMod p)=0 := by rw [Nat.cast_sub am, (sub_eq_zero.mp h),sub_self]
    exact clean (dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff ..).mp e) _)
  let base : ZMod p := (F:ZMod p)+(K:ZMod p)*x
  let slope : ZMod p := (K:ZMod p)*((a:ZMod p)-m)
  have nz : slope≠0 := mul_ne_zero kpz gapz
  refine ⟨-base/slope,?_⟩
  intro u v fixed s
  have derivative : (horner (a:ℤ) (s.coeffs side)).2 = F+(K:ℤ)*(x+((a:ℤ)-m)*v) := by
    have eq := derivative_perturb len K m u v a
    rw [fixed] at eq
    cases side <;> exact eq
  rw [derivative]
  have iff : p ∣ (F+(K:ℤ)*(x+((a:ℤ)-m)*v)).natAbs ↔ base+slope*(v:ZMod p)=0 := by
    rw [←Int.natCast_dvd_natCast, Int.dvd_natAbs, ←ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp only [base,slope]; push_cast; constructor <;> intro z <;> linear_combination z
  rw [iff,eq_div_iff nz]
  constructor <;> intro z <;> linear_combination z

end Cogentic.Construction
