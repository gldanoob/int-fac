import Cogentic.CleanWindows
import Cogentic.AffineMark

namespace Cogentic.Construction
open Cogentic.Window

/-- The integer representative of a signed affine progression. -/
def scalarResidue (c s : ℤ) : ℕ := ((c:ZMod s.natAbs)).val

def commonDivisor (c s : ℤ) : ℕ := (scalarResidue c s).gcd s.natAbs

/-- The signed discrete-Gaussian sum entering the scalar one-mark and two-mark laws. -/
noncomputable def scalarMass (J : Finset ℕ) (c s : ℤ) (Y S : ℝ) : ℂ :=
  ((s.natAbs:ℝ)/S * ∑' j : ℤ, if c+s*j ∈ (squarefreeSupport J).image (fun n : ℕ => (n:ℤ)) then
      coeffGaussian (c+s*j : ℤ) Y S else 0 : ℝ)

noncomputable def scalarPrincipal (J : Finset ℕ) (c s : ℤ) (Y S : ℝ) : ℂ :=
  let g := commonDivisor c s
  let q := s.natAbs/g
  let K := J.filter (fun p => ¬p ∣ s.natAbs)
  if g ∈ squarefreeSupport J then ((q:ℂ)/q.totient)*(gaussianMass (K \ q.primeFactors) (Y/g) (S/g):ℂ) else 0

theorem gcd_dvd_intercept (c s : ℤ) (hs : s ≠ 0) :
    commonDivisor c s ∣ c.natAbs ∧ commonDivisor c s ∣ s.natAbs := by
  let q := s.natAbs
  let r := scalarResidue c s
  let g := commonDivisor c s
  have qp : 0 < q := Int.natAbs_pos.mpr hs
  let : NeZero q := ⟨qp.ne'⟩
  have hc : (r:ZMod q) = c := ZMod.natCast_zmod_val _
  have dvdq : g ∣ q := Nat.gcd_dvd_right r q
  have dvdr : g ∣ r := Nat.gcd_dvd_left r q
  have delta : (q:ℤ) ∣ c-(r:ℤ) := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (by simpa using hc)
  have cg : (g:ℤ) ∣ c := by simpa using dvd_add ((Int.natCast_dvd_natCast.mpr dvdq).trans delta) (Int.natCast_dvd_natCast.mpr dvdr)
  exact ⟨Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr cg),dvdq⟩

/-- A supported class is measured after exact division by its common
    divisor. If that divisor fails the squarefree support test both terms
    vanish. This statement includes the full signed affine Gaussian sum. -/
theorem scalar_progression_discrepancy (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∀ {n ell pre : ℕ} (c s : ℤ) (Y S : ℝ),
      2≤n → 10004≤Fixed.d (n.log2+1) → ¬n.Prime → ell ∈ dyadicTargets (Fixed.beta (n.log2+1)) →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none →
      0<pre → pre≤(Fixed.B (n.log2+1))^3 → s≠0 → s.natAbs ≤ conductorCap n → 0<S →
      InWindow (n.log2+1) (Y/(pre*(commonDivisor c s:ℝ))) (S/(pre*(commonDivisor c s:ℝ))) →
      let J := sieveBand n ell pre
      ‖scalarMass J c s (Y/pre) (S/pre)-scalarPrincipal J c s (Y/pre) (S/pre)‖ ≤
      C*(Y/(pre*(commonDivisor c s:ℝ)))^(-3/1000:ℝ) := by
  obtain ⟨C,Cp,disc⟩ := clean_window_discrepancy line
  refine ⟨C,Cp,?_⟩
  intro n ell pre c s Y S hn big comp target none pp fp hs cap sp window
  let q := s.natAbs; let r := scalarResidue c s; let g := commonDivisor c s
  let J := sieveBand n ell pre
  let K := J.filter (fun p => ¬p ∣ q)
  have qp : 0<q := Int.natAbs_pos.mpr hs
  have gp : 0<g := Nat.gcd_pos_of_pos_right r qp
  have eff : 0<q/g := Nat.div_pos (Nat.le_of_dvd qp (Nat.gcd_dvd_right r q)) gp
  let : NeZero q := ⟨qp.ne'⟩
  have hc : (r:ZMod q) = c := ZMod.natCast_zmod_val _
  have prime (p : ℕ) (hp : p∈J) := (mem_primeBand.mp (Finset.mem_filter.mp hp).1).1
  have eq := affine_gaussian_reduced J prime c s hs r hc (Y/pre) (S/pre) (div_pos sp (by exact_mod_cast pp))
  let u := ZMod.unitOfCoprime (r/g) (TwoThirdsWindow.reduced_class_coprime r q qp)
  change scalarMass J c s (Y/pre) (S/pre) = if g ∈ squarefreeSupport J then ((q/g:ℕ):ℂ)*
    classMass (squarefreeSupport K) (fun t => (gaussian (Y/pre/g) (S/pre/g) t:ℂ)) u else 0 at eq
  change ‖scalarMass J c s (Y/pre) (S/pre)-scalarPrincipal J c s (Y/pre) (S/pre)‖ ≤ _
  rw [eq]
  unfold scalarPrincipal
  by_cases good : g ∈ squarefreeSupport J
  · rw [if_pos good,if_pos good,div_div,div_div]
    exact disc hn big comp target none pp fp eff (Nat.div_le_self q g) cap window u
  · rw [if_neg good,if_neg good,sub_self,norm_zero]
    exact mul_nonneg Cp.le (Real.rpow_nonneg (zero_lt_one.trans_le window.2.1).le _)

end Cogentic.Construction
