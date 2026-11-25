import Cogentic.RelativeClass
import Cogentic.ScalarAffine

namespace Cogentic.Construction
open Real Cogentic.Window

theorem scalar_reduced_exact {J : Finset ℕ} (prime : ∀ p ∈ J, p.Prime)
    (c s : ℤ) (hs : s ≠ 0) (Y S : ℝ) (sp : 0 < S) :
    let g := commonDivisor c s
    let q := s.natAbs/g
    let K := J.filter (fun p => ¬p ∣ s.natAbs)
    let r := scalarResidue c s
    let a := ZMod.unitOfCoprime (r/g) (TwoThirdsWindow.reduced_class_coprime r s.natAbs (Int.natAbs_pos.mpr hs))
    scalarMass J c s Y S = if g ∈ squarefreeSupport J then
      (q:ℂ)*classMass (squarefreeSupport K) (fun t => (gaussian (Y/g) (S/g) t:ℂ)) a else 0 := by
  let : NeZero s.natAbs := ⟨(Int.natAbs_pos.mpr hs).ne'⟩
  exact affine_gaussian_reduced J prime c s hs (scalarResidue c s) (ZMod.natCast_zmod_val _) Y S sp

/-- After removing the forced divisor and the class gcd, the signed
coefficient-lattice sum itself has a relative saddle estimate. -/
theorem scalar_progression_relative (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ {n ell pre : ℕ} (c s : ℤ) (Y S u : ℝ),
    let b := n.log2+1
    let H := log (Fixed.B b)
    let J := sieveBand n ell pre
    let band := J.filter (fun p => ¬p ∣ s.natAbs)
    let D := primeBand b \ band
    let g := commonDivisor c s
    let q := s.natAbs/g
    let y := Y/(pre*(g:ℝ))
    let t := S/(pre*(g:ℝ))
    b₀ ≤ b → 2 ≤ n → ¬n.Prime → ell ∈ dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n) = none →
    0 < pre → pre ≤ (Fixed.B b)^3 → s ≠ 0 → s.natAbs ≤ conductorCap n →
    0 < S → InWindow b y t → 90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → |H*u-log y| ≤ 2*H →
    (g ∉ squarefreeSupport J → scalarMass J c s (Y/pre) (S/pre) = 0) ∧
    (g ∈ squarefreeSupport J → ∃ α ∈ Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=H*u ∧
      let M := omittedMass (primeBand b) D (primeProbability α) (fun p => log p) H (H*u-log y)
      let model := ((q:ℝ)/q.totient)*(y^(α-1)*eulerMass band α)*M
      0 < model ∧ ‖(2*π:ℝ) • scalarMass J c s (Y/pre) (S/pre)-(model:ℂ)‖ ≤
        C*model*exp (-K*(Fixed.z b:ℝ)^2)) := by
  obtain ⟨C,cp,b₀,progr⟩ := constructed_class_relative line K hK
  refine ⟨C,cp,b₀,?_⟩
  intro n ell pre c s Y S u b H J band D g q y t bs hn comp target sieved pp fc hs cap sp win ulo uhi shift
  have qp0 := Int.natAbs_pos.mpr hs
  have dvd : g ∣ s.natAbs := (gcd_dvd_intercept c s hs).2
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ qp0
  have qp : 0 < q := Nat.div_pos (Nat.le_of_dvd qp0 dvd) gp
  have qdvd : q ∣ s.natAbs := Nat.div_dvd_of_dvd dvd
  let a := ZMod.unitOfCoprime (scalarResidue c s/g) (TwoThirdsWindow.reduced_class_coprime _ _ qp0)
  have prime (p : ℕ) (mem : p∈J) := (mem_primeBand.mp (Finset.mem_filter.mp mem).1).1
  have exactMass := scalar_reduced_exact prime c s hs (Y/pre) (S/pre) (div_pos sp (by exact_mod_cast pp))
  change scalarMass J c s (Y/pre) (S/pre) = if g ∈ squarefreeSupport J then
    (q:ℂ)*classMass (squarefreeSupport band) (fun n => (gaussian (Y/pre/g) (S/pre/g) n:ℂ)) a else 0 at exactMass
  rw [div_div,div_div] at exactMass
  refine ⟨fun unsupported => exactMass.trans (if_neg unsupported),?_⟩
  intro supported
  obtain ⟨α,ha,mean,mp,bound⟩ := progr bs hn comp target sieved pp fc qp qdvd qp0 cap win ulo uhi shift
  have yp := zero_lt_one.trans_le win.2.1
  have ap : 0 < (q:ℝ)/q.totient := div_pos (by exact_mod_cast qp) (by exact_mod_cast Nat.totient_pos.mpr qp)
  refine ⟨α,ha,mean,mul_pos (mul_pos ap (mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _))) mp,?_⟩
  rw [exactMass,if_pos supported]
  exact bound a

end Cogentic.Construction
