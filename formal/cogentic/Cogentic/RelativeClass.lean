import Cogentic.ResidueNormalization
import Cogentic.CleanWindows

namespace Cogentic.Construction
open Real Cogentic.Window

private theorem combine_class_estimates (Z : ℂ) (A G F M ε C₁ C₂ y : ℝ)
    (a1 : 1 ≤ A) (fp : 0 < F) (mp : 0 < M) (ep : 0 ≤ ε) (c0 : 0 ≤ C₂)
    (disc : ‖Z-(A*G:ℝ)‖ ≤ C₂*y)
    (principal : |2*π*G/(F*M)-1| ≤ C₁*ε) (ch : y ≤ 2000*F*M*ε) :
    ‖(2*π:ℝ) • Z-(A*F*M:ℝ)‖ ≤ (C₁+4000*π*C₂)*(A*F*M)*ε := by
  have ap := zero_lt_one.trans_le a1
  have fm := mul_pos fp mp
  rw [←div_self fm.ne' (a:=F*M),←sub_div,abs_div,abs_of_pos fm] at principal
  have pr := (div_le_iff₀ fm).mp principal
  have cs := disc.trans (mul_le_mul_of_nonneg_left ch c0)
  have scale : ‖(2*π:ℝ) • (Z-(A*G:ℝ))‖ ≤ (2*π)*(C₂*(2000*F*M*ε)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left cs (by positivity)
  have sc : ‖((A*(2*π*G-F*M):ℝ):ℂ)‖ ≤ A*(C₁*ε*(F*M)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos ap]
    exact mul_le_mul_of_nonneg_left pr ap.le
  have charge := mul_le_mul_of_nonneg_right a1 (show 0 ≤ (2*π)*(C₂*(2000*F*M*ε)) by positivity)
  have add : (2*π:ℝ) • Z-(A*F*M:ℝ) =
      (2*π:ℝ) • (Z-(A*G:ℝ)) + ((A*(2*π*G-F*M):ℝ):ℂ) := by
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub]
    ring
  rw [add]
  exact (norm_add_le ..).trans ((add_le_add scale sc).trans (by linarith only [charge]))

/-- Relative mass of each actual reduced class on the constructed band.
The full-band reference can be shifted by the logs of two inserted primes. -/
theorem constructed_class_relative (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ {n ell forced q₀ q : ℕ} {Y S u : ℝ},
    let b := n.log2+1
    let H := log (Fixed.B b)
    let J := (sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)
    let D := primeBand b \ J
    b₀ ≤ b → 2 ≤ n → ¬n.Prime → ell ∈ dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n) = none →
    0 < forced → forced ≤ (Fixed.B b)^3 → 0 < q → q ∣ q₀ → 0 < q₀ → q₀ ≤ conductorCap n →
    InWindow b Y S → 90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → |H*u-log Y| ≤ 2*H →
    ∃ α ∈ Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=H*u ∧
      let F := Y^(α-1)*eulerMass J α
      let M := omittedMass (primeBand b) D (primeProbability α) (fun p => log p) H (H*u-log Y)
      let A := (q:ℝ)/q.totient
      0 < M ∧ ∀ r : (ZMod q)ˣ,
        ‖(2*π:ℝ) • ((q:ℂ)*classMass (squarefreeSupport J) (fun t => (gaussian Y S t:ℂ)) r) -
          (A*F*M:ℝ)‖ ≤ C*(A*F*M)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C₁,c₁,n₁,principal⟩ := fixed_relative_principal_mass line 3 K hK
  obtain ⟨n₂,ch⟩ := fixed_character_relative line 3 K hK
  obtain ⟨C₂,c₂,character⟩ := clean_window_discrepancy line
  obtain ⟨n₃,grow⟩ := Fixed.degree_grows 50000
  refine ⟨C₁+4000*π*C₂,by positivity,max n₁ (max n₂ n₃),?_⟩
  intro n ell forced q₀ q Y S u b H J D bs hn comp target absent pf fc pq div q₀p cap win ulo uhi shift
  obtain ⟨bp,hs⟩ := max_le_iff.mp bs
  obtain ⟨bc,bg⟩ := max_le_iff.mp hs
  have hd := grow b bg
  have bpos : 0 < b := Nat.succ_pos _
  have big : 10004 ≤ Fixed.d b := by omega
  have hlog := (fixed_band_log_bounds b bpos (by omega)).1
  have dr : 50000 ≤ (Fixed.d b:ℝ) := by exact_mod_cast hd
  have hp : 0 < H := by change 1000*(Fixed.d b:ℝ) ≤ H at hlog; linarith
  have qq := Nat.le_of_dvd q₀p div
  have om := omitted_card hn big comp target absent pf fc q₀p cap
  change D.card ≤ b^3 at om
  have sub : J ⊆ primeBand b := fun p h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have simpD : primeBand b \ D = J := Finset.sdiff_sdiff_eq_self sub
  have simpQ : J \ q.primeFactors = J := by
    ext p
    exact ⟨fun h => (Finset.mem_sdiff.mp h).1,fun h => Finset.mem_sdiff.mpr ⟨h,fun mem =>
      (Finset.mem_filter.mp h).2 ((Nat.mem_primeFactors.mp mem).2.1.trans div)⟩⟩
  have dsub : D ⊆ primeBand b := Finset.sdiff_subset
  have ly := (le_div_iff₀ hp).mp win.2.2.1
  have ly' : H*(80*(Fixed.d b:ℝ)) ≤ log Y := by nlinarith only [ly,mul_nonneg hp.le (Nat.cast_nonneg (α:=ℝ) (Fixed.d b))]
  have py := zero_lt_one.trans_le win.2.1
  simp only [Nat.floor_natCast] at principal ch
  obtain ⟨α,ha,mean,mp,first⟩ := principal b bp u Y S D ulo uhi ly' shift py win.1
    win.2.2.2.2.1 win.2.2.2.2.2.1 om dsub
  change |2*π*gaussianMass (primeBand b \ D) Y S/((Y^(α-1)*eulerMass (primeBand b \ D) α)*_)-1| ≤ _ at first
  have rest := ch b bc u α Y D ulo uhi ha.1 ha.2 mean om dsub win.2.1 ly' shift
  change Y^(-3/1000:ℝ) ≤ 2000*(Y^(α-1)*eulerMass (primeBand b \ D) α)*_*_ at rest
  rw [simpD] at first rest
  refine ⟨α,ha,mean,mp,fun r => ?_⟩
  have absErr := character hn big comp target absent pf fc pq qq cap win r
  change ‖(q:ℂ)*classMass (squarefreeSupport J) _ r-((q:ℂ)/q.totient)*(gaussianMass (J \ q.primeFactors) Y S:ℂ)‖ ≤ _ at absErr
  rw [simpQ] at absErr
  have qc : (1:ℝ) ≤ (q:ℝ)/q.totient :=
    (one_le_div (by exact_mod_cast Nat.totient_pos.mpr pq)).mpr (by exact_mod_cast Nat.totient_le q)
  apply combine_class_estimates _ _ _ _ _ _ _ _ _ qc (mul_pos (rpow_pos_of_pos py _) (eulerMass_pos _ _)) mp
    (exp_pos _).le c₂.le _ first rest
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] using absErr

end Cogentic.Construction
