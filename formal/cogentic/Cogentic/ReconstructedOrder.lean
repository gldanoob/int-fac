import Cogentic.Extraction
import Cogentic.Reconstruction
import TwoThirdsSearch

namespace Cogentic
open NumberField
open scoped NumberField

local instance {K₁ K₂ : Type*} [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂] :
    Module ℤ (UnitClass K₁ × UnitClass K₂) := AddCommGroup.toIntModule (UnitClass K₁ × UnitClass K₂)

/-- Last step of TryPair. Its inputs contain the approximate rational solve,
    denominator and bit caps, and the target multiplicity. -/
def reconstructedProposal {ι : Type*} [Fintype ι] (approx : ι → ℚ) (Q e bits : ℕ) :
    Option TwoThirdsSearch.Proposal := do
  let m ← Reconstruction.multiplier approx Q
  if 2*(e*m) ≤ 2^bits then return .exponent (2*(e*m)) else none

/-- The true rational solution in the paired unit-class basis certifies
    exactly the exponent computed from the lcm of reconstructed denominators. -/
theorem reconstructed_order_hits {K₁ K₂ R₁ R₂ ι κ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [CommRing R₁] [CommRing R₂] [Fintype ι] [Fintype κ]
    (basis : Module.Basis κ ℤ (UnitClass K₁ × UnitClass K₂))
    (σ₁ : K₁ →+* ℝ) (σ₂ : K₂ →+* ℝ)
    (inc₁ : R₁ →+* K₁) (inc₂ : R₂ →+* K₂) (inj₁ : Function.Injective inc₁)
    (inj₂ : Function.Injective inc₂) {N : ℕ} (hn : 2 ≤ N) (eval₁ : R₁ →+* ZMod N) (eval₂ : R₂ →+* ZMod N)
    (ℓ e : ℕ) (he : 0 < e) (t₁ : R₁ˣ) (t₂ : R₂ˣ) (a₁ : ι → R₁ˣ) (a₂ : ι → R₂ˣ)
    (target_eval : eval₁ (t₁ : R₁) = eval₂ (t₂ : R₂))
    (neutral_eval : ∀ i, eval₁ (a₁ i : R₁) = eval₂ (a₂ i : R₂))
    (u₁ : (𝓞 K₁)ˣ) (u₂ : (𝓞 K₂)ˣ) (v₁ : ι → (𝓞 K₁)ˣ) (v₂ : ι → (𝓞 K₂)ˣ)
    (ut₁ : (u₁ : K₁) = ℓ^e * inc₁ (t₁ : R₁)) (ut₂ : (u₂ : K₂) = inc₂ (t₂ : R₂))
    (vr₁ : ∀ i, (v₁ i : K₁) = inc₁ (a₁ i : R₁)) (vr₂ : ∀ i, (v₂ i : K₂) = inc₂ (a₂ i : R₂))
    (approx x : ι → ℚ) (Q bits : ℕ) (small : ∀ i, (x i).den ≤ Q)
    (near : ∀ i, |approx i-x i| < 1/(2*(Q:ℚ)^2))
    (solves : ∀ j, ((basis.repr (unitClass u₁,unitClass u₂) j : ℤ):ℚ) +
      ∑ i, ((basis.repr (unitClass (v₁ i),unitClass (v₂ i)) j : ℤ):ℚ)*x i = 0)
    (fits : 2*(e*Finset.univ.lcm (fun i => (x i).den)) ≤ 2^bits) :
    TwoThirdsSearch.verify N ℓ (reconstructedProposal approx Q e bits) ≠ none := by
  classical
  let m := Finset.univ.lcm (fun i => (x i).den)
  obtain ⟨positive,c,_,eq⟩ := Reconstruction.clear_linear_system _ _ x solves
  have hc : latticeRelation (m:ℤ) (unitClass u₁,unitClass u₂) c
      (fun i => (unitClass (v₁ i),unitClass (v₂ i))) := by
    unfold latticeRelation
    apply basis.equivFun.injective
    ext j
    simpa [Module.Basis.equivFun_apply, mul_comm, m] using eq j
  obtain ⟨epos,kill⟩ := order_from_unit_class_relation σ₁ σ₂ inc₁ inc₂ inj₁ inj₂ eval₁ eval₂ ℓ e he t₁ t₂
    a₁ a₂ target_eval neutral_eval u₁ u₂ v₁ v₂ ut₁ ut₂ vr₁ vr₂ m c hc positive
  have : NeZero N := ⟨by omega⟩
  have modOne : ModularPower.powMod ℓ (2*(e*m)) N = 1 := by
    have h := congrArg ZMod.val kill
    rw [ModularPower.powMod_def]
    simpa only [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < N by omega)] using h
  rw [reconstructedProposal, Reconstruction.multiplier_exact approx x Q small near]
  change TwoThirdsSearch.verify N ℓ (if 2*(e*m) ≤ 2^bits then some (.exponent (2*(e*m))) else none) ≠ none
  rw [if_pos fits]
  exact TwoThirdsSearch.verify_exponent ⟨by omega, dvd_mul_right _ _, modOne⟩

end Cogentic
