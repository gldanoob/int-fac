import Cogentic.RandomizedTaggedProbability
import Cogentic.RandomizedOddSplit
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped Polynomial

namespace Cogentic.RandomizedTaggedDependency

open Polynomial
open Cogentic.RandomizedKrylovProbe Cogentic.RandomizedPadeRecurrence

section BlindSolver

variable {K Row Col Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K]
  [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
  [DecidableEq K] [Fintype K]

/-- Compute the same recurrence as the tagged solver and permit the public
verifier to test every binary basis coordinate, without access to the tag. -/
def BlindTaggedSucceeds (M : Matrix Row Col (ZMod 2)) (split : (Col → ZMod 2) → Prop)
    (b : Module.Basis BasisIndex (ZMod 2) K) (d : Row → K) (e : Col → K)
    (x u : Col → K) : Prop :=
  let S := taggedOperator M d e
  let g := euclideanRecurrence (Fintype.card Col) (fun j => dotProbe u ((S ^ j) x))
  g.coeff 0 = 0 ∧ ∃ bit : BasisIndex,
    let v := (aeval S (g /ₘ X)) x
    let w := fun j => b.coord bit (v j)
    M.mulVec w = 0 ∧ split w

omit [DecidableEq K] in
/-- One public verification call for each binary basis coordinate. -/
theorem blind_tagged_verification_count [Fintype BasisIndex]
    (b : Module.Basis BasisIndex (ZMod 2) K) :
    2 ^ Fintype.card BasisIndex = Fintype.card K := by
  rw [← ZMod.card 2, ← Module.card_fintype b]

noncomputable def badBlindTaggedTrials {N : ℕ} (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (split : (Col → ZMod 2) → Prop)
    (b : Module.Basis BasisIndex (ZMod 2) K) : Finset (TaggedTrial K Col N) := by
  classical
  exact Finset.univ.filter fun t => ¬BlindTaggedSucceeds M split b
    (fun i => t.1 (numbering (Sum.inl i))) (fun j => t.1 (numbering (Sum.inr j))) t.2.1 t.2.2

/-- The hidden tag is used only in the correctness argument. A public
verifier which accepts each tagged dependency inherits the same bound. -/
theorem blind_tagged_failure_fraction_le [Fintype Tag] {N : ℕ}
    (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (split : (Col → ZMod 2) → Prop) (b : Module.Basis BasisIndex (ZMod 2) K)
    (htag : ∃ w : Col → ZMod 2, M.mulVec w = 0 ∧ H.mulVec w ≠ 0)
    (hverify : ∀ w, M.mulVec w = 0 → H.mulVec w ≠ 0 → split w) :
    ((badBlindTaggedTrials numbering M split b).card : ℚ≥0) / Fintype.card (TaggedTrial K Col N) ≤
      (↑(2*M.rank + 1 + Fintype.card Col) : ℚ≥0) / Fintype.card K := by
  classical
  have hsub : badBlindTaggedTrials numbering M split b ⊆ badTaggedTrials numbering M H b := by
    intro t ht
    have hfail := (Finset.mem_filter.mp ht).2
    let good := fun (t : TaggedTrial K Col N) => TaggedSolverSucceeds M H b
      (fun i => t.1 (numbering (Sum.inl i))) (fun j => t.1 (numbering (Sum.inr j))) t.2.1 t.2.2
    let : DecidablePred (fun t => ¬good t) := fun _ => Classical.propDecidable _
    change t ∈ Finset.univ.filter (fun t => ¬good t)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hs
    apply hfail
    obtain ⟨hzero, bit, hM, hH⟩ := hs
    exact ⟨hzero, bit, hM, hverify _ hM hH⟩
  calc
    _ ≤ ((badTaggedTrials numbering M H b).card : ℚ≥0) / Fintype.card (TaggedTrial K Col N) := by
      gcongr
    _ ≤ _ := bad_tagged_trials_fraction_le numbering M H b htag

open Cogentic.RandomizedSignCount Cogentic.RandomizedOddSplit

/-- The public verifier accepts an optional extracted root exactly when its
gcd splits the input. The verifier does not compute CRT signs. -/
def SplitVerified {modulus : ℕ}
    (extract : (Col → ZMod 2) → Option (SquareFiber (1 : (ZMod modulus)ˣ)))
    (w : Col → ZMod 2) : Prop :=
  ∃ root, extract w = some root ∧ 1 < splitGcd root ∧ splitGcd root < modulus

/-- A hidden difference of two CRT signs suffices for the tag-free solver.
The only extraction premise is that the indicated character is realized
by the extracted root on each tagged kernel vector. -/
theorem blind_split_failure_fraction_le {modulus N : ℕ}
    (hm : 3 ≤ modulus) (ho : Odd modulus)
    (i j : Fin modulus.primeFactors.card) (numbering : Row ⊕ Col ≃ Fin N)
    (M : Matrix Row Col (ZMod 2)) (sign : Col → ZMod 2)
    (extract : (Col → ZMod 2) → Option (SquareFiber (1 : (ZMod modulus)ˣ)))
    (b : Module.Basis BasisIndex (ZMod 2) K)
    (htag : ∃ w, M.mulVec w = 0 ∧ sign ⬝ᵥ w ≠ 0)
    (hrealize : ∀ w, M.mulVec w = 0 → sign ⬝ᵥ w ≠ 0 →
      ∃ root, extract w = some root ∧ oddSigns hm ho root i ≠ oddSigns hm ho root j) :
    ((badBlindTaggedTrials numbering M (SplitVerified extract) b).card : ℚ≥0) /
        Fintype.card (TaggedTrial K Col N) ≤
      (↑(2*M.rank + 1 + Fintype.card Col) : ℚ≥0) / Fintype.card K := by
  let H : Matrix Unit Col (ZMod 2) := fun _ => sign
  have hiff (w : Col → ZMod 2) : H.mulVec w ≠ 0 ↔ sign ⬝ᵥ w ≠ 0 := by
    have heq : H.mulVec w = 0 ↔ sign ⬝ᵥ w = 0 := by
      constructor
      · intro hz
        exact congrFun hz ()
      · intro hz
        funext ⟨⟩
        exact hz
    exact not_congr heq
  apply blind_tagged_failure_fraction_le numbering M H (SplitVerified extract) b
  · obtain ⟨w, hw, hs⟩ := htag
    exact ⟨w, hw, (hiff w).mpr hs⟩
  · intro w hw hs
    obtain ⟨root, hx, hbits⟩ := hrealize w hw ((hiff w).mp hs)
    refine ⟨root, hx, (proper_gcd_iff_mixed hm ho root).mpr ?_⟩
    cases hi : oddSigns hm ho root i <;> cases hj : oddSigns hm ho root j
    · exact (hbits (hi.trans hj.symm)).elim
    · exact ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
    · exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    · exact (hbits (hi.trans hj.symm)).elim

omit [Algebra (ZMod 2) K] [Fintype Row] [DecidableEq Row] [DecidableEq Col] [DecidableEq K] in
/-- A field of size at least eight times the positive column count gives
success probability at least one half under the tagged-witness premise. -/
theorem blind_split_bound_le_half (M : Matrix Row Col (ZMod 2))
    (hcol : 0 < Fintype.card Col) (hsize : 8 * Fintype.card Col ≤ Fintype.card K) :
    (↑(2*M.rank + 1 + Fintype.card Col) : ℚ≥0) / Fintype.card K ≤ 1/2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr := M.rank_le_card_width
  have h : (2*M.rank + 1 + Fintype.card Col) * 2 ≤ 1 * Fintype.card K := by omega
  have hq : 0 < (Fintype.card K : ℚ≥0) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card K)
  apply (div_le_div_iff₀ hq (by norm_num)).mpr
  exact_mod_cast h

end BlindSolver

section Classifier

variable {Row Col Ω : Type*} [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]

/-- A hidden scalar tag that vanishes on the constraint kernel is the
restriction of a binary linear classifier of the public columns. -/
theorem exists_classifier_of_tag_zero_on_kernel
    (M : Matrix Row Col (ZMod 2)) (s : Col → ZMod 2)
    (h : ∀ w, M.mulVec w = 0 → s ⬝ᵥ w = 0) :
    ∃ c : Row → ZMod 2, ∀ j, c ⬝ᵥ M.col j = s j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := dotProductEquiv (ZMod 2) Col
  let F := dotProductEquiv (ZMod 2) Row
  have hL : E s ∈ M.mulVecLin.ker.dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro w hw
    exact h w (LinearMap.mem_ker.mp hw)
  rw [← M.mulVecLin.range_dualMap_eq_dualAnnihilator_ker] at hL
  obtain ⟨f, hf⟩ := hL
  refine ⟨F.symm f, fun j => ?_⟩
  have hj := LinearMap.congr_fun hf (Pi.single j 1)
  change f (M.mulVec (Pi.single j 1)) = s ⬝ᵥ Pi.single j 1 at hj
  rw [Matrix.mulVec_single_one, dotProduct_single_one] at hj
  change F (F.symm f) (M.col j) = s j
  rwa [F.apply_symm_apply]

/-- Sources on which one fixed public sign classifier agrees with the hidden sign. -/
noncomputable def signAgreement [Fintype Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (c : Row → ZMod 2) : Finset Ω :=
  Finset.univ.filter fun ω => c ⬝ᵥ pub ω = sign ω

/-- Independent batches whose hidden sign vanishes on every public dependency. -/
noncomputable def hiddenSpanMisses [Fintype Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (m : ℕ) : Finset (Fin m → Ω) := by
  classical
  exact Finset.univ.filter fun draw => ¬∃ w : Fin m → ZMod 2,
    (show Matrix Row (Fin m) (ZMod 2) from fun i j => pub (draw j) i).mulVec w = 0 ∧
      (fun j => sign (draw j)) ⬝ᵥ w ≠ 0

private theorem hiddenSpanMisses_subset [Fintype Ω] (pub : Ω → Row → ZMod 2)
    (sign : Ω → ZMod 2) (m : ℕ) :
    hiddenSpanMisses pub sign m ⊆
      (by
        classical
        exact (Finset.univ : Finset (Row → ZMod 2)).biUnion
          (fun c => Fintype.piFinset fun _ : Fin m => signAgreement pub sign c)) := by
  classical
  intro draw hd
  let M : Matrix Row (Fin m) (ZMod 2) := fun i j => pub (draw j) i
  let s := fun j => sign (draw j)
  have h : ∀ w, M.mulVec w = 0 → s ⬝ᵥ w = 0 := by
    intro w hw
    by_contra hn
    exact (Finset.mem_filter.mp hd).2 ⟨w, hw, hn⟩
  obtain ⟨c, hc⟩ := exists_classifier_of_tag_zero_on_kernel M s h
  refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc j⟩

/-- If every public linear classifier agrees with the hidden character on
at most a `θ` fraction of sources, then `m` IID sources have no nonzero
hidden tag on the public kernel with probability at most `2^d * θ^m`.
Here `d` is the number of public coordinates. -/
theorem hiddenSpan_miss_fraction_le [Fintype Ω] [Nonempty Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (m : ℕ) (θ : ℚ≥0)
    (hagrees : ∀ c, ((signAgreement pub sign c).card : ℚ≥0) / Fintype.card Ω ≤ θ) :
    ((hiddenSpanMisses pub sign m).card : ℚ≥0) / Fintype.card (Fin m → Ω) ≤
      2 ^ Fintype.card Row * θ^m := by
  classical
  let a : ℚ≥0 := Fintype.card Ω
  have ha : 0 < a := by dsimp [a]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hcount := (Finset.card_le_card (hiddenSpanMisses_subset pub sign m)).trans Finset.card_biUnion_le
  have ht : Fintype.card (Fin m → Ω) = Fintype.card Ω ^ m := by simp
  rw [ht, Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos ha _)).mpr
  calc
    _ ≤ ∑ c : Row → ZMod 2, ((signAgreement pub sign c).card : ℚ≥0)^m := by
      simp only [Fintype.card_piFinset_const] at hcount
      exact_mod_cast hcount
    _ ≤ ∑ _c : Row → ZMod 2, (θ * a)^m := by
      apply Finset.sum_le_sum
      intro c _
      exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ ha).mp (hagrees c)) _
    _ = _ := by simp [ZMod.card, mul_pow, Nat.cast_pow, mul_assoc, a]

/-- Fourier coefficient of the binary difference between the hidden
character and the chosen public character. Each agreement contributes
`+1`, and each disagreement contributes `-1`. -/
noncomputable def hiddenSignFourier [Fintype Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (c : Row → ZMod 2) : ℚ :=
  2 * ((signAgreement pub sign c).card : ℚ) / Fintype.card Ω - 1

omit [DecidableEq Row] in
theorem hiddenSignFourier_eq_average [Fintype Ω] [Nonempty Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (c : Row → ZMod 2) :
    hiddenSignFourier pub sign c =
      (∑ ω, if c ⬝ᵥ pub ω = sign ω then (1 : ℚ) else -1) / Fintype.card Ω := by
  classical
  let G := signAgreement pub sign c
  let f := fun ω => if c ⬝ᵥ pub ω = sign ω then (1 : ℚ) else -1
  have hG : (∑ ω ∈ G, f ω) = G.card := by
    calc
      _ = ∑ _ω ∈ G, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro ω hw
        exact if_pos (Finset.mem_filter.mp hw).2
      _ = _ := by simp
  have hGc : (∑ ω ∈ Gᶜ, f ω) = -(Gᶜ.card : ℚ) := by
    calc
      _ = ∑ _ω ∈ Gᶜ, (-1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro ω hw
        apply if_neg
        intro he
        exact (Finset.mem_compl.mp hw) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      _ = _ := by simp
  have hsum : ∑ ω, f ω = 2 * (G.card : ℚ) - Fintype.card Ω := by
    rw [← Finset.sum_add_sum_compl G, hG, hGc, Finset.card_compl,
      Nat.cast_sub (Finset.card_le_univ _)]
    ring
  change 2 * (G.card : ℚ) / Fintype.card Ω - 1 = (∑ ω, f ω) / Fintype.card Ω
  have ha : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, sub_div, div_self ha]

/-- A Fourier bias bound for each classifier difference gives the
IID hidden-span failure bound with `θ = (1 + ε)/2`. -/
theorem hiddenSpan_miss_fraction_le_of_fourier [Fintype Ω] [Nonempty Ω]
    (pub : Ω → Row → ZMod 2) (sign : Ω → ZMod 2) (m : ℕ) (ε : ℚ≥0)
    (hbias : ∀ c, |hiddenSignFourier pub sign c| ≤ (ε : ℚ)) :
    ((hiddenSpanMisses pub sign m).card : ℚ≥0) / Fintype.card (Fin m → Ω) ≤
      2 ^ Fintype.card Row * ((1 + ε)/2)^m := by
  apply hiddenSpan_miss_fraction_le
  intro c
  have hu := (abs_le.mp (hbias c)).2
  unfold hiddenSignFourier at hu
  have hv : ((signAgreement pub sign c).card : ℚ) / Fintype.card Ω ≤ (1 + (ε : ℚ))/2 := by
    rw [mul_div_assoc] at hu
    linarith
  exact_mod_cast hv

end Classifier

end Cogentic.RandomizedTaggedDependency
