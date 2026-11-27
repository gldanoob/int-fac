import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedFieldExtraction

/-!
# Randomized epoch algebra: the final split-probability assembly

This file isolates the last algebra step of the randomized factoring epoch.  The
blueprint's C5.d/C5.e leaves (L33–L39) end with the hidden-sign split probability
`γ / 2 - ε`: rows exceeding columns give a nonempty dependency mask (L33), the
multi-field root assembly turns the mask into a public square check (L35), and the
recognizer coupling is folded into the good-transcript mass `γ` rather than the TV
error `ε` (L39).  The corresponding Lean endpoint is
`RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half`.

The theorems below package that endpoint in three layers:

1. `hit_prob_ge`: the abstract one-epoch statement.  Given the C1 congruence check,
   C2 hidden-sign uniformity, a good-transcript mass `γ`, and an ideal/actual TV
   bound `ε`, the assembled epoch attempt accepts with probability at least
   `γ / 2 - ε`.  This is exactly
   `HardEpochData.assembledAttempt_hit_prob_ge`, but with the four analytic leaves
   collected in an inspectable structure.
2. `ofMultiField_hit_prob_ge`: the concrete multi-field instantiation.  The
   extraction-success leaf is the structure `MultiFieldSplitSuccess`, whose two
   fields are precisely the hypotheses of
   `multiField_epoch_verified_split_probability_half`.  That theorem discharges the
   leaf, so no analytic hypothesis is hidden here beyond the public good-transcript
   mass and the TV error.
3. `hardEpochAsymptoticBound_of_certificate`: the feeding theorem.  A positive
   constant lower bound `c ≤ γ / 2 - ε` (hence, by layer 1, a constant lower bound
   on the actual hit probability), together with the congruence check, hidden-sign
   uniformity, and a public-work bound at exponent `C`, yields
   `HardEpochAsymptoticBound E C` through
   `hardEpochAsymptoticBound_of_const_hit`.  The same certificate is also shown to
   imply the pointwise constant hit bound `ConstHitBound E c`.

No analytic leaf is assumed as an axiom: every analytic input (the C1 congruence
check, C2 hidden-sign uniformity, the good-transcript mass estimate of blueprint C5,
the TV estimate of L39, and the public-work bound at `C`) is an explicit hypothesis
of the assembly or of the certificate.
-/

namespace Cogentic.RandomizedEpochAlgebra

open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochSuccess
open Cogentic.RandomizedFieldExtraction
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenLabels
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedOneThirdAsymptotic
open Filter Real
open scoped ENNReal

/-! ## Section 1: Abstract split algebra for a single hard-input epoch -/

/-- The one-epoch split-algebra inputs: the good-transcript mass `γ`, the TV error
`ε`, the ideal mass of the good event, and the ideal-to-actual TV bound.

The field `gamma_le_goodMass` is the quantitative C5 input (the public transcript
is good with ideal probability at least `γ`); `tv_le` is the L39 coupling error.
No relation between `γ` and `ε` is imposed here beyond the eventual constant lower
bound in `SplitMassBound`. -/
structure SplitAlgebraWitness {N : ℕ} (E : HardEpochData N) where
  gamma : ℝ
  epsilon : ℝ
  gamma_nonneg : 0 ≤ gamma
  gamma_le_goodMass :
    gamma ≤ (E.ideal.toOuterMeasure {x | observe E.trace x ∈ E.good}).toReal
  tv_le : pmfTotalVariation E.ideal E.actual ≤ epsilon

/-- Abstract split-probability assembly for one epoch.  This is the exact
`γ / 2 - ε` conclusion requested from the C1 congruence check, C2 hidden-sign
uniformity, the good-transcript mass `γ`, and the TV bound `ε`.

It is `HardEpochData.assembledAttempt_hit_prob_ge` with the analytic inputs bundled
in `SplitAlgebraWitness`. -/
theorem hit_prob_ge {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N)
    (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    (D : SplitAlgebraWitness E) :
    D.gamma / 2 - D.epsilon ≤
      ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure {o | o.1 ≠ none}).toReal :=
  E.assembledAttempt_hit_prob_ge hN ho hnot hcheck huniform
    D.gamma_nonneg D.gamma_le_goodMass D.tv_le

/-- Constant-hit corollary of `hit_prob_ge`: any positive `c` below the split
margin `γ / 2 - ε` is also below the actual success probability. -/
theorem hit_prob_ge_of_const {N : ℕ} (E : HardEpochData N) (hN : 3 ≤ N)
    (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (hcheck : E.CongruenceCheck) (huniform : E.HiddenUniform)
    (D : SplitAlgebraWitness E) {c : ℝ}
    (hc : c ≤ D.gamma / 2 - D.epsilon) :
    c ≤ ((E.actual.map (E.assembledAttempt hN)).toOuterMeasure
      {o | o.1 ≠ none}).toReal :=
  hc.trans (hit_prob_ge E hN ho hnot hcheck huniform D)

/-! ## Section 2: Multi-field extraction instantiation

The C5.d algebra produces a `PublicMultiFieldTranscript` on every good public
transcript: a nonempty binary mask (L33), a per-field product decomposition, and
verified rational/field roots (L35).  The remaining extraction-success statement is
that this public data satisfies the global modular product identity and that the
ideal hidden-sign law is uniform along the private mask coordinate.  These are
exactly the two hypotheses of
`multiField_epoch_verified_split_probability_half` (blueprint L33–L39). -/

/-- Explicit multi-field extraction-success leaf.

`global_product` is the public global modular identity of L33/L35: the product of
the squared private labels over the sparse mask equals the rational correction
times the product of the per-field products.  `hidden_uniform` is the conditional
hidden-sign symmetry on the private mask coordinate (C2 in the multi-field
presentation).

This structure is discharged by the existing theorem
`RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half`; it is
kept explicit so that any future concrete solver can be audited against the same
interface. -/
structure MultiFieldSplitSuccess
    {Coins Label FieldId Public : Type} {N : ℕ}
    (ideal : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N) where
  global_product : ∀ (t : good) x, observe trace x = t.val →
    (∏ i ∈ (extract t).mask, (x.2 i) ^ 2) =
      (extract t).ratCorr * ∏ j ∈ (extract t).fields, (extract t).fieldProd j
  hidden_uniform : ∀ (t : good) x y, observe trace x = t.val → x.1 = y.1 →
    ∀ i ∈ (extract t).mask, (x.2 i) ^ 2 = (y.2 i) ^ 2 →
    (∀ j, j ≠ i → x.2 j = y.2 j) → ideal x = ideal y

/-- Multi-field split-probability assembly.  This is the first component of
`RandomizedFieldExtraction.multiField_epoch_verified_split_probability_half`,
stated with the extraction-success leaf `MultiFieldSplitSuccess` isolated. -/
theorem multiField_hit_prob_ge
    {Coins Label FieldId Public : Type} [Fintype Coins] [Fintype Label]
    [DecidableEq Label] [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (S : MultiFieldSplitSuccess ideal trace good extract)
    {γ ε : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    γ / 2 - ε ≤
      ((actual.map (epochTrial trace good
        (fun t => (extract t).toTranscriptData))).toOuterMeasure
        {o | o.1 ≠ none}).toReal :=
  (multiField_epoch_verified_split_probability_half hN ho hnot ideal actual trace good
    extract S.global_product S.hidden_uniform γ ε hγ₀ hγ hTV).1

/-- Multi-field split-probability assembly for the concrete `HardEpochData`
constructed by `HardEpochData.ofMultiField`.  The conclusion is stated for
`assembledAttempt`, i.e. the charged epoch attempt, rather than the bare verifier. -/
theorem ofMultiField_hit_prob_ge
    {Coins Label FieldId Public : Type} [Fintype Coins] [Fintype Label]
    [DecidableEq Label] [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ)
    (S : MultiFieldSplitSuccess ideal trace good extract)
    {γ ε : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    γ / 2 - ε ≤
      (((HardEpochData.ofMultiField ideal actual trace good extract pubWork).actual.map
        ((HardEpochData.ofMultiField ideal actual trace good extract pubWork).assembledAttempt
          hN)).toOuterMeasure {o | o.1 ≠ none}).toReal := by
  rw [HardEpochData.assembledAttempt_hit_prob_eq
    (HardEpochData.ofMultiField ideal actual trace good extract pubWork) hN]
  dsimp only [HardEpochData.ofMultiField]
  exact multiField_hit_prob_ge hN ho hnot ideal actual trace good extract S hγ₀ hγ hTV

/-- Constant-hit corollary of `ofMultiField_hit_prob_ge`. -/
theorem ofMultiField_hit_prob_ge_of_const
    {Coins Label FieldId Public : Type} [Fintype Coins] [Fintype Label]
    [DecidableEq Label] [DecidableEq Public] {N : ℕ}
    (hN : 3 ≤ N) (ho : Odd N) (hnot : ¬ IsPrimePow N)
    (ideal actual : PMF (Coins × (Label → (ZMod N)ˣ)))
    (trace : Coins → (Label → (ZMod N)ˣ) → Public)
    (good : Finset Public)
    (extract : good → PublicMultiFieldTranscript Label FieldId N)
    (pubWork : Coins × (Label → (ZMod N)ˣ) → ℕ)
    (S : MultiFieldSplitSuccess ideal trace good extract)
    {γ ε c : ℝ} (hc : c ≤ γ / 2 - ε)
    (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ (ideal.toOuterMeasure {x | observe trace x ∈ good}).toReal)
    (hTV : pmfTotalVariation ideal actual ≤ ε) :
    c ≤
      (((HardEpochData.ofMultiField ideal actual trace good extract pubWork).actual.map
        ((HardEpochData.ofMultiField ideal actual trace good extract pubWork).assembledAttempt
          hN)).toOuterMeasure {o | o.1 ≠ none}).toReal :=
  hc.trans (ofMultiField_hit_prob_ge hN ho hnot ideal actual trace good extract pubWork
    S hγ₀ hγ hTV)

/-! ## Section 3: Uniform certification and the asymptotic epoch bound -/

/-- Eventual C1 congruence check along a hard-input epoch family. -/
def CongruenceEventually (E : ∀ n, 3 ≤ n → HardEpochData n) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), Odd n → ¬ n.Prime → ¬ IsPrimePow n →
    (E n hN).CongruenceCheck

/-- Eventual C2 hidden-sign uniformity along a hard-input epoch family. -/
def HiddenUniformEventually (E : ∀ n, 3 ≤ n → HardEpochData n) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), Odd n → ¬ n.Prime → ¬ IsPrimePow n →
    (E n hN).HiddenUniform

/-- Public-work bound at exponent `C`: for every `δ > 0`, eventually the expected
charged public work is at most `exp ((C + δ / 2) * scale n)`.  This is exactly the
work component of `HardEpochAsymptoticBound`. -/
def PublicWorkBound (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ (hN : 3 ≤ n), Odd n → ¬ n.Prime → ¬ IsPrimePow n →
      ∃ W_pub : ℝ,
        mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
          ENNReal.ofReal W_pub ∧
        W_pub ≤ exp ((C + δ / 2) * scale n)

/-- Split-mass/TV bound with constant margin `c`: eventually every hard input has
a good-transcript mass `γ` and a TV error `ε` with `γ / 2 - ε ≥ c`. -/
def SplitMassBound (E : ∀ n, 3 ≤ n → HardEpochData n) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ (hN : 3 ≤ n), Odd n → ¬ n.Prime → ¬ IsPrimePow n →
      ∃ γ ε : ℝ, 0 ≤ γ ∧
        γ ≤ ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal ∧
        pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε ∧
        c ≤ γ / 2 - ε

/-- Pointwise constant lower bound on the actual hit probability of the assembled
epoch attempt. -/
def ConstHitBound (E : ∀ n, 3 ≤ n → HardEpochData n) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ (hN : 3 ≤ n), Odd n → ¬ n.Prime → ¬ IsPrimePow n →
      c ≤ (((E n hN).actual.map ((E n hN).assembledAttempt hN)).toOuterMeasure
        {o | o.1 ≠ none}).toReal

/-- A complete split-algebra certificate for a hard-input epoch family at target
exponent `C` and constant hit margin `c`. -/
structure SplitAlgebraCertificate (E : ∀ n, 3 ≤ n → HardEpochData n) (C c : ℝ) : Prop where
  c_pos : 0 < c
  congruence : CongruenceEventually E
  hidden_uniform : HiddenUniformEventually E
  public_work : PublicWorkBound E C
  split_mass : SplitMassBound E c

/-- Feeding theorem, modular form: C1, C2, the public-work bound at `C`, and a
constant split margin `c > 0` imply `HardEpochAsymptoticBound E C`.

This is `RandomizedEpochAssembly.hardEpochAsymptoticBound_of_const_hit` after the
C1/C2/work/mass pieces are separated into independently auditable hypotheses. -/
theorem hardEpochAsymptoticBound_of_splitAlgebra
    (E : ∀ n, 3 ≤ n → HardEpochData n) {C c : ℝ}
    (hc : 0 < c)
    (hcheck : CongruenceEventually E)
    (huniform : HiddenUniformEventually E)
    (hwork : PublicWorkBound E C)
    (hsplit : SplitMassBound E c) :
    HardEpochAsymptoticBound E C := by
  refine hardEpochAsymptoticBound_of_const_hit E hc ?_
  intro δ hδ
  filter_upwards [hcheck, huniform, hwork δ hδ, hsplit] with n h1 h2 h3 h4
  intro hN ho hp hpow
  obtain ⟨W_pub, hmean, hW⟩ := h3 hN ho hp hpow
  obtain ⟨γ, ε, hγ₀, hγ, hTV, hcγ⟩ := h4 hN ho hp hpow
  exact ⟨h1 hN ho hp hpow, h2 hN ho hp hpow,
    W_pub, γ, ε, hγ₀, hmean, hW, hγ, hTV, hcγ⟩

/-- Feeding theorem, hit-probability form: the same split-algebra hypotheses also
give the constant lower bound `c` on the actual assembled attempt.  This is the
direct use of `hit_prob_ge` at the family level. -/
theorem const_hit_of_splitAlgebra
    (E : ∀ n, 3 ≤ n → HardEpochData n) {c : ℝ}
    (hcheck : CongruenceEventually E)
    (huniform : HiddenUniformEventually E)
    (hsplit : SplitMassBound E c) :
    ConstHitBound E c := by
  filter_upwards [hcheck, huniform, hsplit] with n h1 h2 h3
  intro hN ho hp hpow
  obtain ⟨γ, ε, hγ₀, hγ, hTV, hcγ⟩ := h3 hN ho hp hpow
  exact hcγ.trans ((E n hN).assembledAttempt_hit_prob_ge hN ho hpow
    (h1 hN ho hp hpow) (h2 hN ho hp hpow) hγ₀ hγ hTV)

/-- Certificate form of `hardEpochAsymptoticBound_of_splitAlgebra`. -/
theorem hardEpochAsymptoticBound_of_certificate
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C c : ℝ}
    (H : SplitAlgebraCertificate E C c) :
    HardEpochAsymptoticBound E C :=
  hardEpochAsymptoticBound_of_splitAlgebra E H.c_pos H.congruence H.hidden_uniform
    H.public_work H.split_mass

/-- Certificate form of `const_hit_of_splitAlgebra`. -/
theorem const_hit_of_certificate
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C c : ℝ}
    (H : SplitAlgebraCertificate E C c) :
    ConstHitBound E c :=
  const_hit_of_splitAlgebra E H.congruence H.hidden_uniform H.split_mass

/-- Combined certificate form: a positive split margin simultaneously feeds the
asymptotic epoch interface and certifies the constant actual hit probability. -/
theorem hardEpochAsymptoticBound_and_const_hit_of_certificate
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C c : ℝ}
    (H : SplitAlgebraCertificate E C c) :
    HardEpochAsymptoticBound E C ∧ ConstHitBound E c :=
  ⟨hardEpochAsymptoticBound_of_certificate H, const_hit_of_certificate H⟩

#print axioms hit_prob_ge
#print axioms hit_prob_ge_of_const
#print axioms multiField_hit_prob_ge
#print axioms ofMultiField_hit_prob_ge
#print axioms ofMultiField_hit_prob_ge_of_const
#print axioms hardEpochAsymptoticBound_of_splitAlgebra
#print axioms const_hit_of_splitAlgebra
#print axioms hardEpochAsymptoticBound_of_certificate
#print axioms const_hit_of_certificate
#print axioms hardEpochAsymptoticBound_and_const_hit_of_certificate

end Cogentic.RandomizedEpochAlgebra
