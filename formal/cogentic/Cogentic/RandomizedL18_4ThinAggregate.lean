import Cogentic.RandomizedL18_4Thin
import Mathlib.Data.Int.CardIntervalMod

/-!
# L18.4: the thin-pair aggregate from determinant levels and the rational-good count

`RandomizedL18_4Thin.ThinPairInputs` isolates three counting estimates behind the
rational-good thin-pair fraction:

* `strip_count`, the determinant-strip / lattice covering count;
* `mark_count`, the rational-good mark count;
* `cutoff_in_range`, the fixed power margin of the free determinant cutoff.

This file constructs those three fields from explicit data rather than assuming
them.

## The model

A `LatticeBox` is a finite set of primitive marks `P = (w, b)` with positive
denominators in a box `(lo, hi]`, denominators bounded below by `bmin`, and
determinants divisible by the root modulus `q`.  The determinant level of an
ordered pair is `det P Q = w_P b_Q - w_Q b_P`.  The divisibility is not an extra
axiom: `det_dvd_of_root` derives it from the root lattice
`w ≡ s b (mod q)` by cancellation.  The file proves:

* `level_card_le`: a nonzero determinant level set `T` (all `D ≠ 0`, `|D| ≤ X`,
  `q ∣ D`) has at most `2X/q` elements, by mapping `D ↦ D / q` into the nonzero
  integers of `[-⌊X/q⌋, ⌊X/q⌋]`;
* `partnerSet_card_le`: a mark `P` has at most `1 + 2 L X/q` partners in the
  strip `|det| ≤ X`, because the diagonal is at most the single point `P`
  (`PrimitiveMark.det_level_zero` plus primitivity) and every nonzero level
  carries at most `L` points (`PrimitiveMark.det_level_card_le`);
* `stripPairSet_card_le`: summing over the marks gives the paper's
  `(1 + 2 L V²/(qk)) R`.

## The three `ThinPairInputs` fields

The aggregate `ThinAggregate I` additionally carries the rational-good cell
counts of `I : L18_4Inputs`:

* `cutoff_in_range` is *reduced* to the explicit fixed power margin
  `2 q (1 + log V) ≤ ρ V²/K` (`power_margin`), an algebraic rearrangement; the
  equivalence `cutoff_in_range_iff_power_margin` shows the reduction is exact;
* `mark_count` is *proved* from `I.cell_prime_count` and
  `I.cell_numerator_count`, the retained-cell inclusion
  `K Ncell Nnum ≤ #marks`, and the explicit constant comparison
  `4 d ρ_ref ≤ ρ`;
* `strip_count` is *proved* from the determinant-level lattice counts above.

Nothing here is a `sorry`, an `axiom`, or `native_decide`; no count, loss or
mass is set to zero.
-/

namespace Cogentic.RandomizedL18_4

open Finset Real
open Cogentic.RandomizedPaperLeafStatements

/-! ## 1. The determinant and the determinant-level count -/

/-- The determinant of two integer points `(w, b)`, `(w', b')`:
`w b' - w' b`. -/
def det (P Q : ℤ × ℤ) : ℤ := P.1 * Q.2 - Q.1 * P.2

@[simp] theorem det_apply (P Q : ℤ × ℤ) : det P Q = P.1 * Q.2 - Q.1 * P.2 := rfl

/-- **Root-lattice divisibility of determinants.**  If both marks lie in the
root lattice `w ≡ s b (mod q)`, then `q ∣ det P Q`: the two residue terms cancel
identically.  This is where the divisor hypothesis of `LatticeBox.det_dvd`
comes from. -/
theorem det_dvd_of_root {q s : ℤ} {P Q : ℤ × ℤ}
    (hP : P.1 ≡ s * P.2 [ZMOD q]) (hQ : Q.1 ≡ s * Q.2 [ZMOD q]) :
    q ∣ det P Q := by
  have h1 : P.1 * Q.2 ≡ (s * P.2) * Q.2 [ZMOD q] :=
    hP.mul (Int.ModEq.refl Q.2)
  have h2 : Q.1 * P.2 ≡ (s * Q.2) * P.2 [ZMOD q] :=
    hQ.mul (Int.ModEq.refl P.2)
  have h := h1.sub h2
  have hzero : det P Q ≡ 0 [ZMOD q] := by
    have h' : det P Q ≡ (s * P.2) * Q.2 - (s * Q.2) * P.2 [ZMOD q] := by
      simpa [det] using h
    rw [show (s * P.2) * Q.2 - (s * Q.2) * P.2 = 0 by ring] at h'
    exact h'
  exact Int.modEq_zero_iff_dvd.mp hzero

/-- **A nonzero determinant level set has at most `2X/q` elements.**  If every
`D ∈ T` is a nonzero multiple of `q` with `|D| ≤ X`, then `D ↦ D / q` injects
`T` into the nonzero integers of `[-⌊X/q⌋, ⌊X/q⌋]`, a set of `2⌊X/q⌋` elements,
and `2⌊X/q⌋ ≤ 2X/q`. -/
theorem level_card_le (q : ℕ) (hq : 0 < q) {X : ℝ} (hX : 0 ≤ X)
    {T : Finset ℤ} (hmem : ∀ D ∈ T, (q : ℤ) ∣ D ∧ D ≠ 0 ∧ |D| ≤ X) :
    (T.card : ℝ) ≤ 2 * X / (q : ℝ) := by
  classical
  set N : ℤ := ⌊X / (q : ℝ)⌋ with hN
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNnonneg : 0 ≤ N := by
    rw [hN]
    exact Int.floor_nonneg.mpr (div_nonneg hX hqR.le)
  -- the target set of normalized level indices
  set U : Finset ℤ := (Finset.Icc (-N) N).erase 0 with hU
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-N) N := by
    rw [Finset.mem_Icc]
    omega
  have hcardIcc : (Finset.Icc (-N) N).card = (2 * N + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have htoNat : (2 * N + 1).toNat = 2 * N.toNat + 1 := by
    have hcast : (((2 * N + 1).toNat : ℕ) : ℤ) = ((2 * N.toNat + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ 2 * N + 1), Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, Int.toNat_of_nonneg hNnonneg]
    exact Nat.cast_injective hcast
  have hcardU_nat : U.card = 2 * N.toNat := by
    rw [hU, Finset.card_erase_of_mem h0mem, hcardIcc, htoNat]
    omega
  have hNcast : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by
    have h : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hNnonneg
    exact_mod_cast h
  -- `D ↦ D / q` maps `T` into `U`
  have hmaps : Set.MapsTo (fun D : ℤ => D / (q : ℤ)) (T : Set ℤ) (U : Set ℤ) := by
    intro D hD
    obtain ⟨hdvd, hne, hle⟩ := hmem D hD
    set m : ℤ := D / (q : ℤ) with hm
    have hmul : m * (q : ℤ) = D := Int.ediv_mul_cancel hdvd
    have hmne : m ≠ 0 := by
      intro h0
      apply hne
      rw [← hmul, h0, zero_mul]
    have hDcast : (D : ℝ) = (m : ℝ) * (q : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hmul
      push_cast at h
      linarith
    have habs : ((|m| : ℤ) : ℝ) * (q : ℝ) = (|D| : ℝ) := by
      have h1 : ((|m| : ℤ) : ℝ) = |(m : ℝ)| := Int.cast_abs
      rw [h1, hDcast, abs_mul, abs_of_pos hqR]
    have hX' : (|D| : ℝ) ≤ X := by exact_mod_cast hle
    have hml : ((|m| : ℤ) : ℝ) ≤ X / (q : ℝ) := by
      rw [le_div_iff₀ hqR]
      calc
        ((|m| : ℤ) : ℝ) * (q : ℝ) = (|D| : ℝ) := habs
        _ ≤ X := hX'
    have hm_le_abs : (m : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
      exact_mod_cast le_abs_self m
    have hneg_le_abs : ((-m : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
      have h : (-m : ℤ) ≤ |m| := by simpa using le_abs_self (-m)
      exact_mod_cast h
    have hm1 : m ≤ N := by
      rw [hN]
      exact Int.le_floor.mpr (le_trans hm_le_abs hml)
    have hm2 : -N ≤ m := by
      have h : (-m : ℤ) ≤ N := by
        rw [hN]
        exact Int.le_floor.mpr (le_trans hneg_le_abs hml)
      omega
    change D / (q : ℤ) ∈ U
    rw [hU, Finset.mem_erase, Finset.mem_Icc]
    exact ⟨hmne, hm2, hm1⟩
  have hinj : (T : Set ℤ).InjOn (fun D : ℤ => D / (q : ℤ)) := by
    intro D₁ hD₁ D₂ hD₂ heq
    obtain ⟨hdvd₁, -, -⟩ := hmem D₁ hD₁
    obtain ⟨hdvd₂, -, -⟩ := hmem D₂ hD₂
    have heq' : D₁ / (q : ℤ) = D₂ / (q : ℤ) := heq
    have h1 : D₁ / (q : ℤ) * (q : ℤ) = D₁ := Int.ediv_mul_cancel hdvd₁
    rw [heq'] at h1
    have h2 : D₂ / (q : ℤ) * (q : ℤ) = D₂ := Int.ediv_mul_cancel hdvd₂
    rw [← h1, h2]
  have hcard : T.card ≤ U.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hUle : (U.card : ℝ) = 2 * (N : ℝ) := by
    rw [hcardU_nat]
    push_cast
    rw [hNcast]
  have hNle : (N : ℝ) ≤ X / (q : ℝ) := by
    rw [hN]
    exact Int.floor_le _
  calc
    (T.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hcard
    _ = 2 * (N : ℝ) := hUle
    _ ≤ 2 * (X / (q : ℝ)) := by linarith
    _ = 2 * X / (q : ℝ) := by ring

/-! ## 2. The lattice box and the per-mark strip count -/

/-- **A finite box of primitive marks.**  `S` is a finite set of primitive
integer points `(w, b)` with positive denominators in `(lo, hi]`, denominators
bounded below by `bmin`, and determinants divisible by the root modulus `q`.
`L` is the per-determinant-level solution bound. -/
structure LatticeBox where
  /-- The retained marks. -/
  S : Finset (ℤ × ℤ)
  /-- The root modulus. -/
  q : ℕ
  /-- The root modulus is positive. -/
  q_pos : 0 < q
  /-- Lower endpoint of the denominator interval. -/
  lo : ℤ
  /-- Upper endpoint of the denominator interval. -/
  hi : ℤ
  /-- The denominator interval is genuine. -/
  lo_le_hi : lo ≤ hi
  /-- Uniform lower bound for the denominators. -/
  bmin : ℕ
  /-- The denominator lower bound is positive. -/
  bmin_pos : 0 < bmin
  /-- The per-level solution bound `L₀`. -/
  L : ℝ
  /-- `L₀ ≥ (hi - lo)/bmin + 1`, the count of one residue class in the box. -/
  level_bound : ((hi - lo : ℤ) : ℝ) / (bmin : ℝ) + 1 ≤ L
  /-- Every mark is primitive. -/
  prim : ∀ P ∈ S, IsCoprime P.1 P.2
  /-- Every mark has a positive denominator. -/
  den_pos : ∀ P ∈ S, 0 < P.2
  /-- Every denominator lies in `(lo, hi]`. -/
  box : ∀ P ∈ S, lo < P.2 ∧ P.2 ≤ hi
  /-- Every denominator is at least `bmin`. -/
  bmin_le : ∀ P ∈ S, (bmin : ℤ) ≤ P.2
  /-- Every determinant is divisible by the root modulus. -/
  det_dvd : ∀ P ∈ S, ∀ Q ∈ S, (q : ℤ) ∣ det P Q

/-- The partners of `P` inside the determinant strip `|det| ≤ X`. -/
noncomputable def partnerSet (S : Finset (ℤ × ℤ)) (P : ℤ × ℤ) (X : ℝ) : Finset (ℤ × ℤ) :=
  S.filter fun Q => |det P Q| ≤ X

/-- The ordered pairs of marks inside the determinant strip `|det| ≤ X`. -/
noncomputable def stripPairSet (S : Finset (ℤ × ℤ)) (X : ℝ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (S.product S).filter fun r => |det r.1 r.2| ≤ X

/-- **The diagonal determinant level is a single point.**  On the zero level the
partner of a primitive mark is the mark itself, because
`PrimitiveMark.det_level_zero` makes it an integer multiple and primitivity
forces the multiplier to be a unit; positive denominators then force `+1`. -/
theorem zero_partner_card_le (B : LatticeBox) {P : ℤ × ℤ} (hP : P ∈ B.S) :
    ((B.S.filter fun Q => det P Q = 0).card : ℝ) ≤ 1 := by
  have hsub : (B.S.filter fun Q => det P Q = 0) ⊆ {P} := by
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨hQS, h0⟩ := hQ
    obtain ⟨t, ht1, ht2⟩ :=
      PrimitiveMark.det_level_zero (B.prim P hP) (B.den_pos P hP).ne' (by simpa [det] using h0)
    have hunit : IsUnit t := by
      refine (B.prim Q hQS).isUnit_of_dvd' ?_ ?_
      · exact ⟨P.1, ht1⟩
      · exact ⟨P.2, ht2⟩
    rcases Int.isUnit_eq_one_or hunit with h | h
    · have hQP : Q = P := by
        rw [Prod.ext_iff]
        exact ⟨by rw [ht1, h]; ring, by rw [ht2, h]; ring⟩
      simp [hQP]
    · exfalso
      have hpos := B.den_pos Q hQS
      rw [ht2, h] at hpos
      have hPpos := B.den_pos P hP
      linarith
  calc
    ((B.S.filter fun Q => det P Q = 0).card : ℝ) ≤ (({P} : Finset (ℤ × ℤ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = 1 := by simp

/-- **A mark has at most `1 + 2 L X/q` strip partners.**  Split the partners into
the diagonal level (`≤ 1` point, `zero_partner_card_le`) and the nonzero levels.
Every nonzero level has at most `L` points (`PrimitiveMark.det_level_card_le`),
and `level_card_le` bounds the number of nonzero levels by `2X/q`. -/
theorem partnerSet_card_le (B : LatticeBox) {P : ℤ × ℤ} (hP : P ∈ B.S) {X : ℝ}
    (hX : 0 ≤ X) :
    ((partnerSet B.S P X).card : ℝ) ≤ 1 + 2 * B.L * (X / (B.q : ℝ)) := by
  classical
  set nz : Finset (ℤ × ℤ) :=
    B.S.filter (fun Q => det P Q ≠ 0 ∧ |det P Q| ≤ X) with hnzdef
  have hsub : partnerSet B.S P X ⊆
      (B.S.filter fun Q => det P Q = 0) ∪ nz := by
    intro Q hQ
    rw [partnerSet, Finset.mem_filter] at hQ
    obtain ⟨hQS, hXQ⟩ := hQ
    by_cases h0 : det P Q = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hQS, h0⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hQS, h0, hXQ⟩)
  have hsplit : (partnerSet B.S P X).card ≤
      (B.S.filter fun Q => det P Q = 0).card + nz.card := by
    calc
      (partnerSet B.S P X).card ≤
          ((B.S.filter fun Q => det P Q = 0) ∪ nz).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le ..
  -- the nonzero-level fiber bound
  have hfiber : ∀ D ∈ nz.image (det P), ((nz.filter fun Q => det P Q = D).card : ℝ) ≤ B.L := by
    intro D _
    have hsubset : (nz.filter fun Q => det P Q = D) ⊆
        B.S.filter (fun Q => det P Q = D) := by
      intro Q hQ
      rw [Finset.mem_filter] at hQ
      have hQnz : Q ∈ nz := hQ.1
      rw [hnzdef, Finset.mem_filter] at hQnz
      rw [Finset.mem_filter]
      exact ⟨hQnz.1, hQ.2⟩
    have hlev : ((B.S.filter fun Q => det P Q = D).card : ℝ) ≤
        ((B.hi - B.lo : ℤ) : ℝ) / (P.2 : ℝ) + 1 := by
      refine @PrimitiveMark.det_level_card_le P.1 P.2 (B.prim P hP) (B.den_pos P hP) D
        (B.S.filter (fun Q => det P Q = D)) ?_ B.lo B.hi B.lo_le_hi ?_
      · intro Q hQ
        rw [Finset.mem_filter] at hQ
        exact hQ.2
      · intro Q hQ
        rw [Finset.mem_filter] at hQ
        exact B.box Q hQ.1
    have hbP : (0 : ℝ) < (P.2 : ℝ) := by exact_mod_cast B.den_pos P hP
    have hbminR : (0 : ℝ) < (B.bmin : ℝ) := by exact_mod_cast B.bmin_pos
    have hbmin_le : (B.bmin : ℝ) ≤ (P.2 : ℝ) := by exact_mod_cast B.bmin_le P hP
    have hdiam : (0 : ℝ) ≤ ((B.hi - B.lo : ℤ) : ℝ) := by
      exact_mod_cast sub_nonneg.mpr B.lo_le_hi
    have hstep : ((B.hi - B.lo : ℤ) : ℝ) / (P.2 : ℝ) + 1 ≤
        ((B.hi - B.lo : ℤ) : ℝ) / (B.bmin : ℝ) + 1 := by
      gcongr
    calc
      ((nz.filter fun Q => det P Q = D).card : ℝ) ≤
          ((B.S.filter fun Q => det P Q = D).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ((B.hi - B.lo : ℤ) : ℝ) / (P.2 : ℝ) + 1 := hlev
      _ ≤ ((B.hi - B.lo : ℤ) : ℝ) / (B.bmin : ℝ) + 1 := hstep
      _ ≤ B.L := B.level_bound
  have hnz : (nz.card : ℝ) ≤ B.L * ((nz.image (det P)).card : ℝ) := by
    have hcast : (nz.card : ℝ) =
        ∑ D ∈ nz.image (det P), ((nz.filter fun Q => det P Q = D).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image (f := fun Q : ℤ × ℤ => det P Q) (s := nz)]
      push_cast
      ring
    calc
      (nz.card : ℝ) = ∑ D ∈ nz.image (det P), ((nz.filter fun Q => det P Q = D).card : ℝ) :=
        hcast
      _ ≤ ∑ _D ∈ nz.image (det P), B.L := Finset.sum_le_sum hfiber
      _ = B.L * ((nz.image (det P)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hlevcard : ((nz.image (det P)).card : ℝ) ≤ 2 * X / (B.q : ℝ) := by
    refine level_card_le B.q B.q_pos hX ?_
    intro D hD
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hD
    rw [hnzdef, Finset.mem_filter] at hQ
    obtain ⟨hQS, hne, hle⟩ := hQ
    exact ⟨B.det_dvd P hP Q hQS, hne, hle⟩
  have hzero : ((B.S.filter fun Q => det P Q = 0).card : ℝ) ≤ 1 :=
    zero_partner_card_le B hP
  have hsum : ((B.S.filter fun Q => det P Q = 0).card : ℝ) + (nz.card : ℝ) ≤
      1 + 2 * B.L * (X / (B.q : ℝ)) := by
    have hLnn : 0 ≤ B.L := by
      have h0 : (0 : ℝ) ≤ ((B.hi - B.lo : ℤ) : ℝ) / (B.bmin : ℝ) + 1 := by
        have hbminR : (0 : ℝ) < (B.bmin : ℝ) := by exact_mod_cast B.bmin_pos
        have hdiam : (0 : ℝ) ≤ ((B.hi - B.lo : ℤ) : ℝ) := by
          exact_mod_cast sub_nonneg.mpr B.lo_le_hi
        positivity
      linarith [B.level_bound]
    have hthis : (nz.card : ℝ) ≤ B.L * (2 * X / (B.q : ℝ)) :=
      hnz.trans (mul_le_mul_of_nonneg_left hlevcard hLnn)
    have this' : (nz.card : ℝ) ≤ 2 * B.L * (X / (B.q : ℝ)) := by
      calc
        (nz.card : ℝ) ≤ B.L * (2 * X / (B.q : ℝ)) := hthis
        _ = 2 * B.L * (X / (B.q : ℝ)) := by ring
    linarith [hzero, this']
  calc
    ((partnerSet B.S P X).card : ℝ) ≤
        ((B.S.filter fun Q => det P Q = 0).card : ℝ) + (nz.card : ℝ) := by
      exact_mod_cast hsplit
    _ ≤ 1 + 2 * B.L * (X / (B.q : ℝ)) := hsum

/-- **The strip count from the determinant-level lattice bound.**  Summing
`partnerSet_card_le` over the marks gives the paper's
`#stripPairs ≤ (1 + 2 L X/q) R`, with `R = #S`. -/
theorem stripPairSet_card_le (B : LatticeBox) {X : ℝ} (hX : 0 ≤ X) :
    ((stripPairSet B.S X).card : ℝ) ≤
      (1 + 2 * B.L * (X / (B.q : ℝ))) * (B.S.card : ℝ) := by
  classical
  have hsub : stripPairSet B.S X ⊆
      B.S.biUnion fun P => (partnerSet B.S P X).image fun Q => (P, Q) := by
    intro r hr
    rw [stripPairSet, Finset.mem_filter] at hr
    obtain ⟨hrS, hXr⟩ := hr
    have hmem := Finset.mem_product.mp hrS
    rw [Finset.mem_biUnion]
    refine ⟨r.1, hmem.1, ?_⟩
    rw [Finset.mem_image]
    exact ⟨r.2, by rw [partnerSet, Finset.mem_filter]; exact ⟨hmem.2, hXr⟩, rfl⟩
  have hcard : (stripPairSet B.S X).card ≤
      ∑ P ∈ B.S, (partnerSet B.S P X).card := by
    calc
      (stripPairSet B.S X).card ≤
          (B.S.biUnion fun P => (partnerSet B.S P X).image fun Q => (P, Q)).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ P ∈ B.S, ((partnerSet B.S P X).image fun Q => (P, Q)).card :=
        Finset.card_biUnion_le
      _ = ∑ P ∈ B.S, (partnerSet B.S P X).card := by
        apply Finset.sum_congr rfl
        intro P _
        exact Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)
  calc
    ((stripPairSet B.S X).card : ℝ) ≤
        ∑ P ∈ B.S, ((partnerSet B.S P X).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hcard
    _ ≤ ∑ _P ∈ B.S, (1 + 2 * B.L * (X / (B.q : ℝ))) :=
      Finset.sum_le_sum fun P hP => partnerSet_card_le B hP hX
    _ = (1 + 2 * B.L * (X / (B.q : ℝ))) * (B.S.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ## 3. The thin-pair aggregate -/

/-- **The aggregate data behind the three `ThinPairInputs` counting fields.**

`box n` is the determinant-lattice model of the retained marks; `dens` is the
reference density `ρ`; the `thin_le_pairFraction` field identifies `thin` with
the normalized strip-pair count; and the remaining fields are the rational-good
counts and the two explicit numeric inputs:

* `retained_cell_count`: the rational-good cell marks are retained;
* `const_le`: `4 d ρ_ref ≤ ρ`, the constant bookkeeping in `mark_count`;
* `power_margin`: the fixed power margin `2 q (1 + log V) ≤ ρ V²/K`. -/
structure ThinAggregate (I : L18_4Inputs) where
  /-- The lattice box model of the retained marks at each stage. -/
  box : ℕ → LatticeBox
  /-- The reference density `ρ` of the numerator progression. -/
  dens : ℕ → ℝ
  /-- The reference density is positive. -/
  dens_pos : ∀ n, 0 < dens n
  /-- The reference density is at most one. -/
  dens_le_one : ∀ n, dens n ≤ 1
  /-- The root index is the geometric modulus. -/
  ell_eq : ∀ n, I.ell n = ((box n).q : ℝ)
  /-- `thin` is the normalized number of ordered strip pairs. -/
  thin_le_pairFraction : ∀ n, I.thin n ≤
    ((stripPairSet (box n).S
      (denomScale I.W n ^ 2 / thinCutoff I.W (fun m => (box m).L) dens n)).card : ℝ) /
      (((box n).S.card : ℝ) ^ 2)
  /-- **The rational-good cell marks are retained.**  The product of the cell
  denominator count and the numerator count is at most the number of marks. -/
  retained_cell_count : ∀ n, I.K n * I.Ncell n * I.Nnum n ≤ ((box n).S.card : ℝ)
  /-- **Constant bookkeeping for `mark_count`.** -/
  const_le : ∀ n, 4 * I.d n * dens n ≤ I.rho n
  /-- **The fixed power margin.**  `2 q (1 + log V) ≤ ρ V²/K`, where
  `V = exp W` and `K = V^{1/4}`.  This is the paper's `q/V² ≤ V^{-c₀}` with
  `c₀ > 1/4`, in the exact form needed for `cutoff_in_range`. -/
  power_margin : ∀ n,
    2 * ((box n).q : ℝ) * (1 + I.W n) ≤ dens n * denomScale I.W n ^ 2 / cellMesh I.W n

namespace ThinAggregate

variable {I : L18_4Inputs}

/-- The geometric modulus `q` of the aggregate. -/
noncomputable def q (A : ThinAggregate I) (n : ℕ) : ℝ := ((A.box n).q : ℝ)

/-- The per-level solution bound `L₀` of the aggregate. -/
noncomputable def L (A : ThinAggregate I) (n : ℕ) : ℝ := (A.box n).L

/-- The retained mark set of the aggregate. -/
noncomputable def S (A : ThinAggregate I) (n : ℕ) : Finset (ℤ × ℤ) := (A.box n).S

/-- The number of retained marks. -/
noncomputable def R (A : ThinAggregate I) (n : ℕ) : ℝ := ((A.box n).S.card : ℝ)

/-- The per-level bound is at least one. -/
theorem L_ge_one (A : ThinAggregate I) (n : ℕ) : 1 ≤ A.L n := by
  have hb : (0 : ℝ) < ((A.box n).bmin : ℝ) := by exact_mod_cast (A.box n).bmin_pos
  have hd : (0 : ℝ) ≤ ((A.box n).hi - (A.box n).lo : ℤ) := by
    exact_mod_cast sub_nonneg.mpr (A.box n).lo_le_hi
  have h0 : (0 : ℝ) ≤ ((A.box n).hi - (A.box n).lo : ℤ) / ((A.box n).bmin : ℝ) :=
    div_nonneg hd hb.le
  have := (A.box n).level_bound
  rw [L]
  linarith

/-- **`strip_count` from the determinant-level lattice count.** -/
theorem strip_count (A : ThinAggregate I) (n : ℕ) {k : ℝ} (hk : 0 < k) :
    ((stripPairSet (A.S n) (denomScale I.W n ^ 2 / k)).card : ℝ) ≤
      (1 + 2 * A.L n * (denomScale I.W n ^ 2 / (A.q n * k))) * A.R n := by
  have hX : 0 ≤ denomScale I.W n ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
  have h := stripPairSet_card_le (A.box n) hX
  have harg : (denomScale I.W n ^ 2 / k) / ((A.box n).q : ℝ) =
      denomScale I.W n ^ 2 / (A.q n * k) := by
    rw [q]
    have hq : ((A.box n).q : ℝ) ≠ 0 := by
      exact_mod_cast (A.box n).q_pos.ne'
    field_simp
  rw [harg] at h
  simpa [L, S, R, q] using h

/-- **The arithmetic core of the rational-good mark count.**  The cell
denominator and numerator lower bounds, multiplied and scaled by the `K` cells,
give `V² ρ/(4 d q (1 + W))`; the constant comparison `4 d ρ_ref ≤ ρ` then gives
`ρ_ref V²/(q (1 + W)) ≤ K Ncell Nnum`. -/
theorem mark_count_arith {V rho d K Nc Nn q dens W : ℝ}
    (hV : 0 < V) (hrho : 0 < rho) (hd : 0 < d) (hK : 0 < K) (hq : 0 < q)
    (hW : 0 < 1 + W)
    (hNc : V / (2 * d * K * (1 + W)) ≤ Nc)
    (hNn : V * rho / (2 * q) ≤ Nn)
    (hconst : 4 * d * dens ≤ rho) :
    dens * (V ^ 2 / (q * (1 + W))) ≤ K * Nc * Nn := by
  have hbase : V / (2 * d * K * (1 + W)) * (V * rho / (2 * q)) =
      V ^ 2 * rho / (4 * d * K * q * (1 + W)) := by
    field_simp
    ring
  have hNc_nn : 0 ≤ Nc := le_trans (by positivity) hNc
  have hprod : V / (2 * d * K * (1 + W)) * (V * rho / (2 * q)) ≤ Nc * Nn :=
    mul_le_mul hNc hNn (by positivity : 0 ≤ V * rho / (2 * q)) hNc_nn
  rw [hbase] at hprod
  have hKne : K ≠ 0 := hK.ne'
  have hstep : V ^ 2 * rho / (4 * d * q * (1 + W)) ≤ K * Nc * Nn := by
    have hleft : K * (V ^ 2 * rho / (4 * d * K * q * (1 + W))) =
        V ^ 2 * rho / (4 * d * q * (1 + W)) := by
      field_simp
    calc
      V ^ 2 * rho / (4 * d * q * (1 + W))
          = K * (V ^ 2 * rho / (4 * d * K * q * (1 + W))) := hleft.symm
      _ ≤ K * (Nc * Nn) := mul_le_mul_of_nonneg_left hprod hK.le
      _ = K * Nc * Nn := by ring
  have htarget : dens * (V ^ 2 / (q * (1 + W))) ≤
      V ^ 2 * rho / (4 * d * q * (1 + W)) := by
    have heq : V ^ 2 * rho / (4 * d * q * (1 + W)) =
        (rho / (4 * d)) * (V ^ 2 / (q * (1 + W))) := by
      field_simp
    rw [heq]
    have hle : dens ≤ rho / (4 * d) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d)]
      linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ V ^ 2 / (q * (1 + W)))
  exact htarget.trans hstep

/-- **`mark_count` from the rational-good denominator count.**  The cell prime
count `I.cell_prime_count`, the numerator count `I.cell_numerator_count`, the
retained-cell inclusion and the constant comparison give
`ρ V²/(q (1 + log V)) ≤ R`. -/
theorem mark_count (A : ThinAggregate I) (n : ℕ) :
    A.dens n * (denomScale I.W n ^ 2 / (A.q n * (1 + I.W n))) ≤ A.R n := by
  have hV : 0 < denomScale I.W n := by unfold denomScale; exact exp_pos _
  have hrho : 0 < I.rho n := I.rho_pos n
  have hd : 0 < I.d n := I.d_pos n
  have hK : 0 < I.K n := I.K_pos n
  have hq : 0 < A.q n := by
    rw [q]
    exact_mod_cast (A.box n).q_pos
  have hW : 0 < 1 + I.W n := by linarith [I.W_nonneg n]
  have hNc : denomScale I.W n / (2 * I.d n * I.K n * (1 + I.W n)) ≤ I.Ncell n := by
    simpa only [L18_4Inputs.K] using I.cell_prime_count n
  have hNn : denomScale I.W n * I.rho n / (2 * A.q n) ≤ I.Nnum n := by
    have h := I.cell_numerator_count n
    rw [A.ell_eq n] at h
    exact h
  have hprod := mark_count_arith hV hrho hd hK hq hW hNc hNn (A.const_le n)
  calc
    A.dens n * (denomScale I.W n ^ 2 / (A.q n * (1 + I.W n))) ≤
        I.K n * I.Ncell n * I.Nnum n := hprod
    _ ≤ A.R n := A.retained_cell_count n

/-- **`cutoff_in_range` from the fixed power margin.**  Substituting
`K_det = 4L₀(1 + W)/ρ · K` into `2L₀V²/(qK_det)` leaves
`ρV²/(2q(1 + W)K)`, and the power margin `2q(1 + W) ≤ ρV²/K` makes this at
least one. -/
theorem cutoff_in_range (A : ThinAggregate I) (n : ℕ) :
    1 ≤ 2 * A.L n * (denomScale I.W n ^ 2 / (A.q n * thinCutoff I.W A.L A.dens n)) := by
  have hK : 0 < cellMesh I.W n := by unfold cellMesh; exact exp_pos _
  have hL : 0 < A.L n := lt_of_lt_of_le zero_lt_one (A.L_ge_one n)
  have hdens : 0 < A.dens n := A.dens_pos n
  have hq : 0 < A.q n := by
    rw [q]
    exact_mod_cast (A.box n).q_pos
  have h1W : 0 < 1 + I.W n := by linarith [I.W_nonneg n]
  have hthin_ne : thinCutoff I.W A.L A.dens n ≠ 0 := by
    unfold thinCutoff
    positivity
  have hcell_ne : cellMesh I.W n ≠ 0 := hK.ne'
  have hL_ne : A.L n ≠ 0 := hL.ne'
  have hdens_ne : A.dens n ≠ 0 := hdens.ne'
  have h1W_ne : (1 + I.W n) ≠ 0 := h1W.ne'
  have hq_ne : A.q n ≠ 0 := hq.ne'
  have hid : 2 * A.L n * (denomScale I.W n ^ 2 / (A.q n * thinCutoff I.W A.L A.dens n)) =
      A.dens n * denomScale I.W n ^ 2 /
        (2 * A.q n * (1 + I.W n) * cellMesh I.W n) := by
    unfold thinCutoff
    field_simp
    ring
  rw [hid]
  rw [le_div_iff₀ (by positivity)]
  have hp := A.power_margin n
  have hmul := mul_le_mul_of_nonneg_right hp hK.le
  rw [div_mul_cancel₀ _ hcell_ne] at hmul
  simpa [q, mul_assoc] using hmul

/-- The `cutoff_in_range` inequality is *exactly* the power margin: the
cancellation `2L₀V²/(qK_det) = ρV²/(2q(1 + W)K)` is an identity, so no further
loss is incurred by the reduction. -/
theorem cutoff_in_range_iff_power_margin (A : ThinAggregate I) (n : ℕ) :
    (1 ≤ 2 * A.L n *
        (denomScale I.W n ^ 2 / (A.q n * thinCutoff I.W A.L A.dens n))) ↔
      2 * A.q n * (1 + I.W n) ≤
        A.dens n * denomScale I.W n ^ 2 / cellMesh I.W n := by
  have hK : 0 < cellMesh I.W n := by unfold cellMesh; exact exp_pos _
  have hL : 0 < A.L n := lt_of_lt_of_le zero_lt_one (A.L_ge_one n)
  have hdens : 0 < A.dens n := A.dens_pos n
  have hq : 0 < A.q n := by
    rw [q]
    exact_mod_cast (A.box n).q_pos
  have h1W : 0 < 1 + I.W n := by linarith [I.W_nonneg n]
  have hthin_ne : thinCutoff I.W A.L A.dens n ≠ 0 := by
    unfold thinCutoff
    positivity
  have hcell_ne : cellMesh I.W n ≠ 0 := hK.ne'
  have hL_ne : A.L n ≠ 0 := hL.ne'
  have hdens_ne : A.dens n ≠ 0 := hdens.ne'
  have h1W_ne : (1 + I.W n) ≠ 0 := h1W.ne'
  have hq_ne : A.q n ≠ 0 := hq.ne'
  have hid : 2 * A.L n * (denomScale I.W n ^ 2 / (A.q n * thinCutoff I.W A.L A.dens n)) =
      A.dens n * denomScale I.W n ^ 2 /
        (2 * A.q n * (1 + I.W n) * cellMesh I.W n) := by
    unfold thinCutoff
    field_simp
    ring
  rw [hid, le_div_iff₀ (by positivity), le_div_iff₀ hK]
  constructor
  · intro h
    simpa [mul_assoc] using h
  · intro h
    simpa [mul_assoc] using h

/-- **Assemble the `ThinPairInputs` record.** -/
noncomputable def toThinPairInputs (A : ThinAggregate I) : ThinPairInputs I.W I.thin where
  q := A.q
  dens := A.dens
  R := A.R
  L := A.L
  thinPairs := fun n k => ((stripPairSet (A.S n) (denomScale I.W n ^ 2 / k)).card : ℝ)
  W_nonneg := I.W_nonneg
  q_pos := fun n => by
    rw [q]
    exact_mod_cast (A.box n).q_pos
  dens_pos := A.dens_pos
  dens_le_one := A.dens_le_one
  R_pos := fun n => by
    have hq : 0 < A.q n := by
      rw [q]
      exact_mod_cast (A.box n).q_pos
    have hV : 0 < denomScale I.W n := by unfold denomScale; exact exp_pos _
    have h1W : 0 < 1 + I.W n := by linarith [I.W_nonneg n]
    have hpos : 0 < A.dens n *
        (denomScale I.W n ^ 2 / (A.q n * (1 + I.W n))) :=
      mul_pos (A.dens_pos n) (div_pos (pow_pos hV 2) (mul_pos hq h1W))
    exact lt_of_lt_of_le hpos (A.mark_count n)
  L_ge_one := A.L_ge_one
  thinPairs_nonneg := fun n X => Nat.cast_nonneg _
  thin_le_pairFraction := A.thin_le_pairFraction
  strip_count := fun n k hk => A.strip_count n hk
  cutoff_in_range := A.cutoff_in_range
  mark_count := A.mark_count

/-- **The rational-good thin-pair fraction from the aggregate.** -/
theorem thin_pair_fraction (A : ThinAggregate I) (n : ℕ) :
    I.thin n ≤ 1 / cellMesh I.W n :=
  A.toThinPairInputs.thin_pair_fraction n

/-- **Literal replacement of the `thin_pair_fraction` proof field** using the
determinant-level lattice counts and the rational-good cell counts. -/
noncomputable def replaceThinPairFraction (A : ThinAggregate I) : L18_4Inputs :=
  I.replaceThinPairFraction A.toThinPairInputs

/-- The replacement does not change the rational-good deficit. -/
@[simp] theorem replaceThinPairFraction_loss (A : ThinAggregate I) :
    A.replaceThinPairFraction.loss = I.loss := rfl

/-- The replaced input still carries the `D^{-B}` deficit. -/
theorem replaceThinPairFraction_subexpLoss (A : ThinAggregate I) :
    SubexpLoss A.replaceThinPairFraction.loss := by
  rw [A.replaceThinPairFraction_loss]
  exact I.subexpLoss

end ThinAggregate

/-! ## Axiom audit -/

#print axioms det_dvd_of_root
#print axioms level_card_le
#print axioms zero_partner_card_le
#print axioms partnerSet_card_le
#print axioms stripPairSet_card_le
#print axioms ThinAggregate.L_ge_one
#print axioms ThinAggregate.strip_count
#print axioms ThinAggregate.mark_count_arith
#print axioms ThinAggregate.mark_count
#print axioms ThinAggregate.cutoff_in_range
#print axioms ThinAggregate.cutoff_in_range_iff_power_margin
#print axioms ThinAggregate.toThinPairInputs
#print axioms ThinAggregate.thin_pair_fraction
#print axioms ThinAggregate.replaceThinPairFraction
#print axioms ThinAggregate.replaceThinPairFraction_loss
#print axioms ThinAggregate.replaceThinPairFraction_subexpLoss

end Cogentic.RandomizedL18_4


