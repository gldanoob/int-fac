import Cogentic.RandomizedL18_4
import Mathlib.Data.Int.CardIntervalMod

/-!
# L18.4: the rational-good thin-pair fraction

`RandomizedL18_4.L18_4Inputs.thin_pair_fraction` is the hypothesis

`thin n ≤ 1 / cellMesh W n`,

where `cellMesh W n = exp (W n / 4) = V^{1/4}` is the rational-good cell mesh.
In the manuscript (KeyBreak Lemma G.3 p.107, G.15; see
`research/keybreak-balanced-ideal-pair-audit.md` §Denominator and
`research/keybreak-thin-top-pairs.md` §Determinant levels and repeated
denominators) this is a count of pairs of primitive marks `P = (w, b)` in a
root lattice `w ≡ s b (mod q)` whose determinant

`det (P₁, P₂) = w₁ b₂ - w₂ b₁`

lies in the strip `|det| ≪ V²/K`.

This file does not assume `thin_pair_fraction`.  It

1. **Proves the lattice-line structure of one determinant level**
   (`PrimitiveMark.det_level_step`): for a primitive mark `P = (a, b)`, two
   integer points on the same level `a b' - a' b = D` differ by an integer
   multiple of `P`.  Hence the solutions on one level are spaced by
   `‖P‖ ≍ V`, at most `L₀ = 1 + ⌊diam/‖P‖⌋ = O(1)` of them lie in the box, and
   two distinct marks on one level cannot share a denominator.  This is the
   arithmetic content of "determinant levels and repeated denominators".
   The box count is proved, not assumed: `PrimitiveMark.card_modEq_le` counts
   one residue class in an integer interval and
   `PrimitiveMark.det_level_card_le` gives at most `(hi - lo)/b + 1` marks of
   one level in a denominator interval `(lo, hi]`.  With `hi - lo = O(V)` and
   `b ≍ V` this is the `O(1)` per-level bound.

2. **Isolates the two counting estimates** in `ThinPairInputs`:

   * `strip_count`: at determinant cutoff `k` the number of ordered thin pairs
     is at most `(1 + 2 L₀ V²/(q k)) · R`, the manuscript's
     `1 + 2L₀⌊V²/(qK)⌋` partners per mark summed over the `R` retained marks.
   * `mark_count`: the rational-good cell retains `R ≥ ρ V²/(q (1 + log V))`
     marks (`research/keybreak-thin-top-pairs.md` §Which top rational count
     applies).

   In addition `cutoff_in_range` records that the chosen determinant cutoff is
   still inside the strip range, `2 L₀ V²/(q K_det) ≥ 1`; with `K_det` a fixed
   polylogarithmic multiple of the mesh this is the paper's fixed power margin
   `q/V² ≤ V^{-c₀}` with `c₀ > 1/4`.

3. **Chooses the determinant cutoff freely**, as the paper stresses: it "is
   independent of the mesh size used to obtain rational-good events"
   (`research/keybreak-thin-top-pairs.md` §Normalization on a rational-good
   box).  Taking

   `K_det = 4 L₀ (1 + log V) / ρ · K`

   absorbs both the `+1` of the strip count and the `1/ρ` normalization loss,
   and gives the exact relative thin-pair fraction `≤ 1/K`, not merely
   `O(1/K)`.  This is `ThinPairInputs.thin_pair_fraction`.

4. **Replaces the field** in `L18_4Inputs` (`replaceThinPairFraction`) without
   changing the rational-good deficit `loss`, since `loss` only reads data
   fields.

Nothing here is a `sorry`, an `axiom`, or a `native_decide`, and `thin` is
never set to zero: the count `thinPairs`, the mark count `R`, the density `ρ`
and the per-level bound `L₀` all remain explicit, and the conclusion is derived
from the strip count.
-/

namespace Cogentic.RandomizedL18_4

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Finset

/-! ## 1. The lattice line of a determinant level -/

namespace PrimitiveMark

/-- **A determinant level is a lattice line.**  Let `P = (a, b)` be primitive and
fix a determinant level `D`: `a b₁ - a₁ b = D` and `a b₂ - a₂ b = D`.  Then the
two solutions differ by an integer multiple `t` of `P`:
`a₂ = a₁ + t a`, `b₂ = b₁ + t b`.

This is the arithmetic form of `research/keybreak-thin-top-pairs.md`
§Determinant levels: "any two integer solutions to one determinant level differ
by an integer multiple of `P`, since `gcd(a, b) = 1`". -/
theorem det_level_step {a b a₁ b₁ a₂ b₂ D : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (h₁ : a * b₁ - a₁ * b = D) (h₂ : a * b₂ - a₂ * b = D) :
    ∃ t : ℤ, a₂ = a₁ + t * a ∧ b₂ = b₁ + t * b := by
  have hsub : a * (b₂ - b₁) = b * (a₂ - a₁) := by linarith
  have hdvd : b ∣ b₂ - b₁ := by
    have h : b ∣ a * (b₂ - b₁) := ⟨a₂ - a₁, hsub⟩
    exact hcop.symm.dvd_of_dvd_mul_left h
  obtain ⟨t, ht⟩ := hdvd
  have ht' : b₂ - b₁ = b * t := ht
  have hmul : b * (a * t) = b * (a₂ - a₁) := by
    calc
      b * (a * t) = a * (b * t) := by ring
      _ = a * (b₂ - b₁) := by rw [ht']
      _ = b * (a₂ - a₁) := hsub
  have hta : a * t = a₂ - a₁ := mul_left_cancel₀ hb hmul
  exact ⟨t, by linarith, by linarith⟩

/-- **The zero determinant level contains only `±P`.**  A primitive mark
`P = (a, b)` admits `a b' - a' b = 0` for an integer point `(a', b')` only when
`(a', b')` is an integer multiple of `P`.  Since the box keeps positive
denominators, the only primitive partner on the diagonal is `P` itself, which is
the `1` in the strip count `1 + 2L₀⌊V²/(qK)⌋`. -/
theorem det_level_zero {a b a' b' : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (h : a * b' - a' * b = 0) :
    ∃ t : ℤ, a' = t * a ∧ b' = t * b := by
  obtain ⟨t, ha, hb'⟩ :=
    det_level_step (D := 0) (a₁ := 0) (b₁ := 0) hcop hb (by ring) h
  exact ⟨t, by simpa using ha, by simpa using hb'⟩

/-- **Distinct marks on one determinant level have distinct denominators.**
Two solutions on one level with the same denominator coincide.  This is the
"repeated denominators" statement of `research/keybreak-thin-top-pairs.md`: on a
fixed level the denominator determines the mark. -/
theorem det_level_den_eq {a b a₁ b₁ a₂ b₂ D : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (h₁ : a * b₁ - a₁ * b = D) (h₂ : a * b₂ - a₂ * b = D) (hbb : b₂ = b₁) :
    a₂ = a₁ := by
  obtain ⟨t, ha, hb'⟩ := det_level_step hcop hb h₁ h₂
  rw [hbb] at hb'
  have htb : t * b = 0 := by linarith
  rcases mul_eq_zero.mp htb with ht | hb0
  · subst ht
    linarith
  · exact absurd hb0 hb

/-- **Distinct marks on one determinant level are spaced by `‖P‖ = |b|`.**  For
two different integer points on the level `D`, the denominators differ by at
least `b` in absolute value.  Consequently a box of denominator diameter `H`
meets one level in at most `1 + H/b` points. -/
theorem det_level_snd_dist {a b a₁ b₁ a₂ b₂ D : ℤ} (hcop : IsCoprime a b) (hb : 0 < b)
    (h₁ : a * b₁ - a₁ * b = D) (h₂ : a * b₂ - a₂ * b = D)
    (hne : a₂ ≠ a₁ ∨ b₂ ≠ b₁) : b ≤ |b₂ - b₁| := by
  obtain ⟨t, ha, hb'⟩ := det_level_step hcop hb.ne' h₁ h₂
  have ht : t ≠ 0 := by
    rintro rfl
    rcases hne with h | h
    · exact h (by linarith)
    · exact h (by linarith)
  have hb2 : b₂ - b₁ = t * b := by linarith
  rw [hb2, abs_mul, abs_of_pos hb]
  have h1 : (1 : ℤ) ≤ |t| := Int.one_le_abs ht
  nlinarith [hb, h1, abs_nonneg t]

/-- **Counting one residue class in a denominator interval.**  A half-open integer
interval `(lo, hi]` contains at most `(hi - lo)/b + 1` integers congruent to a
fixed residue modulo `b`.  This is the elementary count behind the per-level
bound `L₀ = 1 + ⌊diam/‖P‖⌋`: the exact count is
`Int.Ioc_filter_modEq_card`, and the two floor errors cost at most one extra
element. -/
theorem card_modEq_le {r v : ℤ} (hr : 0 < r) {lo hi : ℤ} (hlohi : lo ≤ hi) :
    ((#{x ∈ Ioc lo hi | x ≡ v [ZMOD r]} : ℕ) : ℝ) ≤
      ((hi - lo : ℤ) : ℝ) / (r : ℝ) + 1 := by
  have hc : ((#{x ∈ Ioc lo hi | x ≡ v [ZMOD r]} : ℕ) : ℝ) =
      ((max (⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋) (0 : ℤ) : ℤ) :
        ℝ) := by
    have h := Int.Ioc_filter_modEq_card lo hi hr v
    exact_mod_cast h
  rw [hc]
  have hmain :
      ((max (⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋) (0 : ℤ) : ℤ) :
          ℚ) ≤ ((hi - lo : ℤ) : ℚ) / (r : ℚ) + 1 := by
    have hY : (0 : ℚ) ≤ ((hi - lo : ℤ) : ℚ) / (r : ℚ) + 1 := by
      have hnn : (0 : ℚ) ≤ ((hi - lo : ℤ) : ℚ) := by
        exact_mod_cast (sub_nonneg.mpr hlohi)
      have hrq : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
      have : (0 : ℚ) ≤ ((hi - lo : ℤ) : ℚ) / (r : ℚ) := div_nonneg hnn hrq.le
      linarith
    have hX :
        ((⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) ≤
          ((hi - lo : ℤ) : ℚ) / (r : ℚ) + 1 := by
      have hcast :
          ((⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) =
            ((⌊((hi : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) -
              ((⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) := by
        push_cast
        ring
      rw [hcast]
      have heq :
          ((hi : ℚ) - v) / (r : ℚ) - (((lo : ℚ) - v) / (r : ℚ)) =
            ((hi - lo : ℤ) : ℚ) / (r : ℚ) := by
        push_cast
        field_simp
        ring
      have hA : ((⌊((hi : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) ≤
          ((hi : ℚ) - v) / (r : ℚ) := Int.floor_le _
      have hB : ((lo : ℚ) - v) / (r : ℚ) - 1 <
          ((⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) := Int.sub_one_lt_floor _
      have h1 : ((⌊((hi : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) -
            ((⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ) <
          ((hi : ℚ) - v) / (r : ℚ) - (((lo : ℚ) - v) / (r : ℚ)) + 1 := by
        linarith
      rw [heq] at h1
      linarith
    calc
      ((max (⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋) (0 : ℤ) : ℤ) :
          ℚ) =
          max (((⌊((hi : ℚ) - v) / (r : ℚ)⌋ - ⌊((lo : ℚ) - v) / (r : ℚ)⌋ : ℤ) : ℚ))
            0 := by
        push_cast
        ring
      _ ≤ _ := max_le hX hY
  exact_mod_cast hmain

/-- **A determinant level meets a denominator interval in at most `1 + H/b`
points.**  The `b`-coordinates of the marks on one level are distinct and all
congruent modulo `b` (`det_level_step`), so a box whose denominators lie in
`(lo, hi]` meets the level in at most `(hi - lo)/b + 1` points.  This is the
`L₀ = 1 + ⌊diam/‖P‖⌋ = O(1)` of `research/keybreak-thin-top-pairs.md`: with
`hi - lo = O(V)` and `b ≍ V`, one level contributes `O(1)` partners. -/
theorem det_level_card_le {a b : ℤ} (hcop : IsCoprime a b) (hb : 0 < b)
    {D : ℤ} {S : Finset (ℤ × ℤ)}
    (hmem : ∀ p ∈ S, a * p.2 - p.1 * b = D)
    {lo hi : ℤ} (hlohi : lo ≤ hi) (hbox : ∀ p ∈ S, lo < p.2 ∧ p.2 ≤ hi) :
    (S.card : ℝ) ≤ ((hi - lo : ℤ) : ℝ) / (b : ℝ) + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hnn : (0 : ℝ) ≤ ((hi - lo : ℤ) : ℝ) := by
      exact_mod_cast (sub_nonneg.mpr hlohi)
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have : (0 : ℝ) ≤ ((hi - lo : ℤ) : ℝ) / (b : ℝ) := div_nonneg hnn hbR.le
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · obtain ⟨p₀, hp₀⟩ := hne
    have hmod : ∀ p ∈ S, p.2 ≡ p₀.2 [ZMOD b] := by
      intro p hp
      obtain ⟨t, -, hb'⟩ := det_level_step hcop hb.ne' (hmem p hp) (hmem p₀ hp₀)
      exact Int.modEq_iff_dvd.mpr ⟨t, by rw [hb']; ring⟩
    have hinj : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q := by
      intro p hp q hq hpq
      have hfst := det_level_den_eq hcop hb.ne' (hmem p hp) (hmem q hq) hpq.symm
      exact Prod.ext hfst.symm hpq
    let F : Finset ℤ := {x ∈ Ioc lo hi | x ≡ p₀.2 [ZMOD b]}
    have hsub : S.image Prod.snd ⊆ F := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨(hbox p hp).1, (hbox p hp).2⟩, hmod p hp⟩
    have hcard : (S.card : ℝ) ≤ (F.card : ℝ) := by
      have hT : (S.image Prod.snd).card = S.card :=
        Finset.card_image_of_injOn hinj
      rw [← hT]
      exact_mod_cast Finset.card_le_card hsub
    have hF : (F.card : ℝ) ≤ ((hi - lo : ℤ) : ℝ) / (b : ℝ) + 1 :=
      card_modEq_le hb hlohi
    exact hcard.trans hF

end PrimitiveMark

/-! ## 2. The free determinant cutoff -/

/-- The determinant-strip cutoff used for thin pairs.  It is a fixed
polylogarithmic multiple `4 L₀ (1 + log V)/ρ` of the rational-good mesh, chosen
so that the strip count's `+1`, the per-level factor `2L₀` and the density
normalization `1/ρ` all cancel exactly. -/
noncomputable def thinCutoff (W : ℕ → ℝ) (L dens : ℕ → ℝ) (n : ℕ) : ℝ :=
  4 * L n * (1 + W n) / dens n * cellMesh W n

/-! ## 3. The two counting estimates -/

/-- **The remaining paper-level content of `thin_pair_fraction`.**

`W = log V`, `thin` the relative thin-pair fraction of `L18_4Inputs`, and:

* `q` is the geometric modulus of the root lattice `w ≡ s b (mod q)`;
* `dens` is the reference density `ρ` of the numerator progression (`0 < ρ ≤ 1`);
* `R` is the number of retained primitive marks on the rational-good cell;
* `L` is the per-determinant-level solution bound `L₀ = 1 + ⌊diam/‖P‖⌋ ≥ 1`;
* `thinPairs n k` is the number of ordered pairs `(P, P')` of retained marks with
  `|det(P, P')| ≤ V²/k`, the diagonal included.

The estimates are:

* `strip_count` — the determinant-strip / lattice covering count.  A box of
  diameter `O(V)` meets one determinant level in `L₀ = O(1)` points
  (`PrimitiveMark.det_level_card_le`), and `Δ ∈ qℤ` with `|Δ| ≤ V²/k` leaves
  `⌊V²/(qk)⌋` levels, so each mark has at most `1 + 2L₀⌊V²/(qk)⌋` partners.
  The floors are discarded upward.
* `mark_count` — the rational-good mark count `R ≥ ρ V²/(q (1 + W))`.
* `cutoff_in_range` — the strip with cutoff `thinCutoff` contains at least one
  level: `1 ≤ 2L₀ V²/(q K_det)`.  With `K_det` a polylogarithmic multiple of the
  mesh this is the paper's fixed power margin `q/V² ≤ V^{-c₀}`, `c₀ > 1/4`.
* `thin_le_pairFraction` — `thin` is the normalized fraction of ordered thin
  pairs among the `R²` pairs of the cell.

None of these is the conclusion, and none is zero. -/
structure ThinPairInputs (W thin : ℕ → ℝ) where
  /-- The geometric modulus of the root lattice. -/
  q : ℕ → ℝ
  /-- The reference density `ρ` of the numerator progression. -/
  dens : ℕ → ℝ
  /-- The number of retained primitive marks on the rational-good cell. -/
  R : ℕ → ℝ
  /-- The per-determinant-level solution bound `L₀`. -/
  L : ℕ → ℝ
  /-- The number of ordered pairs inside the determinant strip of cutoff `k`. -/
  thinPairs : ℕ → ℝ → ℝ
  /-- `log V ≥ 0`. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- The geometric modulus is positive. -/
  q_pos : ∀ n, 0 < q n
  /-- The reference density is positive. -/
  dens_pos : ∀ n, 0 < dens n
  /-- The reference density is a fraction of the numerator interval, so `ρ ≤ 1`. -/
  dens_le_one : ∀ n, dens n ≤ 1
  /-- The cell is nonempty. -/
  R_pos : ∀ n, 0 < R n
  /-- `L₀ = 1 + ⌊diam/‖P‖⌋ ≥ 1`. -/
  L_ge_one : ∀ n, 1 ≤ L n
  /-- The pair count is nonnegative. -/
  thinPairs_nonneg : ∀ n k, 0 ≤ thinPairs n k
  /-- The normalized thin-pair fraction is at most the pair count over `R²`. -/
  thin_le_pairFraction : ∀ n,
    thin n ≤ thinPairs n (thinCutoff W L dens n) / R n ^ 2
  /-- **Determinant-strip / lattice covering count** (KB G.15).  At cutoff `k`
  the number of ordered pairs in the strip `|det| ≤ V²/k` is at most
  `(1 + 2L₀ V²/(qk)) · R`. -/
  strip_count : ∀ n, ∀ k : ℝ, 0 < k →
    thinPairs n k ≤ (1 + 2 * L n * (denomScale W n ^ 2 / (q n * k))) * R n
  /-- **The cutoff is inside the strip range.**  With `K_det` the free
  determinant cutoff, the strip still carries a level:
  `1 ≤ 2L₀ V²/(q K_det)`. -/
  cutoff_in_range : ∀ n,
    1 ≤ 2 * L n * (denomScale W n ^ 2 / (q n * thinCutoff W L dens n))
  /-- **Rational-good mark count.**  The cell retains at least
  `ρ V²/(q (1 + log V))` primitive marks. -/
  mark_count : ∀ n,
    dens n * (denomScale W n ^ 2 / (q n * (1 + W n))) ≤ R n

namespace ThinPairInputs

variable {W thin : ℕ → ℝ}

/-- The free determinant cutoff is positive. -/
theorem thinCutoff_pos (P : ThinPairInputs W thin) (n : ℕ) :
    0 < thinCutoff W P.L P.dens n := by
  have hL : 0 < P.L n := lt_of_lt_of_le zero_lt_one (P.L_ge_one n)
  have hdens := P.dens_pos n
  have hW : 0 < 1 + W n := by linarith [P.W_nonneg n]
  have hK : 0 < cellMesh W n := by unfold cellMesh; exact exp_pos _
  unfold thinCutoff
  positivity

/-- **The cutoff sits above the rational-good mesh.**  Since `L₀ ≥ 1`,
  `ρ ≤ 1` and `log V ≥ 0`, the free determinant cutoff `K_det` is at least the
  cell mesh `K`, so the paper's remark that the geometric cutoff is independent
  of the mesh is realised here with `K_det ≥ K`. -/
theorem cellMesh_le_thinCutoff (P : ThinPairInputs W thin) (n : ℕ) :
    cellMesh W n ≤ thinCutoff W P.L P.dens n := by
  have hK : 0 < cellMesh W n := by unfold cellMesh; exact exp_pos _
  have hL : 1 ≤ P.L n := P.L_ge_one n
  have hdens := P.dens_pos n
  have hdens1 : P.dens n ≤ 1 := P.dens_le_one n
  have hW : 0 ≤ W n := P.W_nonneg n
  have hfactor : 1 ≤ 4 * P.L n * (1 + W n) / P.dens n := by
    have hnum : 4 * P.L n * (1 + W n) ≥ 4 * 1 * 1 := by
      have h1W : 1 ≤ 1 + W n := by linarith
      nlinarith only [hL, h1W, hW]
    -- `1 / ρ ≥ 1`, hence `4 L₀ (1 + W) ≤ 4 L₀ (1 + W) / ρ`
    calc (1 : ℝ) ≤ 1 / P.dens n := by
          rw [le_div_iff₀ hdens]
          linarith
      _ ≤ 4 * P.L n * (1 + W n) / P.dens n := by
          have h4 : (1 : ℝ) ≤ 4 * P.L n * (1 + W n) := by nlinarith only [hnum]
          exact div_le_div_of_nonneg_right h4 hdens.le
  unfold thinCutoff
  exact le_mul_of_one_le_left hK.le hfactor

/-- **Exact cancellation of the free cutoff.**  Evaluating the strip count at
`K_det = 4L₀(1 + log V)/ρ · K` leaves exactly the rational-good scale
`ρ V²/(q(1 + log V))` divided by the mesh `K`. -/
theorem four_mul_strip_scale (P : ThinPairInputs W thin) (n : ℕ) :
    4 * P.L n *
        (denomScale W n ^ 2 / (P.q n * thinCutoff W P.L P.dens n)) =
      P.dens n * (denomScale W n ^ 2 / (P.q n * (1 + W n))) / cellMesh W n := by
  have hq : P.q n ≠ 0 := (P.q_pos n).ne'
  have hL : P.L n ≠ 0 := (lt_of_lt_of_le zero_lt_one (P.L_ge_one n)).ne'
  have hdens : P.dens n ≠ 0 := (P.dens_pos n).ne'
  have hW : (1 + W n) ≠ 0 := by linarith [P.W_nonneg n]
  have hK : cellMesh W n ≠ 0 := by unfold cellMesh; exact (exp_pos _).ne'
  unfold thinCutoff
  field_simp

/-- **`thin_pair_fraction` from the determinant-strip count.**  The `+1` of the
strip count is absorbed because the cutoff is in range (`1 ≤ 2L₀V²/(qK_det)`),
giving `thinPairs ≤ (ρ V²/(q(1+log V))/K) · R`; the rational mark count
`R ≥ ρ V²/(q(1+log V))` then gives `thinPairs ≤ R²/K`, hence
`thin ≤ 1/K`. -/
theorem thin_pair_fraction (P : ThinPairInputs W thin) (n : ℕ) :
    thin n ≤ 1 / cellMesh W n := by
  have hKpos : 0 < cellMesh W n := by unfold cellMesh; exact exp_pos _
  have hcutpos := P.thinCutoff_pos n
  have hstrip := P.strip_count n _ hcutpos
  have hrange := P.cutoff_in_range n
  -- absorb the `+1`: `1 + 2L₀x ≤ 4L₀x`
  have habsorb :
      1 + 2 * P.L n * (denomScale W n ^ 2 / (P.q n * thinCutoff W P.L P.dens n)) ≤
        4 * P.L n * (denomScale W n ^ 2 / (P.q n * thinCutoff W P.L P.dens n)) := by
    linarith only [hrange]
  have hT :
      P.thinPairs n (thinCutoff W P.L P.dens n) ≤
        (P.dens n * (denomScale W n ^ 2 / (P.q n * (1 + W n))) / cellMesh W n) *
          P.R n := by
    calc
      P.thinPairs n (thinCutoff W P.L P.dens n) ≤
          (1 + 2 * P.L n *
            (denomScale W n ^ 2 / (P.q n * thinCutoff W P.L P.dens n))) * P.R n :=
        hstrip
      _ ≤ (4 * P.L n *
            (denomScale W n ^ 2 / (P.q n * thinCutoff W P.L P.dens n))) * P.R n :=
        mul_le_mul_of_nonneg_right habsorb (P.R_pos n).le
      _ = (P.dens n * (denomScale W n ^ 2 / (P.q n * (1 + W n))) / cellMesh W n) *
            P.R n := by rw [P.four_mul_strip_scale n]
  have hR : P.R n ≠ 0 := (P.R_pos n).ne'
  have hK : cellMesh W n ≠ 0 := hKpos.ne'
  calc
    thin n ≤ P.thinPairs n (thinCutoff W P.L P.dens n) / P.R n ^ 2 :=
      P.thin_le_pairFraction n
    _ ≤ ((P.dens n * (denomScale W n ^ 2 / (P.q n * (1 + W n))) / cellMesh W n) *
          P.R n) / P.R n ^ 2 := by
      exact div_le_div_of_nonneg_right hT (sq_nonneg _)
    _ = (P.dens n * (denomScale W n ^ 2 / (P.q n * (1 + W n))) / cellMesh W n) /
          P.R n := by
      field_simp
    _ ≤ (P.R n / cellMesh W n) / P.R n := by
      refine div_le_div_of_nonneg_right ?_ (P.R_pos n).le
      exact div_le_div_of_nonneg_right (P.mark_count n) hKpos.le
    _ = 1 / cellMesh W n := by
      field_simp

end ThinPairInputs

/-! ## 4. Replacement of the `L18_4Inputs.thin_pair_fraction` field -/

namespace L18_4Inputs

variable (I : L18_4Inputs)

/-- **The `thin_pair_fraction` field is reduced to `ThinPairInputs`.**  For any
`L18_4Inputs`, the determinant-strip count, the rational mark count and the
cutoff range imply the inequality assumed by its `thin_pair_fraction` field. -/
theorem thin_pair_fraction_of_inputs (P : ThinPairInputs I.W I.thin) :
    ∀ n, I.thin n ≤ 1 / cellMesh I.W n :=
  fun n => P.thin_pair_fraction n

/-- **Literal replacement of the `thin_pair_fraction` proof field.**  All other
fields of `I` are kept, while `thin_pair_fraction` is now derived from the
counting estimates in `P` instead of being assumed. -/
noncomputable def replaceThinPairFraction (P : ThinPairInputs I.W I.thin) :
    L18_4Inputs :=
  { I with thin_pair_fraction := I.thin_pair_fraction_of_inputs P }

/-- Replacing the thin-pair proof field does not change the rational-good
deficit: `loss` depends only on the data fields, which are untouched. -/
@[simp] theorem replaceThinPairFraction_loss (P : ThinPairInputs I.W I.thin) :
    (I.replaceThinPairFraction P).loss = I.loss := rfl

/-- The replaced input still yields the L18.4 `D^{-B}` deficit bound, because the
deficit is unchanged. -/
theorem replaceThinPairFraction_subexpLoss (P : ThinPairInputs I.W I.thin) :
    SubexpLoss (I.replaceThinPairFraction P).loss := by
  rw [I.replaceThinPairFraction_loss P]
  exact I.subexpLoss

end L18_4Inputs

/-! ## Axiom audit -/

#print axioms PrimitiveMark.det_level_step
#print axioms PrimitiveMark.det_level_zero
#print axioms PrimitiveMark.det_level_den_eq
#print axioms PrimitiveMark.det_level_snd_dist
#print axioms PrimitiveMark.card_modEq_le
#print axioms PrimitiveMark.det_level_card_le
#print axioms ThinPairInputs.thinCutoff_pos
#print axioms ThinPairInputs.cellMesh_le_thinCutoff
#print axioms ThinPairInputs.four_mul_strip_scale
#print axioms ThinPairInputs.thin_pair_fraction
#print axioms L18_4Inputs.thin_pair_fraction_of_inputs
#print axioms L18_4Inputs.replaceThinPairFraction
#print axioms L18_4Inputs.replaceThinPairFraction_loss
#print axioms L18_4Inputs.replaceThinPairFraction_subexpLoss

end Cogentic.RandomizedL18_4
