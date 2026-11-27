import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedL18_4Thin

/-!
# L19.6: thin and small-determinant pair fractions

`Cogentic.RandomizedL19SecondMoment.ThinPairInputs` records the L19.6 pair
fractions `thin` and `smallDet` together with the manuscript's estimates

`thin n ≤ D^{cThin} V^{-etaThin}` and
`smallDet n ≤ D^{cDet} V^{-etaDet}`,

where `W = log V`, `V = exp W`, and `D = exp (scale n)`.

This file supplies those two fields from the determinant-level lattice counts of
`Cogentic.RandomizedL18_4Thin` and from the paper's `O(1/K)` / `V^{-c}` pair
estimates (`research/keybreak-thin-top-pairs.md`,
`research/keybreak-narrow-top-moment.md` §"From pairs to the moment").

## What is proved

1. **The thin-pair field, pointwise and unconditionally.**
   `thin_bound_of_lattice` proves

   `thin n ≤ exp (0 · scale n) · exp (-(1/4) · W n)`

   from `RandomizedL18_4.ThinPairInputs.thin_pair_fraction`.  That theorem is the
   determinant-strip lattice count: one determinant level meets a box of
   diameter `O(V)` in `L₀ = O(1)` points
   (`PrimitiveMark.det_level_card_le`), so at the free cutoff
   `K_det = 4L₀(1 + log V)/ρ · K` the relative close-pair fraction is at most
   `1/K = V^{-1/4}`.  This is the paper's `O(1/K)` estimate with the explicit
   mesh `K = V^{1/4}`.

2. **The small-determinant field, from the three paper contributions.**
   `SmallDetPaperInputs` records the decomposition of the small-determinant
   fraction into

   * distinct pairs with `|det| ≤ V²/K`, fraction `O(1/K) = V^{-ζ}`;
   * same-denominator pairs, fraction `O(1/V)`;
   * the diagonal, fraction `1/R = O(q/V²) = O(V^{-c₀})`,

   exactly the three lines of `research/keybreak-thin-top-pairs.md`
   §"Normalization on a rational-good box" and the combined
   `V^{-min(c₀,1,ζ)+o(1)}` of `research/keybreak-narrow-top-moment.md`.
   `SmallDetPaperInputs.smallDet_eventually_bound` proves the combined exponent
   `min ζ (min 1 c₀)` (with the harmless factor `3` absorbed by
   `scale n ≥ 1`), and `smallDet_subexpLoss` proves the `SubexpLoss` form.

3. **The literal L19.6 structure.**
   `LatticeThinInputs.toThinPairInputs` constructs a
   `RandomizedL19SecondMoment.ThinPairInputs` whose `thin_bound` and
   `smallDet_bound` fields are *proved* from the lattice count, using
   `smallDet ≤ thin` (the union of all close pairs is the L18.4 strip count).
   `LatticePaperThinInputs.toThinPairInputs` does the same with the sharper
   small-determinant exponents, retaining only a finite initial-segment
   bookkeeping hypothesis: the paper's asymptotic constants are chosen large
   enough at the finitely many `n` with `scale n < 1`.  This is the smallest
   residual `Prop` of the sharp route, and it is not a zero-loss assertion.

Both assembled inputs feed the existing L19.6 consequences
(`ThinPairInputs.subexpLoss`, `toSubexpLeaf`, `slot_le`), which are restated here
for the two constructions.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and neither fraction is
set to zero.
-/

namespace Cogentic.RandomizedL19Thin

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment

/-! ## 1. The thin-pair field from the determinant-level lattice count -/

/-- **The thin-pair estimate from the L18.4 determinant-strip count.**

`RandomizedL18_4.ThinPairInputs.thin_pair_fraction` is the lattice covering
count at the free cutoff: one determinant level contributes `L₀ = O(1)` partners
and the cutoff `K_det = 4L₀(1 + log V)/ρ · K` cancels the `+1` and the density
normalization, leaving `thin ≤ 1/K = V^{-1/4}`.  In the `D^{O(1)} V^{-η}` shape
of `RandomizedL19SecondMoment.ThinPairInputs` this is `cThin = 0` and
`etaThin = 1/4`. -/
theorem thin_bound_of_lattice {W thin : ℕ → ℝ}
    (P : Cogentic.RandomizedL18_4.ThinPairInputs W thin) (n : ℕ) :
    thin n ≤ exp (0 * scale n) * exp (-(1 / 4 : ℝ) * W n) := by
  have hfrac := P.thin_pair_fraction n
  have hneg : (1 : ℝ) / Cogentic.RandomizedL18_4.cellMesh W n =
      exp (-(1 / 4 : ℝ) * W n) := by
    rw [Cogentic.RandomizedL18_4.cellMesh, one_div, ← Real.exp_neg]
    congr 1
    ring
  calc
    thin n ≤ 1 / Cogentic.RandomizedL18_4.cellMesh W n := hfrac
    _ = exp (-(1 / 4 : ℝ) * W n) := hneg
    _ = exp (0 * scale n) * exp (-(1 / 4 : ℝ) * W n) := by
      rw [zero_mul, Real.exp_zero, one_mul]

/-! ## 2. The sharp small-determinant reduction

The paper's small-determinant fraction is the sum of three contributions.  The
distinct-pair term is the `O(1/K)` strip count with `K = V^ζ`; the
same-denominator term is `O(1/V)` because a fixed mark has
`1 + 2⌊W_a/q⌋ = O(1 + V/q)` partners and the rational-good mark count is
`R ≍ ρV²/(q(1 + log V))`; the diagonal is `1/R = O(q/V²) = O(V^{-c₀})` by the
fixed power margin `q/V² ≤ V^{-c₀}`.  Their sum is the combined
`V^{-min(c₀,1,ζ)+o(1)}` fraction of
`research/keybreak-narrow-top-moment.md` §"From pairs to the moment". -/

/-- The three normalized contributions to the small-determinant fraction, each
with the paper's own exponent. -/
structure SmallDetPaperInputs (W smallDet : ℕ → ℝ) where
  /-- Distinct-pair contribution with `|det| ≤ V²/K`. -/
  distinct : ℕ → ℝ
  /-- Same-denominator contribution. -/
  sameDen : ℕ → ℝ
  /-- Diagonal contribution. -/
  diag : ℕ → ℝ
  /-- The distinct contribution is a nonnegative fraction. -/
  distinct_nonneg : ∀ n, 0 ≤ distinct n
  /-- The same-denominator contribution is a nonnegative fraction. -/
  sameDen_nonneg : ∀ n, 0 ≤ sameDen n
  /-- The diagonal contribution is a nonnegative fraction. -/
  diag_nonneg : ∀ n, 0 ≤ diag n
  /-- **The pair decomposition.**  Every small-determinant pair is distinct,
  same-denominator, or diagonal. -/
  pair_split : ∀ n, smallDet n = distinct n + sameDen n + diag n
  /-- `log V ≥ 0`. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- Exponent of the distinct-pair envelope. -/
  cDistinct : ℝ
  /-- Determinant cutoff exponent `ζ`: the strip is `|det| ≤ V²/V^ζ`. -/
  etaDistinct : ℝ
  /-- The determinant cutoff exponent is genuine. -/
  etaDistinct_pos : 0 < etaDistinct
  /-- **Distinct small-determinant pairs** (`O(1/K)`, KB G.15): the fraction is at
  most `D^{cDistinct} V^{-ζ}`. -/
  distinct_bound : ∀ n,
    distinct n ≤ exp (cDistinct * scale n) * exp (-etaDistinct * W n)
  /-- Exponent of the same-denominator envelope. -/
  cSame : ℝ
  /-- Same-denominator decay exponent, `1` in the paper. -/
  etaSame : ℝ
  /-- The same-denominator decay is genuine. -/
  etaSame_pos : 0 < etaSame
  /-- **Same-denominator pairs** (`O(1/V)`): the fraction is at most
  `D^{cSame} V^{-etaSame}`. -/
  sameDen_bound : ∀ n,
    sameDen n ≤ exp (cSame * scale n) * exp (-etaSame * W n)
  /-- Exponent of the diagonal envelope. -/
  cDiag : ℝ
  /-- Diagonal decay exponent `c₀` from `q/V² ≤ V^{-c₀}`. -/
  etaDiag : ℝ
  /-- The diagonal decay is genuine. -/
  etaDiag_pos : 0 < etaDiag
  /-- **Diagonal pairs** (`1/R ≪ q/V² ≤ V^{-c₀}`): the fraction is at most
  `D^{cDiag} V^{-c₀}`. -/
  diag_bound : ∀ n,
    diag n ≤ exp (cDiag * scale n) * exp (-etaDiag * W n)

namespace SmallDetPaperInputs

variable {W smallDet : ℕ → ℝ} (S : SmallDetPaperInputs W smallDet)

/-- The combined decay exponent `min ζ (min 1 c₀)`. -/
noncomputable def eta : ℝ := min (min S.etaDistinct S.etaSame) S.etaDiag

/-- The combined polynomial exponent before the factor-`3` absorption. -/
noncomputable def cMax : ℝ := max (max S.cDistinct S.cSame) S.cDiag

/-- The combined polynomial exponent after absorbing the three-term union bound. -/
noncomputable def c : ℝ := S.cMax + Real.log 3

/-- The combined decay exponent is genuine. -/
theorem eta_pos : 0 < S.eta :=
  lt_min (lt_min S.etaDistinct_pos S.etaSame_pos) S.etaDiag_pos

theorem eta_le_distinct : S.eta ≤ S.etaDistinct :=
  le_trans (min_le_left _ _) (min_le_left _ _)

theorem eta_le_same : S.eta ≤ S.etaSame :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem eta_le_diag : S.eta ≤ S.etaDiag := min_le_right _ _

theorem cDistinct_le_cMax : S.cDistinct ≤ S.cMax :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem cSame_le_cMax : S.cSame ≤ S.cMax :=
  le_trans (le_max_right S.cDistinct S.cSame)
    (le_max_left (max S.cDistinct S.cSame) S.cDiag)

theorem cDiag_le_cMax : S.cDiag ≤ S.cMax := le_max_right _ _

theorem cMax_le_c : S.cMax ≤ S.c := by
  unfold c
  have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  linarith

/-- Monotonicity of the `exp (c · scale) · exp (-η · W)` envelope: increasing the
polynomial exponent and decreasing the decay exponent can only increase it,
provided `scale n ≥ 0` and `W n ≥ 0`. -/
theorem envelope_mono {c c' η η' : ℝ} {n : ℕ}
    (hcc : c ≤ c') (hη : η' ≤ η) (hs : 0 ≤ scale n) (hW : 0 ≤ W n) :
    exp (c * scale n) * exp (-η * W n) ≤
      exp (c' * scale n) * exp (-η' * W n) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : c * scale n ≤ c' * scale n :=
    mul_le_mul_of_nonneg_right hcc hs
  have h2 : -η * W n ≤ -η' * W n := by nlinarith
  linarith

/-- **The three-term union bound at `scale n ≥ 1`.**  Each contribution is at most
`exp (cMax · scale) · exp (-η · W)`; the factor `3` is then absorbed by
`exp (log 3 · scale) ≥ 3`. -/
theorem smallDet_le_of_scale_ge_one {n : ℕ} (hs : 1 ≤ scale n) :
    smallDet n ≤ exp (S.c * scale n) * exp (-S.eta * W n) := by
  have hscale0 : 0 ≤ scale n := by linarith
  have hW := S.W_nonneg n
  have h1 : S.distinct n ≤
      exp (S.cMax * scale n) * exp (-S.eta * W n) :=
    (S.distinct_bound n).trans
      (envelope_mono S.cDistinct_le_cMax S.eta_le_distinct hscale0 hW)
  have h2 : S.sameDen n ≤
      exp (S.cMax * scale n) * exp (-S.eta * W n) :=
    (S.sameDen_bound n).trans
      (envelope_mono S.cSame_le_cMax S.eta_le_same hscale0 hW)
  have h3 : S.diag n ≤
      exp (S.cMax * scale n) * exp (-S.eta * W n) :=
    (S.diag_bound n).trans
      (envelope_mono S.cDiag_le_cMax S.eta_le_diag hscale0 hW)
  have hsum : smallDet n ≤
      3 * (exp (S.cMax * scale n) * exp (-S.eta * W n)) := by
    calc
      smallDet n = S.distinct n + S.sameDen n + S.diag n := S.pair_split n
      _ ≤ exp (S.cMax * scale n) * exp (-S.eta * W n) +
            exp (S.cMax * scale n) * exp (-S.eta * W n) +
              exp (S.cMax * scale n) * exp (-S.eta * W n) := by
        linarith [h1, h2, h3]
      _ = 3 * (exp (S.cMax * scale n) * exp (-S.eta * W n)) := by ring
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hthree : (3 : ℝ) ≤ exp (Real.log 3 * scale n) := by
    calc
      (3 : ℝ) = exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ exp (Real.log 3 * scale n) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hE : 0 ≤ exp (S.cMax * scale n) * exp (-S.eta * W n) := by positivity
  calc
    smallDet n ≤ 3 * (exp (S.cMax * scale n) * exp (-S.eta * W n)) := hsum
    _ ≤ exp (Real.log 3 * scale n) *
          (exp (S.cMax * scale n) * exp (-S.eta * W n)) :=
      mul_le_mul_of_nonneg_right hthree hE
    _ = exp (S.c * scale n) * exp (-S.eta * W n) := by
      have harg : Real.log 3 * scale n + S.cMax * scale n =
          S.c * scale n := by
        unfold c
        ring
      calc
        exp (Real.log 3 * scale n) *
            (exp (S.cMax * scale n) * exp (-S.eta * W n))
            = (exp (Real.log 3 * scale n) * exp (S.cMax * scale n)) *
                exp (-S.eta * W n) := by ring
        _ = exp (Real.log 3 * scale n + S.cMax * scale n) *
              exp (-S.eta * W n) := by rw [← Real.exp_add]
        _ = exp (S.c * scale n) * exp (-S.eta * W n) := by rw [harg]

/-- **The small-determinant estimate from the three paper contributions**, in the
eventual `D^{O(1)} V^{-η}` shape. -/
theorem smallDet_eventually_bound (S : SmallDetPaperInputs W smallDet) :
    ∀ᶠ n : ℕ in atTop,
      smallDet n ≤ exp (S.c * scale n) * exp (-S.eta * W n) := by
  filter_upwards [scale_grows.eventually_ge_atTop (1 : ℝ)] with n hs
  exact S.smallDet_le_of_scale_ge_one hs

/-- **The L19.6 small-determinant `SubexpLoss`.** -/
theorem smallDet_subexpLoss (S : SmallDetPaperInputs W smallDet)
    (hWdom : DominatesScale W) :
    SubexpLoss smallDet :=
  subexpLoss_of_eventually_le (SmallDetPaperInputs.smallDet_eventually_bound S)
    (subexpLoss_exp_mul_exp_neg hWdom (SmallDetPaperInputs.eta_pos S))

/-- **The pointwise small-determinant estimate.**  The only extra hypothesis is
the finite initial-segment bookkeeping `scale n < 1 → ...`; for all larger `n`
the three paper estimates give the bound. -/
theorem smallDet_bound_pointwise (S : SmallDetPaperInputs W smallDet)
    (hprefix : ∀ n : ℕ, scale n < 1 →
      smallDet n ≤ exp (S.c * scale n) * exp (-S.eta * W n)) :
    ∀ n : ℕ, smallDet n ≤ exp (S.c * scale n) * exp (-S.eta * W n) := by
  intro n
  by_cases hn : scale n < 1
  · exact hprefix n hn
  · exact S.smallDet_le_of_scale_ge_one (by linarith)

/-- The small-determinant fraction is nonnegative, from the decomposition. -/
theorem smallDet_nonneg (S : SmallDetPaperInputs W smallDet) (n : ℕ) :
    0 ≤ smallDet n := by
  rw [S.pair_split n]
  exact add_nonneg (add_nonneg (S.distinct_nonneg n) (S.sameDen_nonneg n))
    (S.diag_nonneg n)

end SmallDetPaperInputs

/-! ## 3. The fully proved coarse route: `smallDet` is a sub-fraction of `thin` -/

/-- The L18.4 thin-pair count bounds the whole strip `|det| ≤ V²/K`, hence also
every nonnegative sub-fraction such as the small-determinant pairs.  This route
gives both L19.6 fields with the same explicit exponent `η = 1/4` and needs no
new paper estimate beyond the determinant-level lattice count. -/
structure LatticeThinInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- The L19.6 thin fraction. -/
  thin : ℕ → ℝ
  /-- The L19.6 small-determinant fraction. -/
  smallDet : ℕ → ℝ
  /-- The L18.4 determinant-strip count at the free cutoff `K = V^{1/4}`. -/
  lattice : Cogentic.RandomizedL18_4.ThinPairInputs W thin
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The thin fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The small-determinant fraction is nonnegative. -/
  smallDet_nonneg : ∀ n, 0 ≤ smallDet n
  /-- The small-determinant pairs are a sub-collection of the close pairs counted
  by `thin`. -/
  smallDet_le_thin : ∀ n, smallDet n ≤ thin n

namespace LatticeThinInputs

variable (S : LatticeThinInputs)

/-- **The L19.6 `ThinPairInputs` with both bound fields proved from the lattice
count.**  The thin field is `thin_bound_of_lattice`; the small-determinant field
is its monotone consequence `smallDet ≤ thin`. -/
noncomputable def toThinPairInputs :
    Cogentic.RandomizedL19SecondMoment.ThinPairInputs where
  W := S.W
  W_nonneg := S.lattice.W_nonneg
  W_dominates := S.W_dominates
  thin := S.thin
  smallDet := S.smallDet
  thin_nonneg := S.thin_nonneg
  smallDet_nonneg := S.smallDet_nonneg
  cThin := 0
  etaThin := 1 / 4
  etaThin_pos := by norm_num
  cDet := 0
  etaDet := 1 / 4
  etaDet_pos := by norm_num
  thin_bound := fun n => thin_bound_of_lattice S.lattice n
  smallDet_bound := fun n =>
    (S.smallDet_le_thin n).trans (thin_bound_of_lattice S.lattice n)

/-- The proved thin-pair field of the constructed L19.6 structure. -/
theorem thin_bound (n : ℕ) :
    S.thin n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * S.W n) :=
  S.toThinPairInputs.thin_bound n

/-- The proved small-determinant field of the constructed L19.6 structure. -/
theorem smallDet_bound (n : ℕ) :
    S.smallDet n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * S.W n) :=
  S.toThinPairInputs.smallDet_bound n

/-- The L19.6 `SubexpLoss` from the coarse lattice route. -/
theorem subexpLoss : SubexpLoss S.toThinPairInputs.loss :=
  S.toThinPairInputs.subexpLoss

/-- The L19.6 `SubexpLeaf` from the coarse lattice route. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  S.toThinPairInputs.toSubexpLeaf

/-- The L19.6 C5 slot from the coarse lattice route. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    S.toThinPairInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toThinPairInputs.slot_le

end LatticeThinInputs

/-! ## 4. The sharp route: the paper's three exponents -/

/-- The sharp L19.6 assembly: the L18.4 lattice count supplies `thin`, and the
three paper contributions supply `smallDet`.  The field `smallDet_prefix` is the
finite initial-segment bookkeeping only; it is the smallest residual proposition
of this route and is not a zero-loss assertion. -/
structure LatticePaperThinInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- The L19.6 thin fraction. -/
  thin : ℕ → ℝ
  /-- The L19.6 small-determinant fraction. -/
  smallDet : ℕ → ℝ
  /-- The L18.4 determinant-strip count. -/
  lattice : Cogentic.RandomizedL18_4.ThinPairInputs W thin
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The thin fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The three paper contributions to `smallDet`. -/
  paper : SmallDetPaperInputs W smallDet
  /-- Finite initial-segment bookkeeping for the sharp exponents. -/
  smallDet_prefix : ∀ n : ℕ, scale n < 1 →
    smallDet n ≤ exp (paper.c * scale n) * exp (-paper.eta * W n)

namespace LatticePaperThinInputs

variable (S : LatticePaperThinInputs)

/-- **The sharp L19.6 `ThinPairInputs`.**  The thin bound is again the L18.4
lattice count (`η = 1/4`); the small-determinant bound is the three-term paper
estimate with `η = min ζ (min 1 c₀)`. -/
noncomputable def toThinPairInputs :
    Cogentic.RandomizedL19SecondMoment.ThinPairInputs where
  W := S.W
  W_nonneg := S.lattice.W_nonneg
  W_dominates := S.W_dominates
  thin := S.thin
  smallDet := S.smallDet
  thin_nonneg := S.thin_nonneg
  smallDet_nonneg := SmallDetPaperInputs.smallDet_nonneg S.paper
  cThin := 0
  etaThin := 1 / 4
  etaThin_pos := by norm_num
  cDet := S.paper.c
  etaDet := S.paper.eta
  etaDet_pos := S.paper.eta_pos
  thin_bound := fun n => thin_bound_of_lattice S.lattice n
  smallDet_bound :=
    SmallDetPaperInputs.smallDet_bound_pointwise S.paper S.smallDet_prefix

/-- The proved thin-pair field of the sharp L19.6 structure. -/
theorem thin_bound (n : ℕ) :
    S.thin n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * S.W n) :=
  S.toThinPairInputs.thin_bound n

/-- The proved small-determinant field of the sharp L19.6 structure, with the
paper's combined exponent `min ζ (min 1 c₀)`. -/
theorem smallDet_bound (n : ℕ) :
    S.smallDet n ≤ exp (S.paper.c * scale n) * exp (-S.paper.eta * S.W n) :=
  S.toThinPairInputs.smallDet_bound n

/-- The L19.6 `SubexpLoss` from the sharp route. -/
theorem subexpLoss : SubexpLoss S.toThinPairInputs.loss :=
  S.toThinPairInputs.subexpLoss

/-- The L19.6 `SubexpLeaf` from the sharp route. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  S.toThinPairInputs.toSubexpLeaf

/-- The L19.6 C5 slot from the sharp route. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    S.toThinPairInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toThinPairInputs.slot_le

end LatticePaperThinInputs

/-! ## Axiom audit -/

#print axioms thin_bound_of_lattice
#print axioms SmallDetPaperInputs.eta_pos
#print axioms SmallDetPaperInputs.envelope_mono
#print axioms SmallDetPaperInputs.smallDet_le_of_scale_ge_one
#print axioms SmallDetPaperInputs.smallDet_eventually_bound
#print axioms SmallDetPaperInputs.smallDet_subexpLoss
#print axioms SmallDetPaperInputs.smallDet_bound_pointwise
#print axioms SmallDetPaperInputs.smallDet_nonneg
#print axioms LatticeThinInputs.toThinPairInputs
#print axioms LatticeThinInputs.thin_bound
#print axioms LatticeThinInputs.smallDet_bound
#print axioms LatticeThinInputs.subexpLoss
#print axioms LatticeThinInputs.toSubexpLeaf
#print axioms LatticeThinInputs.slot_le
#print axioms LatticePaperThinInputs.toThinPairInputs
#print axioms LatticePaperThinInputs.thin_bound
#print axioms LatticePaperThinInputs.smallDet_bound
#print axioms LatticePaperThinInputs.subexpLoss
#print axioms LatticePaperThinInputs.toSubexpLeaf
#print axioms LatticePaperThinInputs.slot_le

end Cogentic.RandomizedL19Thin
