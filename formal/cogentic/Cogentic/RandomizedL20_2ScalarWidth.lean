import Cogentic.RandomizedL20_2Width

set_option linter.style.haveILetI false

/-!
# L20.2: the paper's band parameters and the residual scalar width

`Cogentic.RandomizedL20_2Width` reduced the L20.2 prime-bin character decay to
the scalar inequality `PaperBandScalarWidthBound`, which still mentions a common
upper endpoint `y` and a common lower endpoint `L` of the paper's bins:

```
exp ((c D log D) / J) * 2K (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ L - 1 .
```

This file instantiates that inequality at the manuscript's own band parameters
and with the actual centred-bin geometry of `RandomizedBalancedStrip`.  The
paper (prime-product grid note) takes

```
δ = log (1 + λ) / (2k),      P = x^(1/k),
H = log (y / P),            J = floor (H / (4δ)),
I_j = [P exp (δ (j - a/k)), P exp (δ (j + 1 - a/k))) ,
```

with `0 < λ ≤ 1`, `k > 0`, and `a` the sum of `k` distinct bin indices in
`0, ..., J - 1`.  The concrete interval bounds used below are

```
paperBandTop    P δ J = P exp (δ J) ,      (right end of the top bin)
paperBandBottom P δ J = P exp (-δ J) .     (left end of the bottom bin)
```

The two geometric facts are proved from `centeredBinEndpoint`:

* `centeredBinEndpoint_le_paperBandTop`: every lower endpoint is at most
  `paperBandTop P δ J`;
* `paperBandBottom_le_centeredBinEndpoint`: every lower endpoint is at least
  `paperBandBottom P δ J`, because `a ≤ kJ`.

Consequently the whole residual condition is the single explicit interval/scale
inequality `PaperBandScaleInequality`:

```
exp (decayExponent c n / J) * (2K) * (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ * paperBandBottom P δ J - 1 .
```

No index, bin, or floor appears in it.  `paperBandScalarWidthBound_of_scaleInequality`
turns it into `PaperBandScalarWidthBound` for the paper's `y` and the explicit
bottom endpoint `paperBandBottom P δ J`, and
`primeBinEnvelopeWidthCore_of_scaleInequality` combines it with the centred-bin
geometry to obtain `PrimeBinEnvelopeWidthCore` on the paper's integer bins.
Finally `primeBinCharacterDecay_of_scaleInequality` composes this with the
existing critical-line supply/GRH reduction, so the manuscript's smooth-character
decay follows from the single scale inequality.

The width is kept as `δ * paperBandBottom P δ J - 1`; the `- 1` is the exact
floor loss and is never dropped.  `paperBandScaleInequality_width_pos` records
that the residual inequality makes the width strictly positive whenever the
envelope constant is positive and `1 < y`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL20_2ScalarWidth

open Filter Real
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_2Decay
open Cogentic.RandomizedL20_2Width
open Cogentic.Randomized

noncomputable section

/-! ## 1. The paper's band parameters -/

/-- The manuscript's bin spacing `δ = log (1 + λ) / (2k)`. -/
noncomputable def paperBandDelta (lam : ℝ) (k : ℕ) : ℝ :=
  Real.log (1 + lam) / (2 * (k : ℝ))

/-- The manuscript's geometric mean `P = x^(1/k)`. -/
noncomputable def paperBandP (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (1 / (k : ℝ))

/-- The manuscript's band height `H = log (y / P)`. -/
noncomputable def paperBandH (y P : ℝ) : ℝ :=
  Real.log (y / P)

/-- The manuscript's number of bins `J = floor (H / (4δ))`. -/
noncomputable def paperBandJ (y P lam : ℝ) (k : ℕ) : ℕ :=
  Nat.floor (paperBandH y P / (4 * paperBandDelta lam k))

/-- The right endpoint of the top bin: a common upper bound for all bin
endpoints. -/
noncomputable def paperBandTop (P δ : ℝ) (J : ℕ) : ℝ :=
  P * Real.exp (δ * (J : ℝ))

/-- The left endpoint of the bottom bin: a common lower bound for all bin
endpoints. -/
noncomputable def paperBandBottom (P δ : ℝ) (J : ℕ) : ℝ :=
  P * Real.exp (δ * (-(J : ℝ)))

theorem paperBandDelta_pos {lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 0 < k) :
    0 < paperBandDelta lam k := by
  unfold paperBandDelta
  have hlog : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact div_pos hlog (by positivity)

theorem paperBandP_pos {x : ℝ} (hx : 0 < x) (k : ℕ) :
    0 < paperBandP x k :=
  Real.rpow_pos_of_pos hx _

theorem paperBandTop_pos {P δ : ℝ} (hP : 0 < P) (J : ℕ) :
    0 < paperBandTop P δ J := by
  unfold paperBandTop
  positivity

theorem paperBandBottom_pos {P δ : ℝ} (hP : 0 < P) (J : ℕ) :
    0 < paperBandBottom P δ J := by
  unfold paperBandBottom
  positivity

/-- The top endpoint is literally the lower real endpoint of the bin of index
`J` when the centering index is zero. -/
theorem paperBandTop_eq_centeredBinEndpoint (P δ : ℝ) (k J : ℕ) :
    paperBandTop P δ J = centeredBinEndpoint P δ 0 k J := by
  unfold paperBandTop centeredBinEndpoint
  norm_num

/-! ## 2. The centred-bin geometry -/

/-- Every lower real endpoint is at most the top endpoint `P exp (δJ)`, since
its exponent is `δ (j - a/k) ≤ δJ`. -/
theorem centeredBinEndpoint_le_paperBandTop {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    {a k J j : ℕ} (hj : j ≤ J) :
    centeredBinEndpoint P δ a k j ≤ paperBandTop P δ J := by
  unfold centeredBinEndpoint paperBandTop
  refine mul_le_mul_of_nonneg_left ?_ hP
  refine Real.exp_le_exp.mpr ?_
  have harg : (j : ℝ) - (a : ℝ) / (k : ℝ) ≤ (J : ℝ) := by
    have hdiv : 0 ≤ (a : ℝ) / (k : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hj' : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
    linarith
  exact mul_le_mul_of_nonneg_left harg hδ

/-- Every lower real endpoint is at least `P exp (-δJ)`, since its exponent is
`δ (j - a/k) ≥ -δJ` whenever `a ≤ kJ`. -/
theorem paperBandBottom_le_centeredBinEndpoint {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    {a k J j : ℕ} (hk : 0 < k) (ha : a ≤ k * J) :
    paperBandBottom P δ J ≤ centeredBinEndpoint P δ a k j := by
  unfold paperBandBottom centeredBinEndpoint
  refine mul_le_mul_of_nonneg_left ?_ hP
  refine Real.exp_le_exp.mpr ?_
  have harg : (-(J : ℝ)) ≤ (j : ℝ) - (a : ℝ) / (k : ℝ) := by
    have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have har : (a : ℝ) ≤ (k : ℝ) * (J : ℝ) := by exact_mod_cast ha
    have hdiv : (a : ℝ) / (k : ℝ) ≤ (J : ℝ) :=
      (div_le_iff₀ hkr).mpr (by simpa [mul_comm] using har)
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  exact mul_le_mul_of_nonneg_left harg hδ

/-- The integer upper endpoint of every paper bin is at most the top endpoint
`P exp (δJ)`. -/
theorem paperBinUpper_le_paperBandTop {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    {a k J j : ℕ} (hj : j < J) :
    (paperBinUpper P δ a k j : ℝ) ≤ paperBandTop P δ J := by
  have hend := centeredBinEndpoint_le_paperBandTop (P := P) (δ := δ)
    (a := a) (k := k) (J := J) (j := j + 1) hP hδ (by omega)
  unfold paperBinUpper centeredBinFloor
  exact (Nat.floor_le (mul_nonneg hP (Real.exp_pos _).le)).trans hend

/-- The index sum of any pattern in `centeredBinPatterns J k a` is at most
`kJ`; this is the `ha` hypothesis used by the lower-endpoint comparison. -/
theorem centeredBinPatterns_sum_le {J k a : ℕ} {s : Finset ℕ}
    (hs : s ∈ centeredBinPatterns J k a) : a ≤ k * J := by
  obtain ⟨hset, hsum⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hset
  have hle : (∑ j ∈ s, j) ≤ s.card * J := by
    calc
      (∑ j ∈ s, j) ≤ ∑ j ∈ s, J := by
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.le_of_lt (Finset.mem_range.mp (hsub hj))
      _ = s.card * J := by simp [Finset.sum_const]
  rw [hsum, hcard] at hle
  exact hle

/-- If the bottom endpoint is at least `2`, every integer upper endpoint is at
least `2` as well. -/
theorem two_le_paperBinUpper_of_two_le_bottom {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    {a k J j : ℕ} (hk : 0 < k) (ha : a ≤ k * J)
    (h2 : 2 ≤ paperBandBottom P δ J) (_hj : j < J) :
    2 ≤ paperBinUpper P δ a k j := by
  have hle := paperBandBottom_le_centeredBinEndpoint (P := P) (δ := δ)
    (a := a) (k := k) (J := J) (j := j + 1) hP hδ hk ha
  have h2' : (2 : ℝ) ≤ centeredBinEndpoint P δ a k (j + 1) := h2.trans hle
  unfold paperBinUpper centeredBinFloor
  exact Nat.le_floor h2'

/-- The upper endpoints satisfy the `hB1` hypothesis of
`primeBinEnvelopeWidthCore_of_scalarBound` once the bottom endpoint is at least
`2`. -/
theorem one_le_paperBinUpper_of_two_le_bottom {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    {a k J j : ℕ} (hk : 0 < k) (ha : a ≤ k * J)
    (h2 : 2 ≤ paperBandBottom P δ J) (hj : j < J) :
    (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ) := by
  have h2' := two_le_paperBinUpper_of_two_le_bottom hP hδ hk ha h2 hj
  exact_mod_cast (show (1 : ℕ) ≤ paperBinUpper P δ a k j by omega)

/-! ## 3. The paper's `J` really puts the top bin below `y` -/

/-- The floor defining `J` satisfies `J δ ≤ H / 4`. -/
theorem paperBandJ_mul_delta_le {y P lam : ℝ} {k : ℕ}
    (hH : 0 ≤ paperBandH y P) (hδ : 0 < paperBandDelta lam k) :
    (paperBandJ y P lam k : ℝ) * paperBandDelta lam k ≤ paperBandH y P / 4 := by
  unfold paperBandJ
  have hq : 0 ≤ paperBandH y P / (4 * paperBandDelta lam k) :=
    div_nonneg hH (by positivity)
  have hfloor :
      (Nat.floor (paperBandH y P / (4 * paperBandDelta lam k)) : ℝ) ≤
        paperBandH y P / (4 * paperBandDelta lam k) :=
    Nat.floor_le hq
  have hmul := mul_le_mul_of_nonneg_right hfloor hδ.le
  calc
    (Nat.floor (paperBandH y P / (4 * paperBandDelta lam k)) : ℝ) *
        paperBandDelta lam k
        ≤ (paperBandH y P / (4 * paperBandDelta lam k)) *
            paperBandDelta lam k := hmul
    _ = paperBandH y P / 4 := by
      field_simp [hδ.ne']

/-- The paper's bin count is positive as soon as the band height covers one
full spacing `4δ`. -/
theorem paperBandJ_pos {y P lam : ℝ} {k : ℕ}
    (h : (1 : ℝ) ≤ paperBandH y P / (4 * paperBandDelta lam k)) :
    0 < paperBandJ y P lam k := by
  unfold paperBandJ
  have h1 : 1 ≤ Nat.floor (paperBandH y P / (4 * paperBandDelta lam k)) :=
    Nat.le_floor (by simpa using h)
  omega

/-- If `δJ ≤ H/4` then the top endpoint is below `y`. -/
theorem paperBandTop_le_of_J_mul_delta_le {P δ y : ℝ} {J : ℕ}
    (hP : 0 < P) (hyP : P ≤ y)
    (hJδ : (J : ℝ) * δ ≤ paperBandH y P / 4) :
    paperBandTop P δ J ≤ y := by
  have hypos : 0 < y := lt_of_lt_of_le hP hyP
  have hHnonneg : 0 ≤ paperBandH y P := by
    unfold paperBandH
    apply Real.log_nonneg
    rw [le_div_iff₀ hP]
    simpa using hyP
  have hexp : Real.exp (δ * (J : ℝ)) ≤ Real.exp (paperBandH y P) := by
    apply Real.exp_le_exp.mpr
    calc
      δ * (J : ℝ) = (J : ℝ) * δ := by ring
      _ ≤ paperBandH y P / 4 := hJδ
      _ ≤ paperBandH y P := by linarith
  calc
    paperBandTop P δ J = P * Real.exp (δ * (J : ℝ)) := rfl
    _ ≤ P * Real.exp (paperBandH y P) := mul_le_mul_of_nonneg_left hexp hP.le
    _ = P * (y / P) := by
      rw [paperBandH, Real.exp_log (div_pos hypos hP)]
    _ = y := by field_simp

/-- For the paper's choice `J = floor (H / (4δ))`, the top bin is below the
smoothness cutoff `y`. -/
theorem paperBandTop_paperBandJ_le {x y lam : ℝ} {k : ℕ}
    (hx : 0 < x) (hPle : paperBandP x k ≤ y)
    (hlam : 0 < lam) (hk : 0 < k) :
    paperBandTop (paperBandP x k) (paperBandDelta lam k)
        (paperBandJ y (paperBandP x k) lam k) ≤ y := by
  have hP : 0 < paperBandP x k := paperBandP_pos hx k
  have hH : 0 ≤ paperBandH y (paperBandP x k) := by
    unfold paperBandH
    apply Real.log_nonneg
    rw [le_div_iff₀ hP]
    simpa using hPle
  have hδ : 0 < paperBandDelta lam k := paperBandDelta_pos hlam hk
  exact paperBandTop_le_of_J_mul_delta_le hP hPle
    (paperBandJ_mul_delta_le hH hδ)

/-! ## 4. The smallest residual interval/scale inequality -/

/-- **The single explicit interval/scale inequality left by the paper's bands.**
All bin indices, floors and centered endpoints have disappeared: only the
common top cutoff `y`, the paper's `P` and `δ`, the bin count `J`, and the
explicit bottom endpoint `paperBandBottom P δ J` remain. -/
def PaperBandScaleInequality (K Ks c : ℝ) (q : ℕ) (n J : ℕ)
    (P δ y : ℝ) : Prop :=
  Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
      (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
    Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
      δ * paperBandBottom P δ J - 1

/-- The scale inequality is exactly `PaperBandScalarWidthBound` at the paper's
top cutoff and the explicit bottom endpoint.  No loss is introduced by passing
to the centred-bin description. -/
theorem paperBandScaleInequality_iff_scalarWidthBound
    {K Ks c : ℝ} {q n J : ℕ} {P δ y : ℝ} :
    PaperBandScaleInequality K Ks c q n J P δ y ↔
      PaperBandScalarWidthBound K Ks c q n J δ y (paperBandBottom P δ J) :=
  Iff.rfl

/-- **The paper's scale inequality gives `PaperBandScalarWidthBound`.** -/
theorem paperBandScalarWidthBound_of_scaleInequality
    {K Ks c : ℝ} {q n J : ℕ} {P δ y : ℝ}
    (h : PaperBandScaleInequality K Ks c q n J P δ y) :
    PaperBandScalarWidthBound K Ks c q n J δ y (paperBandBottom P δ J) :=
  h

/-- The residual inequality makes the width `δ * paperBandBottom P δ J - 1`
nonnegative. -/
theorem paperBandScaleInequality_width_nonneg
    {K Ks c : ℝ} {q n J : ℕ} {P δ y : ℝ}
    (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hy : 1 ≤ y)
    (h : PaperBandScaleInequality K Ks c q n J P δ y) :
    0 ≤ δ * paperBandBottom P δ J - 1 := by
  unfold PaperBandScaleInequality at h
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hbase : 0 ≤ 1 + Real.log (3 * (q : ℝ) * y) := by
    have h3 : 1 ≤ 3 * (q : ℝ) * y := by nlinarith only [hqr, hy]
    have hlog : 0 ≤ Real.log (3 * (q : ℝ) * y) := Real.log_nonneg h3
    linarith
  have henv :
      0 ≤ Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
          (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y := by
    positivity
  have hleft :
      0 ≤ Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
          (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
        Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y := by
    exact add_nonneg (mul_nonneg henv hlogy) (by positivity)
  linarith

/-- If the envelope constant is positive and `1 < y`, the width supplied by the
residual scale inequality is strictly positive.  The `- 1` is retained. -/
theorem paperBandScaleInequality_width_pos
    {K Ks c : ℝ} {q n J : ℕ} {P δ y : ℝ}
    (hK : 0 < K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hy : 1 < y)
    (h : PaperBandScaleInequality K Ks c q n J P δ y) :
    0 < δ * paperBandBottom P δ J - 1 := by
  unfold PaperBandScaleInequality at h
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hsqrty : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have henv :
      0 < Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
          (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y := by
    have hbase : 0 < 1 + Real.log (3 * (q : ℝ) * y) := by
      have h3 : 1 ≤ 3 * (q : ℝ) * y := by nlinarith only [hqr, hy]
      have hlog : 0 ≤ Real.log (3 * (q : ℝ) * y) := Real.log_nonneg h3
      linarith
    positivity
  have hsupply :
      0 ≤ Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y := by
    positivity
  have hleft :
      0 < Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
          (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
        Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y :=
    add_pos_of_pos_of_nonneg henv hsupply
  linarith

/-! ## 5. From the scale inequality to the paper's integer bins -/

/-- **`PrimeBinEnvelopeWidthCore` on the paper's bins from the scale
inequality.**  The geometry takes care of both endpoint comparisons; the only
remaining input is `PaperBandScaleInequality`. -/
theorem primeBinEnvelopeWidthCore_of_scaleInequality
    {K Ks c : ℝ} {q n : ℕ} {P δ y : ℝ} {a k J : ℕ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hδ : 0 ≤ δ)
    (hk : 0 < k) (ha : a ≤ k * J)
    (hB1 : ∀ j < J, (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ))
    (hY : paperBandTop P δ J ≤ y)
    (hscalar : PaperBandScaleInequality K Ks c q n J P δ y) :
    PrimeBinEnvelopeWidthCore (ι := Fin J) K Ks c q
      (fun j => paperBinLower P δ a k j)
      (fun j => paperBinUpper P δ a k j) n := by
  refine primeBinEnvelopeWidthCore_of_scalarBound
    (y := y) (L := paperBandBottom P δ J) hP hK hKs hq hδ hB1 ?_ ?_ ?_
  · intro j hj
    exact (paperBinUpper_le_paperBandTop hP hδ hj).trans hY
  · intro _j _hj
    exact paperBandBottom_le_centeredBinEndpoint hP hδ hk ha
  · exact paperBandScalarWidthBound_of_scaleInequality hscalar

/-- The same width core with the pointwise `hB1` hypothesis replaced by the
single numeric condition `2 ≤ paperBandBottom P δ J`. -/
theorem primeBinEnvelopeWidthCore_of_scaleInequality_of_bottom
    {K Ks c : ℝ} {q n : ℕ} {P δ y : ℝ} {a k J : ℕ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hδ : 0 ≤ δ)
    (hk : 0 < k) (ha : a ≤ k * J)
    (hbot : 2 ≤ paperBandBottom P δ J)
    (hY : paperBandTop P δ J ≤ y)
    (hscalar : PaperBandScaleInequality K Ks c q n J P δ y) :
    PrimeBinEnvelopeWidthCore (ι := Fin J) K Ks c q
      (fun j => paperBinLower P δ a k j)
      (fun j => paperBinUpper P δ a k j) n :=
  primeBinEnvelopeWidthCore_of_scaleInequality hP hK hKs hq hδ hk ha
    (fun _j hj => one_le_paperBinUpper_of_two_le_bottom hP hδ hk ha hbot hj)
    hY hscalar

/-- **The paper-parameter version.**  With `P = x^(1/k)`, `δ = log(1+λ)/(2k)`
and `J = floor(H/(4δ))`, the top endpoint is below `y` automatically, so the
scale inequality yields `PaperBandScalarWidthBound` for the paper's parameters.
-/
theorem paperBandScalarWidthBound_of_paperParameters
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {k : ℕ}
    (_hx : 0 < x) (_hlam : 0 < lam) (_hk : 0 < k) (_hPle : paperBandP x k ≤ y)
    (hscale : PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k)
      (paperBandDelta lam k) y) :
    PaperBandScalarWidthBound K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandDelta lam k) y
      (paperBandBottom (paperBandP x k) (paperBandDelta lam k)
        (paperBandJ y (paperBandP x k) lam k)) :=
  paperBandScalarWidthBound_of_scaleInequality hscale

/-- **`PrimeBinEnvelopeWidthCore` at the paper's parameters.**  This is the
paper's integer-bin form of the width condition, with `J` and `δ` chosen as in
the manuscript and with the geometric top-bound discharged by
`paperBandTop_paperBandJ_le`. -/
theorem primeBinEnvelopeWidthCore_of_paperParameters
    {K Ks c : ℝ} {q n : ℕ} {x y lam : ℝ} {a k : ℕ}
    (hx : 0 < x) (hlam : 0 < lam) (hk : 0 < k) (hPle : paperBandP x k ≤ y)
    (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q)
    (ha : a ≤ k * paperBandJ y (paperBandP x k) lam k)
    (hB1 : ∀ j < paperBandJ y (paperBandP x k) lam k,
      (1 : ℝ) ≤
        (paperBinUpper (paperBandP x k) (paperBandDelta lam k) a k j : ℝ))
    (hscale : PaperBandScaleInequality K Ks c q n
      (paperBandJ y (paperBandP x k) lam k) (paperBandP x k)
      (paperBandDelta lam k) y) :
    PrimeBinEnvelopeWidthCore
      (ι := Fin (paperBandJ y (paperBandP x k) lam k)) K Ks c q
      (fun j => paperBinLower (paperBandP x k) (paperBandDelta lam k) a k j)
      (fun j => paperBinUpper (paperBandP x k) (paperBandDelta lam k) a k j) n := by
  have hP : 0 ≤ paperBandP x k := (paperBandP_pos hx k).le
  have hδ : 0 ≤ paperBandDelta lam k := (paperBandDelta_pos hlam hk).le
  exact primeBinEnvelopeWidthCore_of_scaleInequality hP hK hKs hq hδ hk ha hB1
    (paperBandTop_paperBandJ_le hx hPle hlam hk) hscale

/-! ## 6. Composition with the critical-line character decay -/

/-- **The paper's smooth-character decay from the single scale inequality.**
`primeBinCharacterDecay_of_paperBandWidth` supplies the GRH constants `K` and
`Ks` and the reduction from `PaperBandScalarWidthBound`; the centred-bin
geometry supplies the endpoint comparisons.  Thus only
`PaperBandScaleInequality` remains. -/
theorem primeBinCharacterDecay_of_scaleInequality
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ {c : ℝ} {q n : ℕ} {P δ y : ℝ} {a k J : ℕ},
        (hq : 1 ≤ q) →
        (hP : 0 ≤ P) → (hδ : 0 ≤ δ) →
        (hJ : 0 < J) →
        (hk : 0 < k) → (ha : a ≤ k * J) →
        (hA2 : ∀ j < J, 2 ≤ paperBinLower P δ a k j) →
        (hB1 : ∀ j < J, (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ)) →
        (hY : paperBandTop P δ J ≤ y) →
        PaperBandScaleInequality K Ks c q n J P δ y →
        PrimeBinCharacterDecay K c q
          (fun j : Fin J => paperBinLower P δ a k j)
          (fun j : Fin J => paperBinUpper P δ a k j) n := by
  obtain ⟨K, Ks, hK, hKs, hmain⟩ := primeBinCharacterDecay_of_paperBandWidth line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro c q n P δ y a k J hq hP hδ hJ hk ha hA2 hB1 hY hscalar
  exact hmain hq hP hδ hJ hA2 hB1
    (fun j hj => (paperBinUpper_le_paperBandTop hP hδ hj).trans hY)
    (fun j _hj => paperBandBottom_le_centeredBinEndpoint hP hδ hk ha)
    (paperBandScalarWidthBound_of_scaleInequality hscalar)

/-! ## Axiom audit -/

#print axioms paperBandDelta_pos
#print axioms paperBandTop_eq_centeredBinEndpoint
#print axioms centeredBinEndpoint_le_paperBandTop
#print axioms paperBandBottom_le_centeredBinEndpoint
#print axioms paperBinUpper_le_paperBandTop
#print axioms centeredBinPatterns_sum_le
#print axioms two_le_paperBinUpper_of_two_le_bottom
#print axioms one_le_paperBinUpper_of_two_le_bottom
#print axioms paperBandJ_mul_delta_le
#print axioms paperBandJ_pos
#print axioms paperBandTop_le_of_J_mul_delta_le
#print axioms paperBandTop_paperBandJ_le
#print axioms paperBandScaleInequality_iff_scalarWidthBound
#print axioms paperBandScalarWidthBound_of_scaleInequality
#print axioms paperBandScaleInequality_width_nonneg
#print axioms paperBandScaleInequality_width_pos
#print axioms primeBinEnvelopeWidthCore_of_scaleInequality
#print axioms primeBinEnvelopeWidthCore_of_scaleInequality_of_bottom
#print axioms paperBandScalarWidthBound_of_paperParameters
#print axioms primeBinEnvelopeWidthCore_of_paperParameters
#print axioms primeBinCharacterDecay_of_scaleInequality

end

end Cogentic.RandomizedL20_2ScalarWidth
