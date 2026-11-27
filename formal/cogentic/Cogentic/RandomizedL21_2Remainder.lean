import Cogentic.RandomizedL21_2Vertical
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# L21.2: the residue/contour identity behind `PerronShiftRemainder`

`Cogentic.RandomizedL21_2Vertical.PerronShiftRemainder` is the contour-shift
decomposition

```
(twistedPrimeSum v t - twistedMain v t) - verticalZetaSum v t (X^3)
  = horizontal remainder + prime-power remainder.
```

This file isolates the *exact* complex-analytic content of that decomposition.
Write `refRe v = 1 + 1 / log v` for the reference abscissa and

```
refZetaSum v t T
  = (1 / 2π) ∫_{τ=-T}^{T}
      (-ζ'/ζ) (refRe v + i(τ+t)) · v^{refRe v + iτ} / (refRe v + iτ) dτ,
```

the truncated Perron integral on the reference line.  The two horizontal
segments of the rectangle `[2/3, refRe v] × [-T, T]` are `horizBot` and
`horizTop`, and

```
horizRemainder v t T = I * (horizBot v t T - horizTop v t T).
```

The main theorem `zetaShiftContourIdentity` proves, from the Riemann hypothesis
for `ζ`,

```
refZetaSum v t T - verticalZetaSum v t T - twistedMain v t
  = horizRemainder v t T,
```

for `|t| < T` (so that the pole `1 - it` is strictly inside the rectangle).
The proof applies the general rectangle residue theorem
`GlobalTheory.ResRect.residue_rectangle` to
`F s = (-ζ'/ζ)(s + it) · v^s / s`; the only singularity in the rectangle is the
simple pole at `s = 1 - it`, whose residue is exactly `twistedMain v t`.  The
hypothesis `RiemannZetaZerosOnLine` is used only to exclude zeros of `ζ` in the
closed rectangle; since the left edge is `2/3 > 1/2`, these zeros lie strictly
to the left of the rectangle.

The rest of the file turns this identity into `PerronShiftRemainder`.
`norm_horizRemainder_le` bounds the horizontal segments explicitly by
`(3 e / π) K U^C v / T` from a uniform strip bound for `ζ'/ζ`;
`contourRemainderBound_of_strip` combines it with the residue identity to
discharge `ContourRemainderBound`; and `perronShiftRemainder_of_bounds`
assembles `PerronShiftRemainder` from

* the contour remainder, i.e. the residue identity plus the horizontal bound,
* a strip bound for `ζ'/ζ` (`StripZetaBound`),
* the truncated Perron/Abel step `ReferencePerronBound`, which is exactly the
  standard truncated Perron approximation of `Σ_{n≤v} Λ(n)n^{-it}` on the
  reference line, followed by the prime-power removal, and
* the elementary `VerticalTailBound`, the cost of moving the vertical contour
  from height `X^3` to `X^3 + 1` so that the pole is strictly interior.

The headline `perronShiftRemainder_of_RH_strip` produces
`PerronShiftRemainder` directly from the Riemann hypothesis for `ζ`, the strip
bound, and the two named Perron/tail inputs.  No circle is left unstated: the
residue identity is proved, not assumed.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Remainder

open Filter Real MeasureTheory Complex Topology
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Vertical

/-! ## The reference line and the horizontal segments -/

/-- The reference abscissa `1 + 1 / log v` of the truncated Perron kernel. -/
def refRe (v : ℝ) : ℝ := 1 + 1 / Real.log v

/-- `1 < refRe v` for `1 < v`. -/
theorem one_lt_refRe {v : ℝ} (hv : 1 < v) : 1 < refRe v := by
  unfold refRe
  have hlog : 0 < Real.log v := Real.log_pos hv
  have : 0 < 1 / Real.log v := one_div_pos.mpr hlog
  linarith

/-- The integrand `(-ζ'/ζ)(s + it) · v^s / s` at the complex point `s`. -/
def zetaShiftFunction (v t : ℝ) (s : ℂ) : ℂ :=
  (- logDeriv riemannZeta (s + (t : ℂ) * I)) * (v : ℂ) ^ s / s

/-- The reference-line Perron integral at `Re s = refRe v`, truncated at
height `T`. -/
def refZetaSum (v t T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ τ in (-T)..T, zetaShiftFunction v t (perronLine (refRe v) τ)

/-- The lower horizontal segment, from `Re s = 2/3` to `Re s = refRe v`, at
height `Im s = -T`. -/
def horizBot (v t T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (-T : ℝ) * I)

/-- The upper horizontal segment, from `Re s = 2/3` to `Re s = refRe v`, at
height `Im s = T`. -/
def horizTop (v t T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (T : ℂ) * I)

/-- The horizontal part of the contour-shift remainder. -/
def horizRemainder (v t T : ℝ) : ℂ :=
  I * (horizBot v t T - horizTop v t T)

/-! ## The simple-pole residue is `twistedMain` -/

/-- `(v : ℂ) ^ (1 - i t) / (1 - i t) = v^{1-it} / (1-it)`, the latter being
`twistedMain`. -/
theorem cpow_one_sub_eq_twistedMain {v t : ℝ} (hv : 0 < v) :
    (v : ℂ) ^ (1 - (t : ℂ) * I) / (1 - (t : ℂ) * I) = twistedMain v t := by
  unfold twistedMain
  congr 1
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [Complex.cpow_def_of_ne_zero hv0, ← Complex.ofReal_log hv.le]
  rw [mul_sub, mul_one]
  rw [show (Real.log v : ℂ) - (Real.log v : ℂ) * ((t : ℂ) * I) =
      (Real.log v : ℂ) + (-((t : ℂ) * I * (Real.log v : ℂ))) by ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hv]
  congr 1
  congr 1
  ring

/-- No zeros of `ζ` in the closed rectangle
`[2/3, refRe v] × [-T, T]`, except possibly the pole `1 - it`. -/
def StripNoZeros (v t T : ℝ) : Prop :=
  ∀ s : ℂ, perronRe ≤ s.re → s.re ≤ refRe v → |s.im| ≤ T →
    s ≠ 1 - (t : ℂ) * I → riemannZeta (s + (t : ℂ) * I) ≠ 0

/-- The Riemann hypothesis for `ζ` excludes all zeros in the strip
`2/3 ≤ Re s ≤ refRe v`: zeros in `0 < Re s < 1` have real part `1/2`, and there
are no zeros with real part at least one. -/
theorem stripNoZeros_of_RH (hRH : RiemannZetaZerosOnLine) {v t T : ℝ} :
    StripNoZeros v t T := by
  intro s h1 h2 h3 hne hzero
  have hpos : 0 < (s + (t : ℂ) * I).re := by
    have hre : (s + (t : ℂ) * I).re = s.re := by simp
    rw [hre]
    have : (0 : ℝ) < perronRe := by norm_num [perronRe]
    linarith
  have hne_one : s + (t : ℂ) * I ≠ 1 := by
    intro h
    apply hne
    have h' : s = 1 - (t : ℂ) * I := by linear_combination h
    exact h'
  rcases lt_or_ge (s + (t : ℂ) * I).re 1 with hlt | hge
  · have hnot_triv : ¬ ∃ n : ℕ, s + (t : ℂ) * I = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      have hre' : (s + (t : ℂ) * I).re = -2 * ((n : ℝ) + 1) := by
        simpa using hre
      have hnpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    have hrehalf := hRH (s + (t : ℂ) * I) hzero hnot_triv hne_one
    have hleft : (2 / 3 : ℝ) ≤ (s + (t : ℂ) * I).re := by
      simpa [perronRe] using h1
    linarith
  · exact riemannZeta_ne_zero_of_one_le_re hge hzero

/-! ## The exact rectangle identity -/

/-- The algebraic form of the residue identity, after dividing the boundary
integral by `2π`.  If `b`, `tp`, `r`, `vv` are the normalised lower, upper,
right and left vertical integrals and `M` is the residue, then the rectangle
identity `b - tp + I*(r - vv) = I*M` is equivalent to
`r - vv - M = I*(b - tp)`. -/
private theorem contour_algebra {b tp r vv M : ℂ}
    (h : b - tp + I * (r - vv) = I * M) :
    r - vv - M = I * (b - tp) := by
  have hI : I * I = (-1 : ℂ) := by simpa [pow_two] using Complex.I_sq
  have h2 : I * (b - tp) - (r - vv) = -M := by
    calc
      I * (b - tp) - (r - vv) = I * (b - tp) + I * I * (r - vv) := by
        rw [hI]; ring
      _ = I * (b - tp + I * (r - vv)) := by ring
      _ = I * (I * M) := by rw [h]
      _ = I * I * M := by ring
      _ = -M := by rw [hI]; ring
  linear_combination -h2

/-- **The exact contour-shift identity.**  For `1 < v`, `0 < T`, `|t| < T`, and
no zeros of `ζ` in the rectangle (which holds under RH, see
`stripNoZeros_of_RH`), the difference between the reference-line integral, the
vertical integral at `2/3`, and the residue `twistedMain` is exactly the two
horizontal segments.

This is the missing residue/contour identity of L21.2, proved here from the
general rectangle residue theorem. -/
theorem zetaShiftContourIdentity {v t T : ℝ} (hv : 1 < v) (hT : 0 < T)
    (ht : |t| < T) (hstrip : StripNoZeros v t T) :
    refZetaSum v t T - verticalZetaSum v t T - twistedMain v t =
      horizRemainder v t T := by
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  let p : ℂ := 1 - (t : ℂ) * I
  let z : ℂ := (perronRe : ℂ) + (-T : ℝ) * I
  let w : ℂ := (refRe v : ℂ) + (T : ℝ) * I
  let S : Finset ℂ := {p}
  let r : ℂ → ℂ := fun p' => if p' = p then twistedMain v t else 0
  have hzre : z.re = perronRe := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = refRe v := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hlt_re : z.re < w.re := by rw [hzre, hwre]; exact lt_trans (by norm_num [perronRe]) (one_lt_refRe hv)
  have hlt_im : z.im < w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ p' ∈ S, z.re < p'.re ∧ p'.re < w.re ∧ z.im < p'.im ∧ p'.im < w.im := by
    intro p' hp'
    have hp'_eq : p' = p := by simpa [S] using hp'
    subst hp'_eq
    have ht' := abs_lt.mp ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [p, z, perronRe]
      norm_num
    · simpa [p, w] using one_lt_refRe hv
    · simp only [p, z]
      simp
      linarith [ht'.2]
    · simp only [p, w]
      simp
      linarith [ht'.1]
  have hdiff : DifferentiableOn ℂ (zetaShiftFunction v t)
      ((Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im) \ ↑S) := by
    intro s hs
    rw [Set.mem_sdiff] at hs
    obtain ⟨hsR, hsS⟩ := hs
    rw [Complex.mem_reProdIm] at hsR
    obtain ⟨⟨hsre1, hsre2⟩, ⟨hsim1, hsim2⟩⟩ := hsR
    have hsre1' : perronRe ≤ s.re := by simpa [hzre] using hsre1
    have hsre2' : s.re ≤ refRe v := by simpa [hwre] using hsre2
    have hsim : |s.im| ≤ T := by
      rw [abs_le]
      exact ⟨by simpa [hzim] using hsim1, by simpa [hwim] using hsim2⟩
    have hsp : s ≠ p := by
      intro h
      exact hsS (by simp [S, h])
    have hzene : riemannZeta (s + (t : ℂ) * I) ≠ 0 := hstrip s hsre1' hsre2' hsim hsp
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hsre1'
      have : (0 : ℝ) < perronRe := by norm_num [perronRe]
      linarith
    have hshift : DifferentiableAt ℂ (fun s : ℂ => s + (t : ℂ) * I) s := by
      simpa using (differentiableAt_id (x := s)).add_const ((t : ℂ) * I)
    have hsne1 : s + (t : ℂ) * I ≠ 1 := by
      intro h
      apply hsp
      linear_combination h
    have hAn : AnalyticAt ℂ riemannZeta (s + (t : ℂ) * I) :=
      analyticOn_riemannZeta (s + (t : ℂ) * I) (by simpa using hsne1)
    have hζc : DifferentiableAt ℂ
        (riemannZeta ∘ fun s : ℂ => s + (t : ℂ) * I) s :=
      hAn.differentiableAt.comp s hshift
    have hderc : DifferentiableAt ℂ
        (deriv riemannZeta ∘ fun s : ℂ => s + (t : ℂ) * I) s :=
      hAn.deriv.differentiableAt.comp s hshift
    have hζ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s + (t : ℂ) * I)) s := by
      simpa [Function.comp_def] using hζc
    have hder : DifferentiableAt ℂ (fun s : ℂ => deriv riemannZeta (s + (t : ℂ) * I)) s := by
      simpa [Function.comp_def] using hderc
    have hlog : DifferentiableAt ℂ
        (fun s : ℂ => - logDeriv riemannZeta (s + (t : ℂ) * I)) s := by
      change DifferentiableAt ℂ
        (fun s : ℂ => -(deriv riemannZeta (s + (t : ℂ) * I) /
          riemannZeta (s + (t : ℂ) * I))) s
      exact (hder.div hζ hzene).neg
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (v : ℂ) ^ s) s :=
      (GlobalTheory.ExplicitRect.analyticAt_cpow hv0 s).differentiableAt
    exact ((hlog.mul hcp).div differentiableAt_id hs0).differentiableWithinAt
  have hexp : ∀ p' ∈ S, ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p' ∧
      ∀ᶠ s in 𝓝[≠] p', zetaShiftFunction v t s =
        a / (s - p') ^ 2 + r p' / (s - p') + G s := by
    intro p' hp'
    have hp'_eq : p' = p := by simpa [S] using hp'
    subst hp'_eq
    obtain ⟨g, hg_an, hg⟩ := GlobalTheory.ExplicitRect.logDeriv_one
      (N := 1) (χ := (1 : DirichletCharacter ℂ 1)) DirichletCharacter.isPrimitive_one_level_one
    have hg' : ∀ᶠ s in 𝓝[≠] (1 : ℂ),
        deriv riemannZeta s / riemannZeta s = (-1 : ℂ) / (s - 1) + g s := by
      simpa using hg
    have htend0 : Tendsto (fun s : ℂ => s + (t : ℂ) * I) (𝓝 p) (𝓝 (1 : ℂ)) := by
      have hid : Tendsto (fun s : ℂ => s) (𝓝 p) (𝓝 p) := tendsto_id
      have h := hid.add_const ((t : ℂ) * I)
      have hpadd : p + (t : ℂ) * I = 1 := by simp [p]
      rwa [hpadd] at h
    have htend : Tendsto (fun s : ℂ => s + (t : ℂ) * I) (𝓝[≠] p) (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · exact htend0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
        intro h
        apply hs
        linear_combination h
    have hφ : ∀ᶠ s in 𝓝[≠] p,
        logDeriv riemannZeta (s + (t : ℂ) * I) = (-1 : ℂ) / (s - p) + g (s + (t : ℂ) * I) := by
      filter_upwards [htend.eventually hg'] with s hs
      have hsp : s + (t : ℂ) * I - 1 = s - p := by ring
      simpa [logDeriv, hsp] using hs
    have hp0 : p ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [p] at hre
    have hinner : AnalyticAt ℂ (fun s : ℂ => s + (t : ℂ) * I) p := by
      fun_prop
    have hg_comp : AnalyticAt ℂ (fun s : ℂ => g (s + (t : ℂ) * I)) p := by
      have h := AnalyticAt.comp_of_eq hg_an hinner (by simp [p])
      convert h using 1
      ext s
      rfl
    obtain ⟨a, G, hG, hFG⟩ := GlobalTheory.ExplicitRect.expand_simple
      (u := v) hv0 hp0 hg_comp hφ
    refine ⟨a, G, hG, ?_⟩
    filter_upwards [hFG] with s hs
    have hres : (v : ℂ) ^ p / p = twistedMain v t := cpow_one_sub_eq_twistedMain hv0
    have hzdef : zetaShiftFunction v t s = -(logDeriv riemannZeta (s + (t : ℂ) * I)) *
        (v : ℂ) ^ s / s := rfl
    rw [hzdef]
    rw [hs]
    rw [show -(-1 * ((v : ℂ) ^ p / p)) = (v : ℂ) ^ p / p by ring, hres]
    simp [r, p]
  have hres := GlobalTheory.ResRect.residue_rectangle (zetaShiftFunction v t) z w S r
    hlt_re hlt_im hmem hdiff hexp
  -- Normalise the four boundary integrals.
  have hbot : (∫ x : ℝ in z.re..w.re, zetaShiftFunction v t (x + z.im * I)) =
      (2 * Real.pi : ℂ) * horizBot v t T := by
    rw [hzre, hwre, hzim]
    unfold horizBot
    rw [show (2 * (Real.pi : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (-T : ℝ) * I)) =
        ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (-T : ℝ) * I) by
      field_simp]
  have htop : (∫ x : ℝ in z.re..w.re, zetaShiftFunction v t (x + w.im * I)) =
      (2 * Real.pi : ℂ) * horizTop v t T := by
    rw [hzre, hwre, hwim]
    unfold horizTop
    rw [show (2 * (Real.pi : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (T : ℂ) * I)) =
        ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (T : ℂ) * I) by
      field_simp]
  have hright : (∫ y : ℝ in z.im..w.im, zetaShiftFunction v t (w.re + y * I)) =
      (2 * Real.pi : ℂ) * refZetaSum v t T := by
    rw [hzim, hwim, hwre]
    unfold refZetaSum
    rw [show (2 * (Real.pi : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ τ in -T..T, zetaShiftFunction v t (perronLine (refRe v) τ)) =
        ∫ τ in -T..T, zetaShiftFunction v t (perronLine (refRe v) τ) by
      field_simp]
    rfl
  have hleft : (∫ y : ℝ in z.im..w.im, zetaShiftFunction v t (z.re + y * I)) =
      (2 * Real.pi : ℂ) * verticalZetaSum v t T := by
    rw [hzim, hwim, hzre]
    unfold verticalZetaSum
    rw [show (2 * (Real.pi : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) * ∫ τ in -T..T, stripIntegrand v t τ) =
        ∫ τ in -T..T, stripIntegrand v t τ by
      field_simp]
    apply intervalIntegral.integral_congr
    intro y _
    have harg : ((perronRe : ℂ) + (y : ℂ) * I + (t : ℂ) * I) =
        (perronRe : ℂ) + ((y + t : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [stripIntegrand, zetaShiftFunction, perronLine]
    rw [harg]
    ring
  have hsum : (∑ p' ∈ S, r p') = twistedMain v t := by
    simp [S, r]
  rw [hbot, htop, hright, hleft, hsum] at hres
  -- Divide by `2π` and apply the algebraic lemma.
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hpi
  have hnorm : (2 * Real.pi : ℂ) * horizBot v t T - (2 * Real.pi : ℂ) * horizTop v t T +
      I * ((2 * Real.pi : ℂ) * refZetaSum v t T) - I * ((2 * Real.pi : ℂ) * verticalZetaSum v t T)
      = (2 * Real.pi : ℂ) * (horizBot v t T - horizTop v t T +
        I * (refZetaSum v t T - verticalZetaSum v t T)) := by ring
  have hres' : horizBot v t T - horizTop v t T +
      I * (refZetaSum v t T - verticalZetaSum v t T) = I * twistedMain v t := by
    have := hres
    have hdiv : (2 * Real.pi : ℂ) * (horizBot v t T - horizTop v t T +
        I * (refZetaSum v t T - verticalZetaSum v t T)) =
        (2 * Real.pi : ℂ) * (I * twistedMain v t) := by
      calc
        (2 * Real.pi : ℂ) * (horizBot v t T - horizTop v t T +
            I * (refZetaSum v t T - verticalZetaSum v t T))
            = (2 * Real.pi : ℂ) * horizBot v t T - (2 * Real.pi : ℂ) * horizTop v t T +
              I * ((2 * Real.pi : ℂ) * refZetaSum v t T) -
              I * ((2 * Real.pi : ℂ) * verticalZetaSum v t T) := by ring
        _ = 2 * (Real.pi : ℂ) * I * twistedMain v t := hres
        _ = (2 * Real.pi : ℂ) * (I * twistedMain v t) := by ring
    exact mul_left_cancel₀ h2pi hdiv
  have halg := contour_algebra hres'
  -- `halg : refZetaSum - verticalZetaSum - twistedMain = I * (horizBot - horizTop)`.
  simpa [horizRemainder] using halg

/-- A uniform bound for `ζ'/ζ` on the strip `2/3 ≤ Re s ≤ 3`, up to height
`3 X^3`.  This is the only zeta estimate used by the horizontal remainder; it
is the standard strip bound for the logarithmic derivative of `ζ`. -/
def StripZetaBound (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, perronRe ≤ s.re → s.re ≤ 3 → |s.im| ≤ 3 * X n ^ 3 →
    ‖logDeriv riemannZeta s‖ ≤ K n * (bandLog X n) ^ C

/-- `v ^ refRe v = e · v`, the exact value of the reference-line weight at the
right edge of the rectangle. -/
theorem rpow_refRe_eq {v : ℝ} (hv : 1 < v) : v ^ refRe v = Real.exp 1 * v := by
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have hlog : Real.log v ≠ 0 := (Real.log_pos hv).ne'
  unfold refRe
  rw [Real.rpow_add hv0, Real.rpow_one]
  have h : v ^ (1 / Real.log v) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hv0, Real.exp_eq_exp]
    field_simp
  rw [h]
  ring

/-- The rectangle is at most three units wide in the real direction. -/
theorem refRe_sub_perronRe_le_three {v : ℝ} (hv : 2 ≤ v) :
    refRe v - perronRe ≤ 3 := by
  have hv1 : 1 < v := lt_of_lt_of_le one_lt_two hv
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ge : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogv : Real.log 2 ≤ Real.log v := Real.log_le_log (by norm_num) hv
  have hinv : 1 / Real.log v ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hlogv
  have htwo : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  have hre : refRe v ≤ 3 := by
    unfold refRe
    linarith
  have hper : (0 : ℝ) ≤ perronRe := by norm_num [perronRe]
  linarith

/-- For `v ≥ 2` the reference abscissa lies below `3`, the right edge of the
strip on which `StripZetaBound` is stated. -/
theorem refRe_le_three {v : ℝ} (hv : 2 ≤ v) : refRe v ≤ 3 := by
  have hv1 : 1 < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos hv1
  have hlog2 : Real.log 2 ≤ Real.log v := Real.log_le_log (by norm_num) hv
  have h2 : 1 / Real.log v ≤ 2 := by
    rw [div_le_iff₀ hlogv]
    nlinarith [hlog2, Real.log_two_gt_d9]
  unfold refRe
  linarith

/-- The horizontal remainder is bounded by the strip bound for `ζ'/ζ`.  The
constant `3 e / π` is deliberately coarse: the exact integral of `v^σ` is not
needed, only `refRe v - 2/3 ≤ 3` and `v^refRe v = e v`. -/
theorem norm_horizRemainder_le {v t T K U C : ℝ}
    (hv : 2 ≤ v) (hT : 0 < T) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hbound : ∀ σ ∈ Set.Icc perronRe (refRe v),
      ‖logDeriv riemannZeta ((σ : ℂ) + (T + t) * I)‖ ≤ K * U ^ C ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + (-T + t) * I)‖ ≤ K * U ^ C) :
    ‖horizRemainder v t T‖ ≤
      (3 * Real.exp 1 / Real.pi) * (K * (v * U ^ C / T)) := by
  have hv1 : 1 < v := lt_of_lt_of_le one_lt_two hv
  have hv0 : 0 < v := lt_trans zero_lt_one hv1
  have hT0 : 0 < T := hT
  have hUc : 0 ≤ U ^ C := Real.rpow_nonneg hU C
  have hA : 0 ≤ K * U ^ C := mul_nonneg hK hUc
  have hwidth : refRe v - perronRe ≤ 3 := refRe_sub_perronRe_le_three hv
  have hvr : v ^ refRe v = Real.exp 1 * v := rpow_refRe_eq hv1
  have hnormfac : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hseg (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
      ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (sgn * T : ℝ) * I)‖ ≤
        (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) := by
    rw [norm_mul, hnormfac]
    have hmono : ∀ σ ∈ Set.Ioc perronRe (refRe v),
        ‖zetaShiftFunction v t ((σ : ℂ) + (sgn * T : ℝ) * I)‖ ≤
          (K * U ^ C) * v ^ σ / T := by
      intro σ hσ
      have hσI : σ ∈ Set.Icc perronRe (refRe v) := ⟨le_of_lt hσ.1, hσ.2⟩
      have hb := hbound σ hσI
      have harg : ((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I =
          (σ : ℂ) + ((sgn * T + t : ℝ) : ℂ) * I := by
        push_cast
        ring
      have hζ : ‖logDeriv riemannZeta (((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I)‖ ≤
          K * U ^ C := by
        rw [harg]
        rcases hsgn with rfl | rfl
        · simpa [add_comm, add_left_comm, add_assoc] using hb.1
        · simpa [add_comm, add_left_comm, add_assoc] using hb.2
      have hden : T ≤ ‖(σ : ℂ) + (sgn * T : ℝ) * I‖ := by
        have him : ((σ : ℂ) + (sgn * T : ℝ) * I).im = sgn * T := by simp
        have habs : |sgn * T| = T := by
          rcases hsgn with rfl | rfl
          · simp [abs_of_pos hT0]
          · simp [abs_of_pos hT0]
        calc
          T = |((σ : ℂ) + (sgn * T : ℝ) * I).im| := by rw [him, habs]
          _ ≤ ‖(σ : ℂ) + (sgn * T : ℝ) * I‖ := Complex.abs_im_le_norm _
      have hvσ : 0 ≤ v ^ σ := Real.rpow_nonneg hv0.le σ
      have hmain : ‖zetaShiftFunction v t ((σ : ℂ) + (sgn * T : ℝ) * I)‖ =
          ‖logDeriv riemannZeta (((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I)‖ *
            v ^ σ / ‖(σ : ℂ) + (sgn * T : ℝ) * I‖ := by
        rw [zetaShiftFunction, norm_div, norm_mul, norm_neg,
          Complex.norm_cpow_eq_rpow_re_of_pos hv0]
        simp
      rw [hmain]
      have hnum : ‖logDeriv riemannZeta (((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I)‖ *
          v ^ σ ≤ (K * U ^ C) * v ^ σ :=
        mul_le_mul_of_nonneg_right hζ hvσ
      calc
        ‖logDeriv riemannZeta (((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I)‖ *
            v ^ σ / ‖(σ : ℂ) + (sgn * T : ℝ) * I‖
            = (‖logDeriv riemannZeta (((σ : ℂ) + (sgn * T : ℝ) * I) + (t : ℂ) * I)‖ *
                v ^ σ) * (‖(σ : ℂ) + (sgn * T : ℝ) * I‖)⁻¹ := by ring
        _ ≤ ((K * U ^ C) * v ^ σ) * T⁻¹ := by
          exact mul_le_mul hnum (inv_anti₀ hT0 hden) (by positivity)
            (mul_nonneg hA hvσ)
        _ = (K * U ^ C) * v ^ σ / T := by ring
    have hg : IntervalIntegrable (fun σ : ℝ => (K * U ^ C) * v ^ σ / T) volume
        perronRe (refRe v) := by
      have hcont : Continuous fun σ : ℝ => (K * U ^ C) * v ^ σ / T := by
        have : Continuous fun σ : ℝ => v ^ σ := by
          rw [show (fun σ : ℝ => v ^ σ) = fun σ => Real.exp (Real.log v * σ) by
            funext σ; rw [Real.rpow_def_of_pos hv0]]
          fun_prop
        exact (continuous_const.mul this).div_const T
      exact hcont.intervalIntegrable _ _
    have hint := intervalIntegral.norm_integral_le_of_norm_le
      (by have h := one_lt_refRe hv1; norm_num [perronRe]; linarith)
      (Filter.Eventually.of_forall fun σ hσ => hmono σ hσ) hg
    have hInt2 : (∫ σ in perronRe..refRe v, (K * U ^ C) * v ^ σ / T) ≤
        (K * (v * U ^ C / T)) * (3 * Real.exp 1) := by
      have hle : ∀ σ ∈ Set.Icc perronRe (refRe v), v ^ σ ≤ v ^ refRe v := by
        intro σ hσ
        exact Real.rpow_le_rpow_of_exponent_le hv1.le hσ.2
      have hIntle : (∫ σ in perronRe..refRe v, v ^ σ) ≤
          (refRe v - perronRe) * v ^ refRe v := by
        have hcont : Continuous fun σ : ℝ => v ^ σ := by
          rw [show (fun σ : ℝ => v ^ σ) = fun σ => Real.exp (Real.log v * σ) by
            funext σ; rw [Real.rpow_def_of_pos hv0]]
          fun_prop
        calc
          (∫ σ in perronRe..refRe v, v ^ σ)
              ≤ ∫ σ in perronRe..refRe v, v ^ refRe v :=
            intervalIntegral.integral_mono_on
              (by have h := one_lt_refRe hv1; norm_num [perronRe]; linarith)
              (hcont.intervalIntegrable _ _) (intervalIntegrable_const) hle
          _ = (refRe v - perronRe) * v ^ refRe v := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
      have hIntv : (∫ σ in perronRe..refRe v, v ^ σ) ≤ 3 * (Real.exp 1 * v) := by
        calc
          (∫ σ in perronRe..refRe v, v ^ σ)
              ≤ (refRe v - perronRe) * v ^ refRe v := hIntle
          _ = (refRe v - perronRe) * (Real.exp 1 * v) := by rw [hvr]
          _ ≤ 3 * (Real.exp 1 * v) :=
            mul_le_mul_of_nonneg_right hwidth (by positivity)
      calc
        (∫ σ in perronRe..refRe v, (K * U ^ C) * v ^ σ / T)
            = (K * U ^ C / T) * ∫ σ in perronRe..refRe v, v ^ σ := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
          ring
        _ ≤ (K * U ^ C / T) * (3 * (Real.exp 1 * v)) :=
          mul_le_mul_of_nonneg_left hIntv (by positivity)
        _ = (K * (v * U ^ C / T)) * (3 * Real.exp 1) := by ring
    calc
      (1 / (2 * Real.pi)) *
          ‖∫ σ in perronRe..refRe v, zetaShiftFunction v t ((σ : ℂ) + (sgn * T : ℝ) * I)‖
          ≤ (1 / (2 * Real.pi)) *
              (∫ σ in perronRe..refRe v, (K * U ^ C) * v ^ σ / T) := by
            gcongr
      _ ≤ (1 / (2 * Real.pi)) *
            ((K * (v * U ^ C / T)) * (3 * Real.exp 1)) := by
          gcongr
      _ = (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) := by ring
  have htop := hseg 1 (Or.inl rfl)
  have hbot := hseg (-1) (Or.inr rfl)
  have htop' : ‖horizTop v t T‖ ≤
      (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) := by
    simpa [horizTop, mul_one] using htop
  have hbot' : ‖horizBot v t T‖ ≤
      (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) := by
    simpa [horizBot, neg_one_mul] using hbot
  unfold horizRemainder
  rw [norm_mul, Complex.norm_I, one_mul]
  refine (norm_sub_le _ _).trans ?_
  calc
    ‖horizBot v t T‖ + ‖horizTop v t T‖
        ≤ (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) +
          (3 * Real.exp 1 / (2 * Real.pi)) * (K * (v * U ^ C / T)) :=
      add_le_add hbot' htop'
    _ = (3 * Real.exp 1 / Real.pi) * (K * (v * U ^ C / T)) := by ring

/-- The truncated Perron/Abel approximation of `twistedPrimeSum` by the
reference-line integral at height `X^3 + 1`.  This is the standard truncated
Perron formula for `Σ_{n≤v} Λ(n)n^{-it}`, followed by the prime-power removal.
The existing kernel theorems (`GlobalTheory.PerronKernel.truncated_perron_kernel`
and `GlobalTheory.PerronPsi.truncated_perron_psi`) prove it in the regime
`T ≤ u`; the L21.2 regime `T ≫ u` is the same kernel argument with the `T ≤ u`
side condition removed. -/
def ReferencePerronBound (X : ℕ → ℝ) (c : ℝ) (K : ℕ → ℝ) (_C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1)‖ ≤
        shiftPrimePower (K n) v

/-- The contour-shift remainder at height `X^3 + 1`, where the pole `1 - it` is
strictly inside the rectangle for every `|t| ≤ X^3`. -/
def ContourRemainderBound (X : ℕ → ℝ) (c : ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖refZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3 + 1) -
        twistedMain v t‖ ≤
        shiftHorizontal (K n) (bandLog X n) C (X n) v

/-- The cost of moving the vertical contour from `X^3` to `X^3 + 1`. -/
def VerticalTailBound (X : ℕ → ℝ) (K : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v → |t| ≤ X n ^ 3 →
    ‖verticalZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3)‖ ≤
      shiftHorizontal (K n) (bandLog X n) C (X n) v

/-- **`PerronShiftRemainder` from the contour remainder and the reference
Perron step.**  The exact contour identity is `zetaShiftContourIdentity`; the
two remaining inputs are the strip bound (through `ContourRemainderBound`) and
the truncated Perron/Abel approximation.  The vertical tail at height `X^3 + 1`
is the only boundary correction; it is absorbed into the horizontal term. -/
theorem perronShiftRemainder_of_bounds {X : ℕ → ℝ} {c : ℝ} {Kper : ℕ → ℝ}
    {Cper : ℝ} {Kref Kcont Ktail : ℕ → ℝ}
    (hX : ∀ n, 1 < X n)
    (hRef : ReferencePerronBound X c Kref Cper)
    (hCont : ContourRemainderBound X c Kcont Cper)
    (hTail : VerticalTailBound X Ktail Cper)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hKcont : ∀ᶠ n : ℕ in atTop, 0 ≤ Kcont n)
    (hKtail : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n)
    (hK : ∀ᶠ n : ℕ in atTop, Kref n + Kcont n + Ktail n ≤ Kper n) :
    PerronShiftRemainder X c Kper Cper := by
  filter_upwards [hRef, hCont, hTail, hKref, hKcont, hKtail, hK]
    with n href hcont htail hkref hkcont hktail hk
  intro v t hv hvB ht
  have hsplit : twistedPrimeSum v t - twistedMain v t - verticalZetaSum v t (X n ^ 3) =
      (twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1)) +
        (refZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3 + 1) -
          twistedMain v t) +
        (verticalZetaSum v t (X n ^ 3 + 1) - verticalZetaSum v t (X n ^ 3)) := by
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have h1 := href v t hv hvB ht
  have h2 := hcont v t hv hvB ht
  have h3 := htail v t hv ht
  have hsum : shiftPrimePower (Kref n) v +
      shiftHorizontal (Kcont n) (bandLog X n) Cper (X n) v +
      shiftHorizontal (Ktail n) (bandLog X n) Cper (X n) v ≤
      shiftPrimePower (Kper n) v +
        shiftHorizontal (Kper n) (bandLog X n) Cper (X n) v := by
    have hU : 0 ≤ bandLog X n := (Real.log_pos (hX n)).le
    have hHnon : 0 ≤ v * (bandLog X n) ^ Cper / X n ^ 3 := by
      have hX0 : 0 ≤ X n := (lt_trans zero_lt_one (hX n)).le
      exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hU Cper)) (pow_nonneg hX0 3)
    have hPnon : 0 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg v) (sq_nonneg _)
    have hmul1 : shiftHorizontal (Kcont n + Ktail n) (bandLog X n) Cper (X n) v =
        shiftHorizontal (Kcont n) (bandLog X n) Cper (X n) v +
          shiftHorizontal (Ktail n) (bandLog X n) Cper (X n) v := by
      unfold shiftHorizontal; ring
    have hKref_le : Kref n ≤ Kper n := by linarith [hk, hkcont, hktail]
    have hmul2 : shiftPrimePower (Kref n) v ≤ shiftPrimePower (Kper n) v := by
      unfold shiftPrimePower
      exact mul_le_mul_of_nonneg_right hKref_le hPnon
    have hKct : Kcont n + Ktail n ≤ Kper n := by linarith [hk, hkref]
    have hmul3 : shiftHorizontal (Kcont n + Ktail n) (bandLog X n) Cper (X n) v ≤
        shiftHorizontal (Kper n) (bandLog X n) Cper (X n) v := by
      unfold shiftHorizontal
      exact mul_le_mul_of_nonneg_right hKct hHnon
    linarith [hmul1, hmul2, hmul3]
  linarith


/-! ## What remains

The exact residue/contour identity is **proved**: `zetaShiftContourIdentity`
is the rectangle identity for `F s = (-ζ'/ζ)(s+it) · v^s / s`, with the
simple residue `twistedMain v t` at `s = 1 - it`.  The hypothesis
`StripNoZeros v t T` is discharged from `RiemannZetaZerosOnLine` by
`stripNoZeros_of_RH` (the left edge `2/3` is strictly to the right of the
critical line, so no zero of `ζ` lies inside the rectangle).

`perronShiftRemainder_of_bounds` then reduces the paper's
`PerronShiftRemainder` to three explicit inputs:

* `ReferencePerronBound`: the truncated Perron/Abel approximation of
  `twistedPrimeSum` by `refZetaSum` at height `X^3 + 1`.  This is the standard
  truncated Perron formula for `Σ_{n≤v} Λ(n)n^{-it}` plus the prime-power
  removal.  The repository's kernel theorems
  (`GlobalTheory.PerronKernel.truncated_perron_kernel`,
  `GlobalTheory.PerronPsi.truncated_perron_psi`) prove this in the regime
  `T ≤ u`; L21.2 has `T = X^3 ≫ v`, so the same kernel argument is needed
  with the `T ≤ u` side condition removed.
* `ContourRemainderBound`: the horizontal estimate
  `‖horizRemainder v t (X^3+1)‖ ≤ shiftHorizontal ...`.  It is the `L¹`
  estimate of `∫_{2/3}^{refRe v} (-ζ'/ζ)(σ+iT) v^σ/(σ+iT) dσ`; the explicit
  constant is `O(1)` because `refRe v - 2/3 ≤ 3` and `v^refRe v = e v`.
  A uniform strip bound for `ζ'/ζ` plus this elementary `L¹` estimate
  discharges it; the strip bound is kept as the explicit input
  `ContourRemainderBound` rather than folded back into the contour identity.
* `VerticalTailBound`: the elementary cost of moving the vertical contour
  from `X^3` to `X^3 + 1`; it is `O(v^{2/3} U^C / X^3)`, hence absorbed into
  the horizontal term.

Thus no residue identity remains missing.  The only remaining analytic inputs
are the truncated Perron/Abel approximation and the standard strip bound for
`ζ'/ζ`; both are named explicitly as `Prop`s rather than hidden in
`PerronShiftRemainder`.

-/ 

/-- **The exact contour identity plus the strip bound give the contour
remainder.**  This is the reduction of `ContourRemainderBound` to
`StripZetaBound` and `RiemannZetaZerosOnLine`; the only estimate is the
elementary horizontal bound `norm_horizRemainder_le`. -/
theorem contourRemainderBound_of_strip {X : ℕ → ℝ} {c : ℝ} {K : ℕ → ℝ}
    {C : ℝ} {Kstrip : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine) (hstrip : StripZetaBound X Kstrip C)
    (hX : ∀ n, 1 < X n) (hKstrip : ∀ n, 0 ≤ Kstrip n)
    (hK : ∀ᶠ n : ℕ in atTop,
      (3 * Real.exp 1 / Real.pi) * Kstrip n ≤ K n) :
    ContourRemainderBound X c K C := by
  filter_upwards [hstrip, hK] with n hb hk
  intro v t hv hvB ht
  let T : ℝ := X n ^ 3 + 1
  have hX3pos : (0 : ℝ) < X n ^ 3 := pow_pos (lt_trans zero_lt_one (hX n)) 3
  have hX3gt : (1 : ℝ) < X n ^ 3 := one_lt_pow₀ (hX n) (by norm_num)
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : |t| < T := by
    have := abs_le.mp ht
    dsimp [T]
    linarith
  have hid := zetaShiftContourIdentity (v := v) (t := t) (T := T)
    (by linarith : 1 < v) hT htT (stripNoZeros_of_RH hRH)
  rw [hid]
  have hbound : ∀ σ ∈ Set.Icc perronRe (refRe v),
      ‖logDeriv riemannZeta ((σ : ℂ) + (T + t) * I)‖ ≤
          Kstrip n * (bandLog X n) ^ C ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + (-T + t) * I)‖ ≤
          Kstrip n * (bandLog X n) ^ C := by
    intro σ hσ
    have hσre1 : perronRe ≤ σ := hσ.1
    have hσre2 : σ ≤ 3 := by
      exact hσ.2.trans (refRe_le_three hv)
    have him1 : |((σ : ℂ) + (T + t) * I).im| ≤ 3 * X n ^ 3 := by
      have him : ((σ : ℂ) + (T + t) * I).im = T + t := by simp
      rw [him]
      have ht' := abs_le.mp ht
      dsimp [T] at *
      rw [abs_le]
      constructor <;> nlinarith [hX3gt, ht'.1, ht'.2]
    have him2 : |((σ : ℂ) + (-T + t) * I).im| ≤ 3 * X n ^ 3 := by
      have him : ((σ : ℂ) + (-T + t) * I).im = -T + t := by simp
      rw [him]
      have ht' := abs_le.mp ht
      dsimp [T] at *
      rw [abs_le]
      constructor <;> nlinarith [hX3gt, ht'.1, ht'.2]
    exact ⟨hb ((σ : ℂ) + (T + t) * I) (by simpa using hσre1)
        (by simpa using hσre2) him1,
      hb ((σ : ℂ) + (-T + t) * I) (by simpa using hσre1)
        (by simpa using hσre2) him2⟩
  have hh := norm_horizRemainder_le (v := v) (t := t) (T := T)
    (K := Kstrip n) (U := bandLog X n) (C := C) hv hT
    (hKstrip n) (Real.log_pos (hX n)).le hbound
  refine hh.trans ?_
  have hden : X n ^ 3 ≤ T := by dsimp [T]; linarith
  have hnum_nonneg : 0 ≤ v * (bandLog X n) ^ C :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (Real.log_pos (hX n)).le C)
  have hdiv : v * (bandLog X n) ^ C / T ≤
      v * (bandLog X n) ^ C / X n ^ 3 :=
    div_le_div_of_nonneg_left hnum_nonneg hX3pos hden
  unfold shiftHorizontal
  calc
    (3 * Real.exp 1 / Real.pi) * (Kstrip n * (v * (bandLog X n) ^ C / T))
        ≤ (3 * Real.exp 1 / Real.pi) *
            (Kstrip n * (v * (bandLog X n) ^ C / X n ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdiv (hKstrip n)) (by positivity)
    _ = ((3 * Real.exp 1 / Real.pi) * Kstrip n) *
          (v * (bandLog X n) ^ C / X n ^ 3) := by ring
    _ ≤ K n * (v * (bandLog X n) ^ C / X n ^ 3) :=
          mul_le_mul_of_nonneg_right hk
            (div_nonneg
              (mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_pos (hX n)).le C))
              (pow_nonneg (le_of_lt (lt_trans zero_lt_one (hX n))) 3))

/-- **`PerronShiftRemainder` from the Riemann hypothesis, the strip bound for
`ζ'/ζ`, and the two explicit Perron inputs.**  The contour remainder is
discharged by `contourRemainderBound_of_strip`; `ReferencePerronBound` and
`VerticalTailBound` are the exact truncated-Perron and contour-tail
statements. -/
theorem perronShiftRemainder_of_RH_strip {X : ℕ → ℝ} {c : ℝ} {Kper : ℕ → ℝ}
    {Cper : ℝ} {Kstrip Kref Ktail : ℕ → ℝ}
    (hRH : RiemannZetaZerosOnLine)
    (hstrip : StripZetaBound X Kstrip Cper)
    (hX : ∀ n, 1 < X n) (hKstrip : ∀ n, 0 ≤ Kstrip n)
    (hRef : ReferencePerronBound X c Kref Cper)
    (hTail : VerticalTailBound X Ktail Cper)
    (hKref : ∀ᶠ n : ℕ in atTop, 0 ≤ Kref n)
    (hKtail : ∀ᶠ n : ℕ in atTop, 0 ≤ Ktail n)
    (hK : ∀ᶠ n : ℕ in atTop,
      Kref n + (3 * Real.exp 1 / Real.pi) * Kstrip n + Ktail n ≤ Kper n) :
    PerronShiftRemainder X c Kper Cper := by
  refine perronShiftRemainder_of_bounds (X := X) (c := c) (Kper := Kper)
    (Cper := Cper) (Kref := Kref)
    (Kcont := fun n => (3 * Real.exp 1 / Real.pi) * Kstrip n) (Ktail := Ktail)
    hX hRef ?_ hTail hKref ?_ hKtail ?_
  · exact contourRemainderBound_of_strip hRH hstrip hX hKstrip
      (Filter.Eventually.of_forall fun _ => le_refl _)
  · exact Filter.Eventually.of_forall fun n =>
      mul_nonneg (by positivity) (hKstrip n)
  · exact hK

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Remainder.cpow_one_sub_eq_twistedMain
#print axioms Cogentic.RandomizedL21_2Remainder.stripNoZeros_of_RH
#print axioms Cogentic.RandomizedL21_2Remainder.zetaShiftContourIdentity
#print axioms Cogentic.RandomizedL21_2Remainder.rpow_refRe_eq
#print axioms Cogentic.RandomizedL21_2Remainder.refRe_sub_perronRe_le_three
#print axioms Cogentic.RandomizedL21_2Remainder.refRe_le_three
#print axioms Cogentic.RandomizedL21_2Remainder.norm_horizRemainder_le
#print axioms Cogentic.RandomizedL21_2Remainder.perronShiftRemainder_of_bounds
#print axioms Cogentic.RandomizedL21_2Remainder.contourRemainderBound_of_strip
#print axioms Cogentic.RandomizedL21_2Remainder.perronShiftRemainder_of_RH_strip

end Cogentic.RandomizedL21_2Remainder
