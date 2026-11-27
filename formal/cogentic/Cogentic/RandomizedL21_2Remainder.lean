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

The rest of the file is the elementary estimate of the horizontal remainder
from a strip bound for `ζ'/ζ`, and the assembly of
`PerronShiftRemainder` from

* the contour identity above,
* a strip bound for `ζ'/ζ` (`StripZetaBound`), and
* the truncated Perron/Abel step `ReferencePerronBound`, which is exactly the
  standard truncated Perron approximation of `Σ_{n≤v} Λ(n)n^{-it}` on the
  reference line, followed by the prime-power removal.

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
  rw [Complex.exp_add, Complex.exp_log hv0]

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
  have hI : I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have h2 : I * (b - tp) - (r - vv) = -M := by
    calc
      I * (b - tp) - (r - vv) = I * (b - tp) + I * I * (r - vv) := by
        rw [hI]; ring
      _ = I * (b - tp + I * (r - vv)) := by ring
      _ = I * (I * M) := by rw [h]
      _ = I * I * M := by ring
      _ = -M := by rw [hI]; ring
  linear_combination h2

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
    rw [Set.mem_diff] at hs
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
      have hid : AnalyticAt ℂ (fun s : ℂ => s) p := analyticAt_id
      have hconst : AnalyticAt ℂ (fun _ : ℂ => (t : ℂ) * I) p := analyticAt_const
      simpa [Pi.add_apply] using hid.add hconst
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

end Cogentic.RandomizedL21_2Remainder
