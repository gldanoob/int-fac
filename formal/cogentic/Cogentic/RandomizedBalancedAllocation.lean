import Cogentic.RandomizedBalancedRationalSchedule
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Algebra.Order.Field

namespace Cogentic.RandomizedBalancedAllocation

open Filter
open scoped BigOperators Topology

/-- The source's total length for the private coordinates. -/
def coordinateBits (n : ℕ) : ℕ := (n - 1) / 2 - 2

/-- The top private band exponent in (H.18). -/
def topExponent (n k₀ : ℕ) : ℕ := (n - 5) / (2 * k₀) - 1

/-- Floor all but the last share, and give the last group the exact remainder. -/
def bitShare (last : ℕ) (fraction : ℕ → ℚ) (bits i : ℕ) : ℕ :=
  if i < last then ⌊fraction i * bits⌋₊
  else bits - ∑ j ∈ Finset.range last, ⌊fraction j * bits⌋₊

def bandExponent (scale : ℚ) (top : ℕ) : ℕ := ⌊scale * top⌋₊

def baseCount (bits exponent : ℕ) : ℕ := bits ⌈/⌉ exponent

/-- Add the (H.18) reserve determined by the bit length of the initial count. -/
def factorCount (bits exponent : ℕ) : ℕ :=
  let k := baseCount bits exponent
  k + k ⌈/⌉ k.size

theorem coordinateBits_bounds (n : ℕ) {k₀ : ℕ} (hk : 0 < k₀) :
    k₀ * topExponent n k₀ ≤ coordinateBits n ∧
      coordinateBits n < k₀ * (topExponent n k₀ + 2) := by
  have he : coordinateBits n = (n - 5) / 2 := by unfold coordinateBits; omega
  rw [topExponent, ← Nat.div_div_eq_div_mul, ← he]
  let q := coordinateBits n / k₀
  have hlo : k₀ * q ≤ coordinateBits n := Nat.mul_div_le _ _
  have hmod := Nat.mod_lt (coordinateBits n) hk
  have hsum := Nat.div_add_mod (coordinateBits n) k₀
  change k₀ * (q-1) ≤ coordinateBits n ∧ coordinateBits n < k₀ * (q-1+2)
  have hhi : coordinateBits n < k₀ * (q+1) := by
    rw [Nat.mul_succ]
    change k₀ * q + coordinateBits n % k₀ = coordinateBits n at hsum
    omega
  exact ⟨(Nat.mul_le_mul_left _ (Nat.sub_le ..)).trans hlo,
    hhi.trans_le (Nat.mul_le_mul_left _ (by omega))⟩

variable {last : ℕ} {f : ℕ → ℚ}

private theorem floorRat_bounds {x : ℚ} (hx : 0 ≤ x) :
    ((⌊x⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by
  constructor
  · exact_mod_cast Nat.floor_le hx
  · exact_mod_cast (Nat.lt_floor_add_one x).le

private theorem prefix_floor_le
    (hf : ∀ i ≤ last, 0 ≤ f i)
    (hsum : (∑ i ∈ Finset.range (last+1), f i) = 1) (L : ℕ) :
    (∑ j ∈ Finset.range last, ⌊f j * L⌋₊) ≤ L := by
  rw [Finset.sum_range_succ] at hsum
  have h₁ : (∑ j ∈ Finset.range last, f j) ≤ 1 := by linarith only [hsum, hf last le_rfl]
  have h₂ : ((∑ j ∈ Finset.range last, ⌊f j * L⌋₊ : ℕ) : ℚ) ≤ (L : ℚ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range last, f j * L := Finset.sum_le_sum fun j hj =>
        Nat.floor_le (mul_nonneg (hf _ (Finset.mem_range.mp hj).le) (Nat.cast_nonneg _))
      _ = (∑ j ∈ Finset.range last, f j) * L := by rw [Finset.sum_mul]
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg L)
  exact_mod_cast h₂

theorem sum_bitShare
    (hf : ∀ i ≤ last, 0 ≤ f i)
    (hsum : (∑ i ∈ Finset.range (last+1), f i) = 1) (L : ℕ) :
    (∑ i ∈ Finset.range (last+1), bitShare last f L i) = L := by
  rw [Finset.sum_range_succ]
  have he : (∑ i ∈ Finset.range last, bitShare last f L i) =
      ∑ i ∈ Finset.range last, ⌊f i * L⌋₊ := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [bitShare, Finset.mem_range.mp hi]
  rw [he, bitShare, if_neg (Nat.lt_irrefl _), Nat.add_sub_of_le (prefix_floor_le hf hsum L)]

theorem bitShare_rounding
    (hf : ∀ i ≤ last, 0 ≤ f i)
    (hsum : (∑ i ∈ Finset.range (last+1), f i) = 1)
    (L i : ℕ) (hi : i ≤ last) :
    (f i : ℝ) * L - (last + 1) ≤ bitShare last f L i ∧
      (bitShare last f L i : ℝ) ≤ (f i : ℝ) * L + (last + 1) := by
  by_cases hlt : i < last
  · have hfloor := floorRat_bounds (show 0 ≤ f i * L from mul_nonneg (hf i hi) (by positivity))
    simp only [Rat.cast_mul, Rat.cast_natCast] at hfloor
    rw [bitShare, if_pos hlt]
    constructor <;> linarith only [hfloor.1,hfloor.2,Nat.cast_nonneg (α := ℝ) last]
  · have he : i = last := by omega
    subst i
    let U : ℝ := ∑ j ∈ Finset.range last, (f j : ℝ) * L
    let V : ℝ := ∑ j ∈ Finset.range last, (⌊f j * L⌋₊ : ℕ)
    have hV₁ : V ≤ U := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (floorRat_bounds (show 0 ≤ f j * L from
        mul_nonneg (hf j (Finset.mem_range.mp hj).le) (by positivity))).1
      simpa only [Rat.cast_mul, Rat.cast_natCast] using h
    have hV₂ : U ≤ V + last := by
      dsimp only [V,U]
      calc
        _ ≤ ∑ j ∈ Finset.range last, (((⌊f j * L⌋₊ : ℕ) : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro j hj
          have h := (floorRat_bounds (show 0 ≤ f j * L from
            mul_nonneg (hf j (Finset.mem_range.mp hj).le) (by positivity))).2
          simpa only [Rat.cast_mul, Rat.cast_natCast] using h
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    have hU : U + (f last : ℝ) * L = (L : ℝ) := by
      have hsum' : (∑ j ∈ Finset.range (last+1), (f j : ℝ)) = 1 := by exact_mod_cast hsum
      rw [Finset.sum_range_succ] at hsum'
      dsimp only [U]
      rw [← Finset.sum_mul, ← add_mul, hsum', one_mul]
    rw [bitShare, if_neg (Nat.lt_irrefl _), Nat.cast_sub (prefix_floor_le hf hsum L), Nat.cast_sum]
    change _ ≤ (L : ℝ) - V ∧ (L : ℝ) - V ≤ _
    constructor <;> linarith only [hV₁,hV₂,hU,Nat.cast_nonneg (α := ℝ) last]

private theorem tendsto_div_of_bounded_rounding {x y : ℕ → ℝ} {r B : ℝ}
    (hy : Tendsto y atTop atTop)
    (hx : ∀ᶠ n in atTop, r * y n - B ≤ x n ∧ x n ≤ r * y n + B) :
    Tendsto (fun n => x n / y n) atTop (𝓝 r) := by
  have hl : Tendsto (fun n => r - B / y n) atTop (𝓝 r) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := r)).sub (hy.const_div_atTop B)
  have hu : Tendsto (fun n => r + B / y n) atTop (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r)).add (hy.const_div_atTop B)
  apply hl.squeeze' hu
  · filter_upwards [hx,hy.eventually_gt_atTop 0] with n h hn
    simpa only [sub_div, mul_div_cancel_right₀ _ hn.ne'] using
      div_le_div_of_nonneg_right h.1 hn.le
  · filter_upwards [hx,hy.eventually_gt_atTop 0] with n h hn
    simpa only [add_div, mul_div_cancel_right₀ _ hn.ne'] using
      div_le_div_of_nonneg_right h.2 hn.le

/-- The rounded top-knot exponent, normalized by the actual top exponent. -/
theorem bandExponent_ratio_limit {a : ℚ} {top : ℕ → ℕ} (ha : 0 ≤ a)
    (hTop : Tendsto top atTop atTop) :
    Tendsto (fun n => (bandExponent a (top n) : ℝ) / top n) atTop (𝓝 (a : ℝ)) := by
  apply tendsto_div_of_bounded_rounding (B := 1) (tendsto_natCast_atTop_atTop.comp hTop)
  filter_upwards with n
  have e := floorRat_bounds (show 0 ≤ a * top n from mul_nonneg ha (by positivity))
  simp only [Rat.cast_mul, Rat.cast_natCast] at e
  change (a : ℝ) * top n - 1 ≤ ((⌊a * top n⌋₊ : ℕ) : ℝ) ∧
    ((⌊a * top n⌋₊ : ℕ) : ℝ) ≤ (a : ℝ) * top n + 1
  constructor <;> linarith only [e.1,e.2]

private theorem ceilDiv_error (L E : ℕ) (hE : 0 < E) :
    (L : ℝ) / E ≤ (baseCount L E : ℝ) ∧
      (baseCount L E : ℝ) ≤ (L : ℝ) / E + 1 := by
  have hpos : 0 < (E : ℝ) := by exact_mod_cast hE
  have hl : L ≤ E * baseCount L E := (ceilDiv_le_iff_le_mul hE).1 le_rfl
  have hhi : L < E * (L / E + 1) := by
    have h := Nat.mod_lt L hE
    have he := Nat.div_add_mod L E
    rw [Nat.mul_add, mul_one]
    omega
  have hcount : baseCount L E ≤ L / E + 1 := (ceilDiv_le_iff_le_mul hE).2 hhi.le
  refine ⟨(div_le_iff₀ hpos).2 (by exact_mod_cast (mul_comm E _ ▸ hl)), ?_⟩
  have h₀ : ((L / E : ℕ) : ℝ) ≤ (L : ℝ) / E :=
    (le_div_iff₀ hpos).2 (by exact_mod_cast (mul_comm E _ ▸ Nat.mul_div_le L E))
  exact (by exact_mod_cast hcount : (baseCount L E : ℝ) ≤ (L / E : ℕ) + 1).trans (by linarith)

private theorem natSize_grows {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) :
    Tendsto (fun n => (g n).size) atTop atTop := by
  refine tendsto_atTop.2 fun t => ?_
  filter_upwards [hg.eventually_ge_atTop (2 ^ t)] with n hn
  exact (Nat.lt_size.mpr hn).le

/-- Sublinearity of the actual reference count in the input bit length makes
the source's top exponent grow. -/
theorem topExponent_grows_of_sublinear {k₀ : ℕ → ℕ} (hK : Tendsto k₀ atTop atTop)
    (hsmall : Tendsto (fun n => (k₀ n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n => topExponent n (k₀ n)) atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  let c := (m : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [hsmall.eventually_lt_const (show 0 < 1 / (4 * c) by positivity),
    eventually_ge_atTop (10 : ℕ), hK.eventually_gt_atTop 0] with n hn hn₀ hk
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hcross : (4 * c) * (k₀ n : ℝ) < n := by
    have h := (div_lt_iff₀ hn').1 hn
    rw [one_div_mul_eq_div] at h
    rw [mul_comm]
    exact (lt_div_iff₀ (show 0 < 4 * c by positivity)).1 h
  have hmul : 4 * (k₀ n * (m+1)) < n := by
    have hcast : (4 : ℝ) * ((k₀ n : ℝ) * ((m : ℝ) + 1)) < n := by
      dsimp only [c] at hcross
      nlinarith only [hcross]
    exact_mod_cast hcast
  have hbound : (m+1) * (2 * k₀ n) ≤ n - 5 := by
    rw [show (m+1) * (2 * k₀ n) = 2 * (k₀ n * (m+1)) by ring]
    omega
  have hquot := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * k₀ n)).2 hbound
  unfold topExponent
  omega

/-- The integer private-bit and factor quotas at one fixed positive knot
have the manuscript's limiting normalizations. -/
theorem factorCount_limit {a : ℚ} {top k₀ L : ℕ → ℕ}
    (hTop : Tendsto top atTop atTop) (hK : Tendsto k₀ atTop atTop)
    (hL : ∀ᶠ n in atTop, k₀ n * top n ≤ L n ∧ L n < k₀ n * (top n + 2))
    (hf : ∀ i ≤ last, 0 ≤ f i)
    (hsum : (∑ i ∈ Finset.range (last+1), f i) = 1)
    (i : ℕ) (hi : i ≤ last) (hfi : 0 < f i) (ha : 0 < a) :
    Tendsto (fun n => (factorCount (bitShare last f (L n) i) (bandExponent a (top n)) : ℝ) /
      k₀ n) atTop (𝓝 ((f i : ℝ) / (a : ℝ))) := by
  let E (n : ℕ) := bandExponent a (top n)
  let k (n : ℕ) := baseCount (bitShare last f (L n) i) (E n)
  let Lᵢ (n : ℕ) := bitShare last f (L n) i
  have hTop' : Tendsto (fun n => (top n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hTop
  have hK' : Tendsto (fun n => (k₀ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hproduct : Tendsto (fun n => (k₀ n : ℝ) * top n) atTop atTop := hK'.atTop_mul_atTop₀ hTop'
  have hL' : Tendsto (fun n => (L n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ hproduct
    filter_upwards [hL] with n hn
    exact_mod_cast hn.1
  have hBits : Tendsto (fun n => (Lᵢ n : ℝ) / L n) atTop (𝓝 (f i : ℝ)) :=
    tendsto_div_of_bounded_rounding hL'
      (Eventually.of_forall fun n => bitShare_rounding hf hsum (L n) i hi)
  have hE : Tendsto (fun n => (E n : ℝ) / top n) atTop (𝓝 (a : ℝ)) :=
    bandExponent_ratio_limit ha.le hTop
  have hLratio : Tendsto (fun n => (L n : ℝ) / ((k₀ n : ℝ) * top n)) atTop (𝓝 1) := by
    have hdivide := hTop'.const_div_atTop (2:ℝ)
    refine tendsto_const_nhds.squeeze' (by simpa using (tendsto_const_nhds (x := (1:ℝ))).add hdivide)
      ?_ ?_
    · filter_upwards [hL,hK.eventually_gt_atTop 0,hTop.eventually_gt_atTop 0] with n hn hk ht
      have hpos : 0 < (k₀ n : ℝ) * top n := mul_pos (by exact_mod_cast hk) (by exact_mod_cast ht)
      apply (le_div_iff₀ hpos).2
      rw [one_mul]
      exact_mod_cast hn.1
    · filter_upwards [hL,hK.eventually_gt_atTop 0,hTop.eventually_gt_atTop 0] with n hn hk ht
      have hn₀ : 0 < (k₀ n : ℝ) := by exact_mod_cast hk
      have hnₜ : 0 < (top n : ℝ) := by exact_mod_cast ht
      apply (div_le_iff₀ (mul_pos hn₀ hnₜ)).2
      calc
        _ ≤ (k₀ n : ℝ) * (top n + 2) := by exact_mod_cast hn.2.le
        _ = _ := by field_simp
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hEpos : ∀ᶠ n in atTop, 0 < E n := by
    filter_upwards [hE.eventually_const_lt ha'] with n hn
    by_contra! h
    simp [Nat.le_zero.mp h] at hn
  have hquot : Tendsto (fun n => ((Lᵢ n : ℝ) / E n) / k₀ n) atTop
      (𝓝 ((f i : ℝ) / (a : ℝ))) := by
    apply (show Tendsto (fun n => ((Lᵢ n : ℝ) / L n) *
      ((L n : ℝ) / ((k₀ n : ℝ) * top n)) / ((E n : ℝ) / top n)) atTop
      (𝓝 ((f i : ℝ) / (a : ℝ))) by
        have h := (hBits.mul hLratio).div hE ha'.ne'
        rw [mul_one] at h
        exact h.congr' (Eventually.of_forall fun _ => by simp only [Pi.div_apply])).congr'
    filter_upwards [hEpos,hK.eventually_gt_atTop 0,hTop.eventually_gt_atTop 0,
      hL'.eventually_gt_atTop 0] with n hn hk ht hLn
    have hk' : (k₀ n : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have ht' : (top n : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    have he' : (E n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hk',ht',he',hLn.ne']
  have hkLimit : Tendsto (fun n => (k n : ℝ) / k₀ n) atTop (𝓝 ((f i : ℝ) / (a : ℝ))) := by
    have hupper := hquot.add (hK'.const_div_atTop (1:ℝ))
    refine hquot.squeeze' (by simpa only [add_zero] using hupper) ?_ ?_
    · filter_upwards [hEpos] with n hn
      exact div_le_div_of_nonneg_right (ceilDiv_error (Lᵢ n) (E n) hn).1 (Nat.cast_nonneg _)
    · filter_upwards [hEpos] with n hn
      rw [← add_div]
      exact div_le_div_of_nonneg_right (ceilDiv_error (Lᵢ n) (E n) hn).2 (Nat.cast_nonneg _)
  have hr : 0 < (f i : ℝ) / (a : ℝ) := div_pos (by exact_mod_cast hfi) ha'
  have hkGrow : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 fun m => ?_
    filter_upwards [hkLimit.eventually_const_lt (show (f i : ℝ) / (a : ℝ) / 2 < _ by linarith),
      hK'.eventually_ge_atTop ((m : ℝ) / ((f i : ℝ) / (a : ℝ) / 2)),
      hK.eventually_gt_atTop 0] with n hn hm hkn
    have hkn' : 0 < (k₀ n : ℝ) := by exact_mod_cast hkn
    have hbound := (div_le_iff₀ (show 0 < (f i : ℝ) / (a : ℝ) / 2 by positivity)).1 hm
    have hlt := (lt_div_iff₀ hkn').1 hn
    exact_mod_cast (by linarith only [hbound,hlt] : (m : ℝ) ≤ (k n : ℝ))
  have hsize := natSize_grows hkGrow
  have hsize' : Tendsto (fun n => ((k n).size : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  have hreserve : Tendsto (fun n => ((k n ⌈/⌉ (k n).size : ℕ) : ℝ) / k₀ n) atTop (𝓝 0) := by
    have hupper := (hkLimit.mul (hsize'.const_div_atTop (1:ℝ))).add
      (hK'.const_div_atTop (1:ℝ))
    refine tendsto_const_nhds.squeeze' (by simpa only [mul_zero,zero_add] using hupper)
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [hsize.eventually_gt_atTop 0] with n hn
    have h := div_le_div_of_nonneg_right (ceilDiv_error (k n) (k n).size hn).2
      (Nat.cast_nonneg (α := ℝ) (k₀ n))
    simp only [baseCount, add_div] at h
    convert h using 1
    ring
  have hfinal := hkLimit.add hreserve
  simpa only [add_zero,factorCount,Nat.cast_add,add_div,k,Lᵢ,E] using hfinal

def privateFraction (scale weight : ℕ → ℚ) (moment : ℚ) (i : ℕ) : ℚ :=
  scale i * weight i / moment

/-- The actual count at a fixed knot, converted back to weight units. -/
noncomputable def realizedWeight (last : ℕ) (a w : ℕ → ℚ) (M : ℚ)
    (k₀ n i : ℕ) : ℝ :=
  (M : ℝ) * ((factorCount (bitShare last (privateFraction a w M) (coordinateBits n) i)
    (bandExponent (a i) (topExponent n k₀)) : ℝ) / k₀)

private theorem fractions_normalized {a w : ℕ → ℚ} {M : ℚ}
    (hM : 0 < M) (hmoment : ∑ i ∈ Finset.range (last+1), a i * w i = M) :
    (∑ i ∈ Finset.range (last+1), privateFraction a w M i) = 1 := by
  simp_rw [privateFraction]
  rw [← Finset.sum_div, hmoment, div_self hM.ne']

/-- The coordinate allocation keeps the exact bit total. Every rounded stage
weight converges to the certified scalar weight of the fixed schedule. -/
theorem private_allocation_limits {a w : ℕ → ℚ} {M : ℚ} {k₀ : ℕ → ℕ}
    (hK : Tendsto k₀ atTop atTop)
    (hsmall : Tendsto (fun n => (k₀ n : ℝ) / n) atTop (𝓝 0))
    (ha : ∀ i ≤ last, 0 < a i) (hw : ∀ i ≤ last, 0 < w i) (hM : 0 < M)
    (hmoment : ∑ i ∈ Finset.range (last+1), a i * w i = M) :
    (∀ n, (∑ i ∈ Finset.range (last+1),
      bitShare last (privateFraction a w M) (coordinateBits n) i) = coordinateBits n) ∧
    ∀ i ≤ last, Tendsto (fun n => realizedWeight last a w M (k₀ n) n i) atTop (𝓝 (w i : ℝ)) := by
  have hnorm := fractions_normalized hM hmoment
  have hpos (i : ℕ) (hi : i ≤ last) : 0 < privateFraction a w M i :=
    div_pos (mul_pos (ha i hi) (hw i hi)) hM
  refine ⟨fun n => sum_bitShare (fun i hi => (hpos i hi).le) hnorm (coordinateBits n), ?_⟩
  intro i hi
  have hL : ∀ᶠ n in atTop,
      k₀ n * topExponent n (k₀ n) ≤ coordinateBits n ∧
        coordinateBits n < k₀ n * (topExponent n (k₀ n) + 2) := by
    filter_upwards [hK.eventually_gt_atTop 0] with n hn using coordinateBits_bounds n hn
  have hc := factorCount_limit (topExponent_grows_of_sublinear hK hsmall) hK hL
    (fun j hj => (hpos j hj).le) hnorm i hi (hpos i hi) (ha i hi)
  have hs := (tendsto_const_nhds (x := (M : ℝ))).mul hc
  have he : (M : ℝ) * ((privateFraction a w M i : ℝ) / (a i : ℝ)) = (w i : ℝ) := by
    simp only [privateFraction, Rat.cast_div, Rat.cast_mul]
    field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast hM.ne',
      show (a i : ℝ) ≠ 0 by exact_mod_cast (ha i hi).ne']
  rw [he] at hs
  exact hs

/-- Every strict occurrence and stage-work cap remains valid past a common
input threshold, and the realized moment converges to the exact scalar one. -/
theorem private_allocation_preserves_caps {a w : ℕ → ℚ} {M : ℚ} {k₀ : ℕ → ℕ}
    (hK : Tendsto k₀ atTop atTop)
    (hsmall : Tendsto (fun n => (k₀ n : ℝ) / n) atTop (𝓝 0))
    (ha : ∀ i ≤ last, 0 < a i) (hw : ∀ i ≤ last, 0 < w i) (hM : 0 < M)
    (hmoment : ∑ i ∈ Finset.range (last+1), a i * w i = M)
    (hcount : (∑ i ∈ Finset.range (last+1), w i) < 2 * M)
    (front : ℕ → ℝ) (C : ℝ)
    (hgate : ∀ i ≤ last, front i + (∑ j ∈ Finset.Ico i (last+1), (w j : ℝ)) < C) :
    (Tendsto (fun n => ∑ i ∈ Finset.range (last+1),
      ((bandExponent (a i) (topExponent n (k₀ n)) : ℝ) / topExponent n (k₀ n)) *
      realizedWeight last a w M (k₀ n) n i) atTop (𝓝 (M : ℝ))) ∧
    ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (last+1),
        factorCount (bitShare last (privateFraction a w M) (coordinateBits n) i)
          (bandExponent (a i) (topExponent n (k₀ n)))) < 2 * k₀ n ∧
      ∀ i ≤ last, front i + (∑ j ∈ Finset.Ico i (last+1),
        realizedWeight last a w M (k₀ n) n j) < C := by
  let v (i n : ℕ) := realizedWeight last a w M (k₀ n) n i
  have hlim := (private_allocation_limits hK hsmall ha hw hM hmoment).2
  have hmReal : (∑ i ∈ Finset.range (last+1), (a i : ℝ) * (w i : ℝ)) = (M : ℝ) := by
    exact_mod_cast hmoment
  constructor
  · rw [← hmReal]
    refine tendsto_finsetSum _ fun i hi => ?_
    have hil := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (bandExponent_ratio_limit (ha i hil).le (topExponent_grows_of_sublinear hK hsmall)).mul
      (hlim i hil)
  have htotal : Tendsto (fun n => ∑ j ∈ Finset.range (last+1), v j n) atTop
      (𝓝 (∑ j ∈ Finset.range (last+1), (w j : ℝ))) :=
    tendsto_finsetSum _ fun j hj => hlim j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hthreshold : (∑ j ∈ Finset.range (last+1), (w j : ℝ)) < 2 * (M : ℝ) := by
    exact_mod_cast hcount
  have hcap : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (last+1),
      front i + (∑ j ∈ Finset.Ico i (last+1), v j n) < C := by
    apply ((Finset.range (last+1)).eventually_all).2
    intro i hi
    have ht : Tendsto (fun n => ∑ j ∈ Finset.Ico i (last+1), v j n) atTop
        (𝓝 (∑ j ∈ Finset.Ico i (last+1), (w j : ℝ))) :=
      tendsto_finsetSum _ fun j hj => hlim j (Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2)
    exact ((tendsto_const_nhds (x := front i)).add ht).eventually_lt_const
      (hgate i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  filter_upwards [htotal.eventually_lt_const hthreshold, hK.eventually_gt_atTop 0, hcap]
    with n hn hk hstages
  refine ⟨?_, fun i hi => hstages i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))⟩
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hk' : 0 < (k₀ n : ℝ) := by exact_mod_cast hk
  dsimp only [v,realizedWeight] at hn
  rw [← Finset.mul_sum, ← Finset.sum_div, ← Nat.cast_sum] at hn
  have h := (mul_lt_mul_iff_of_pos_left hM').1 (hn.trans_eq (mul_comm _ _))
  have he := (div_lt_iff₀ hk').1 h
  exact_mod_cast he

#print axioms sum_bitShare
#print axioms factorCount_limit
#print axioms private_allocation_preserves_caps

end Cogentic.RandomizedBalancedAllocation
