import Cogentic.Driver
import TwoThirdsCost
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Cogentic.Fixed

open TwoThirdsSearch TwoThirdsFactor TwoThirdsCost

/-- If b is the input bit length, z differs from log₂ b by at most one.
    The quotient inside the cube root is rounded down exactly. -/
def z (b : ℕ) := b.log2 + 1
def d (b : ℕ) := Nat.nthRoot 3 (b / z b)
def h (b : ℕ) := d b * z b
def v (b : ℕ) := d b * h b
def beta (b : ℕ) := 1000*h b
def B (b : ℕ) : ℕ := 2^(beta b)
def A (b : ℕ) : ℕ := 2^(10000*h b)
def K₁ (b : ℕ) : ℕ := 2^(100*h b)
def invWidth (b : ℕ) : ℕ := 2^(3*h b)
def U (b : ℕ) : ℕ := 2^(100000*v b)
def precision (b : ℕ) := 64*(d b)^3*(2*d b*B b+1)*b

/-- Reading the base-m root in binary makes at most b candidate comparisons. -/
def rootBase (n : ℕ) : ℕ :=
  let b := n.log2+1
  rootDigits (n-1) (d b) b 0 + 1

def parameters (tryPair : ℕ → TryPair) (n : ℕ) : BoxParameters :=
  let b := n.log2+1
  ⟨beta b, b, U b, A b, rootBase n, tryPair n⟩

theorem degree_floor (b : ℕ) : (d b)^3*z b ≤ b ∧ b < (d b+1)^3*z b := by
  have pos : 0 < z b := by simp [z]
  exact ⟨(Nat.le_div_iff_mul_le pos).mp (Nat.pow_nthRoot_le_iff.mpr (.inl (by decide))),
    (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) _)⟩

theorem degree_pos {b : ℕ} (hb : 0 < b) : 0 < d b := by
  change 1 ≤ Nat.nthRoot 3 (b/z b)
  apply (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr
  simp only [one_pow]
  apply (Nat.le_div_iff_mul_le (by simp [z])).mpr
  simpa [z] using (Nat.log2_lt hb.ne').mpr (Nat.lt_two_pow_self (n := b))

private theorem square_le_two_pow (j : ℕ) (hj : 4 ≤ j) : j^2 ≤ 2^j := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [Nat.pow_succ 2 j]
    nlinarith [Nat.mul_le_mul_left j hj]

theorem degree_grows (k : ℕ) : ∃ b₀, ∀ b ≥ b₀, k ≤ d b := by
  let j₀ := max 4 (2*k^3)
  refine ⟨2^j₀, fun b hbig => ?_⟩
  have hb : 0 < b := (Nat.pow_pos (by decide : 0 < 2)).trans_le hbig
  have enough := (Nat.le_log2 hb.ne').mpr hbig
  have j4 := (le_max_left 4 (2*k^3)).trans enough
  have coeff := (le_max_right 4 (2*k^3)).trans enough
  apply (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr
  apply (Nat.le_div_iff_mul_le (by simp [z])).mpr
  calc
    k^3*z b ≤ k^3*(2*b.log2) := Nat.mul_le_mul_left _ (by unfold z; omega)
    _ = (2*k^3)*b.log2 := by ring
    _ ≤ b.log2^2 := by simpa [sq] using Nat.mul_le_mul_right b.log2 coeff
    _ ≤ 2^b.log2 := square_le_two_pow _ j4
    _ ≤ b := Nat.log2_self_le hb.ne'

private theorem digits_floor {n k bits lo : ℕ} (low : lo^k ≤ n) (top : n < (lo+2^bits)^k) :
    let r := rootDigits n k bits lo
    r^k ≤ n ∧ n < (r+1)^k ∧ r < lo+2^bits := by
  induction bits generalizing lo with
  | zero => simpa [rootDigits] using And.intro low (And.intro top (by omega : lo < lo+1))
  | succ bits ih =>
    simp only [rootDigits]
    rw [Nat.pow_succ] at top ⊢
    split
    next isLow =>
      have eq : lo+2^bits+2^bits = lo+2^bits*2 := by omega
      simpa only [eq] using ih isLow (eq ▸ top)
    next isHigh =>
      have ⟨hl,hu,hr⟩ := ih low (Nat.lt_of_not_ge isHigh)
      exact ⟨hl,hu,by omega⟩

theorem rootBase_spec {n : ℕ} (hn : 2 ≤ n) :
    (rootBase n-1)^d (n.log2+1) < n ∧ n ≤ (rootBase n)^d (n.log2+1) ∧
    rootBase n ≤ 2^(n.log2+1) := by
  let b := n.log2+1
  have dp := degree_pos (b := b) (by simp [b])
  have fits : n < 2^b := Nat.lt_log2_self
  have power : 2^b ≤ (2^b)^d b := Nat.le_self_pow dp.ne' _
  have ⟨lo,hi,cap⟩ := digits_floor (n := n-1) (k := d b) (bits := b) (lo := 0)
    (by simp [Nat.zero_pow dp]) (by simp only [zero_add]; omega)
  change (rootDigits (n-1) (d b) b 0+1-1)^d b < n ∧ n ≤ (rootDigits (n-1) (d b) b 0+1)^d b ∧ _
  simp only [Nat.add_sub_cancel]
  exact ⟨by omega,by omega,by unfold rootBase; change rootDigits (n-1) (d b) b 0+1 ≤ 2^b; omega⟩

theorem parameters_grow (attempt : ℕ → TryPair) (k : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, k ≤ (parameters attempt n).beta := by
  refine ⟨2^(2^k), fun n hn => ?_⟩
  have pos := (Nat.pow_pos (by decide : 0 < 2)).trans_le hn
  have a := (Nat.le_log2 pos.ne').mpr hn
  let b := n.log2+1
  have bp : 0 < b := by simp [b]
  have bk : 2^k ≤ b := by dsimp [b]; omega
  have order := (Nat.le_log2 bp.ne').mpr bk
  have dp := degree_pos bp
  have hh := Nat.le_mul_of_pos_left (z b) dp
  change k ≤ 1000*(d b*z b)
  dsimp [z] at hh ⊢
  omega

theorem scale_bounds {b : ℕ} (hb : 0 < b) :
    v b ≤ scale b ∧ b^2*z b ≤ 64*(v b)^3 := by
  have ⟨low,high⟩ := degree_floor b
  have dp := degree_pos hb
  have lo : (v b)^3 ≤ b^2*z b := by
    calc (v b)^3 = ((d b)^3*z b)^2*z b := by unfold v h; ring
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left low 2)
  have hi : b ≤ 8*((d b)^3*z b) := by
    calc b ≤ (d b+1)^3*z b := high.le
         _ ≤ (2*d b)^3*z b := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 3)
         _ = _ := by ring
  refine ⟨(Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp
    (lo.trans (scale_cubed b hb.ne').1), ?_⟩
  calc b^2*z b ≤ (8*((d b)^3*z b))^2*z b := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hi 2)
       _ = _ := by unfold v h; ring

private theorem scales {b : ℕ} (hb : 0 < b) : 1 ≤ z b ∧ z b ≤ h b ∧ h b ≤ v b := by
  have dp := degree_pos hb
  exact ⟨by simp [z], Nat.le_mul_of_pos_left _ dp, Nat.le_mul_of_pos_left _ dp⟩

theorem index_bound {b : ℕ} (hb : 0 < b) : indexCap b (beta b) ≤ 2^(beta b + v b) := by
  obtain ⟨zp,_,_⟩ := scales hb
  have dp := degree_pos hb
  have large : b ≤ (2*d b)^3*z b := (degree_floor b).2.le.trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 3))
  have clog : Nat.clog 2 (6*b) ≤ 4*z b := by
    apply Nat.clog_le_of_le_pow
    calc 6*b ≤ 8*2^(z b) := Nat.mul_le_mul (by decide) Nat.lt_log2_self.le
         _ = 2^(3+z b) := (Nat.pow_add 2 3 (z b)).symm
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have top : b*Nat.clog 2 (6*b) ≤ v b*beta b := by
    apply (Nat.mul_le_mul large clog).trans
    unfold v beta h
    ring_nf
    omega
  have quotient : b*Nat.clog 2 (6*b) / beta b ≤ v b :=
    (Nat.div_le_div_right top).trans_eq (Nat.mul_div_cancel _ (by unfold beta h; positivity))
  rw [indexCap, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) quotient)

private theorem target_card (b : ℕ) : (dyadicTargets (beta b)).card ≤ B b := by
  have subset : dyadicTargets (beta b) ⊆ Finset.Icc 1 (B b) := by
    intro a ha
    have mem := mem_dyadicTargets.mp ha
    exact Finset.mem_Icc.mpr ⟨mem.1.pos,mem.2.2⟩
  simpa using Finset.card_le_card subset

/-- The four-box loop has the paper's leading coefficient 400000 in binary
    units of v. Every other term is a multiple of h, z, or a constant. -/
theorem search_calls {n b : ℕ} (hn : 2 ≤ n) (hb : 0 < b) (attempt : TryPair) :
    (collect hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt)
      (dyadicTargets (beta b)).sort).2 ≤ 2^(400000*v b+21000*h b+8*z b+4) := by
  let gs := (dyadicTargets (beta b)).sort
  have bound := collect_cost hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt) gs _
    (fun g => searchBox_cost _ _ _ g attempt)
  have len : gs.length ≤ B b := by simpa [gs] using target_card b
  have bits : b ≤ 2^z b := Nat.lt_log2_self.le
  apply bound.trans
  calc
    _ ≤ B b * ((2*(2^z b)^2*U b*A b) * ((2*(2^z b)^2*U b) *
        ((2*(2^z b)^2*U b*A b)*(2*(2^z b)^2*U b)))) := by gcongr
    _ = _ := by
      unfold B beta A U
      have twice (e : ℕ) : 2 * 2^e = 2^(1+e) := by rw [Nat.pow_add, Nat.pow_one]
      simp only [← Nat.pow_mul, twice, ← Nat.pow_add]
      congr 1; ring

theorem search_calls_scale {n b : ℕ} (hn : 2 ≤ n) (hb : 0 < b) (attempt : TryPair) :
    (collect hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt)
      (dyadicTargets (beta b)).sort).2 ≤ 2^(421012*scale b) := by
  have ⟨_,zh,hv⟩ := scales hb
  have vs := (scale_bounds hb).1
  have := (scales hb).1
  exact (search_calls hn hb attempt).trans (Nat.pow_le_pow_right (by decide) (by omega))

private theorem degree_le_bits (b : ℕ) : d b ≤ b := by
  have ⟨lo,_⟩ := degree_floor b
  exact (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans
    ((Nat.le_mul_of_pos_right _ (by simp [z])).trans lo)

theorem precision_bound (b : ℕ) : precision b ≤ 2^(8+5*z b+beta b) := by
  have small : b ≤ 2^z b := Nat.lt_log2_self.le
  have deg := (degree_le_bits b).trans small
  have row : 2*d b*B b+1 ≤ 2^(2+z b+beta b) := by
    have p : 0 < 2^z b * B b := by unfold B; positivity
    have le := Nat.mul_le_mul_right (B b) deg
    rw [Nat.pow_add, Nat.pow_add]
    change 2*d b*B b+1 ≤ 4*(2^z b)*B b
    nlinarith
  unfold precision
  calc _ ≤ 64*(2^z b)^3*2^(2+z b+beta b)*2^z b := by gcongr
       _ = _ := by
         change 2^6*(2^z b)^3*2^(2+z b+beta b)*2^z b = _
         simp only [← Nat.pow_mul, ← Nat.pow_add]; congr 1; ring

/-- Explicit bit bound on the exponent that the actual splitter receives, once
    the extractor stays inside the published 64 d³ (2 d B + 1) L₀ guard. -/
theorem splitter_exponent {n b : ℕ} (hn : 2 ≤ n) (hb : 0 < b) (attempt : TryPair)
    (bound : ∀ g a j c k e, attempt g a j c k = some (.exponent e) → e ≤ 2^precision b) :
    match (collect hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt)
      (dyadicTargets (beta b)).sort).1 with
    | .divisor .. => True
    | .orders e .. => saturate e b (beta b) ≤ 2^(2^(2017*scale b)) := by
  let gs := (dyadicTargets (beta b)).sort
  have hres := search_saturated_size hn gs (2*b^2*U b*A b) (2*b^2*U b)
    (precision b) b (beta b) attempt bound
  have len : gs.length ≤ B b := by simpa [gs] using target_card b
  have ⟨zp,zh,hv⟩ := scales hb
  have scaleV := (scale_bounds hb).1
  let X := 2^(2013*scale b)
  have p : precision b * gs.length ≤ X := by
    apply (Nat.mul_le_mul (precision_bound b) len).trans
    change 2^(8+5*z b+beta b)*2^beta b ≤ 2^(2013*scale b)
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by unfold beta; omega)
  have idx : indexCap b (beta b) ≤ X := (index_bound hb).trans
    (Nat.pow_le_pow_right (by decide) (by unfold beta; omega))
  have xp : 0 < X := by unfold X; positivity
  have cap : 1+precision b*gs.length+10*indexCap b (beta b) ≤ 2^(2017*scale b) := by
    calc _ ≤ 16*X := by omega
         _ = 2^(4+2013*scale b) := (Nat.pow_add 2 4 _).symm
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  change (match (collect hn (searchBox n _ _ attempt) gs).1 with
    | .divisor .. => True
    | .orders e .. => saturate e b (beta b) ≤ 2^(2^(2017*scale b)))
  cases eq : (collect hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt) gs).1 with
  | divisor => trivial
  | orders e _ _ _ _ =>
    rw [eq] at hres
    exact Nat.le_trans hres (Nat.pow_le_pow_right (by decide) cap)

def bracketExponent (b : ℕ) := (19*(100*h b)+19)/20

structure StageGuards (n b : ℕ) : Prop where
  parameters : 9 ≤ n ∧ 10 ≤ d b ∧ 10 ≤ b ∧ 16 ≤ K₁ b ∧ 20 ≤ B b
  heights : n ≤ 2^(d b*b) ∧ rootBase n ≤ 2^b ∧ A b ≤ 2^b ∧ B b ≤ 2^b ∧ K₁ b ≤ 2^b
  roots : 16*d b ≤ invWidth b ∧ 8*d b < 2^bracketExponent b ∧ 2*invWidth b ≤ 2^b
  factorBase : (d b)^2 < B b ∧ 2*(d b+1) < B b
  gaussian : 4*(B b)^4 ≤ U b ∧ d b*(A b)^d b ≤ U b
  markRange : 4*d b*A b ≤ rootBase n
  precisionGuard : 100*h b ≤ 64*(d b)^3*(d b+1)*b

/-- The numeric guards for TryPair, the grid and the admissible perturbation box.
    The polynomial height and relation-dependent guards are separate. -/
theorem stage_guards {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ d (n.log2+1)) :
    StageGuards n (n.log2+1) := by
  let b := n.log2+1
  change StageGuards n b
  change 10004 ≤ d b at big
  have bp : 0 < b := by simp [b]
  have ⟨zp,zh,hv⟩ := scales bp
  have hp : 0 < h b := by omega
  have bfits : b ≤ 2^z b := Nat.lt_log2_self.le
  have dfits := (degree_le_bits b).trans bfits
  have degBig := degree_le_bits b
  have hd : 10003*(h b*d b) < b := by
    calc _ < d b*(h b*d b) := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.mul_pos hp (by omega))
         _ = (d b)^3*z b := by unfold h; ring
         _ ≤ b := (degree_floor b).1
  have hd1 : 10003*h b < b := (Nat.mul_le_mul_left 10003 (Nat.le_mul_of_pos_right _ (by omega : 0 < d b))).trans_lt hd
  have btoN : 2^(b-1) ≤ n := by simpa [b] using Nat.log2_self_le (by omega : n ≠ 0)
  have n9 : 9 ≤ n := by
    have e : (4:ℕ) ≤ b-1 := by omega
    exact Nat.le_trans (by decide : 9 ≤ 2^4) ((Nat.pow_le_pow_right (by decide) e).trans btoN)
  have mroot := rootBase_spec hn
  have twice (k j : ℕ) : 2^k*2^j = 2^(k+j) := (Nat.pow_add ..).symm
  have bracket : bracketExponent b = 95*h b := by unfold bracketExponent; omega
  have dz : d b*(A b)^d b ≤ 2^(z b+10000*h b*d b) := by
    rw [Nat.pow_add, Nat.pow_mul 2 (10000*h b)]
    exact Nat.mul_le_mul_right _ dfits
  have gauss : d b*(A b)^d b ≤ U b := dz.trans (Nat.pow_le_pow_right (by decide) (by
    change z b+10000*h b*d b ≤ 100000*(d b*h b)
    rw [Nat.mul_comm (d b), Nat.mul_assoc 10000]
    have hp2 := Nat.le_mul_of_pos_right (h b) (by omega : 0 < d b)
    omega))
  have mark : 4*d b*A b ≤ 2^(2+z b+10000*h b) := by
    rw [Nat.pow_add, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 dfits)
  have markSmall : (4*d b*A b)^d b ≤ n := by
    apply (Nat.pow_le_pow_left mark (d b)).trans
    rw [← Nat.pow_mul]
    apply (Nat.pow_le_pow_right (n := 2) (j := b-1) (by decide) ?_).trans btoN
    have h := Nat.mul_le_mul_right (d b) (show 2+z b+10000*h b ≤ 10003*h b by omega)
    rw [Nat.mul_assoc 10003] at h
    omega
  have key : 2^4 ≤ K₁ b := Nat.pow_le_pow_right (by decide) (show 4 ≤ 100*h b by omega)
  refine ⟨⟨n9,by omega,by omega, key, ?_⟩,
    ⟨?_, mroot.2.2, ?_, ?_, ?_⟩, ⟨?_,?_,?_⟩, ⟨?_,?_⟩, ⟨?_,gauss⟩,
    (Nat.pow_le_pow_iff_left (by omega : d b ≠ 0)).mp (markSmall.trans mroot.2.1), ?_⟩
  · exact (show 20 ≤ 2^5 by decide).trans (Nat.pow_le_pow_right (by decide) (show 5 ≤ beta b by unfold beta; omega))
  · exact (Nat.lt_log2_self (n := n)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact Nat.pow_le_pow_right (by decide) (by unfold beta; omega)
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (Nat.mul_le_mul_left 16 dfits).trans ((twice 4 _).le.trans
      (Nat.pow_le_pow_right (by decide) (by
        have hi := Nat.mul_le_mul_right (z b) big; change 4+z b ≤ 3*h b; unfold h; omega)))
  · exact (Nat.mul_le_mul_left 8 dfits).trans_lt ((twice 3 _).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by rw [bracket]; omega)))
  · exact (twice 1 _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (Nat.pow_le_pow_left dfits 2).trans_lt ((Nat.pow_mul 2 (z b) 2).symm.trans_lt
      (Nat.pow_lt_pow_right (by decide) (by unfold beta; omega)))
  · have w : 0 < 2^z b := Nat.pow_pos (by decide)
    exact (show 2*(d b+1) ≤ 4*2^z b by omega).trans_lt ((twice 2 _).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by unfold beta; omega)))
  · change 4*(2^beta b)^4 ≤ 2^(100000*v b)
    rw [← Nat.pow_mul]
    change 2^2*2^(beta b*4) ≤ 2^(100000*v b)
    rw [twice]
    exact Nat.pow_le_pow_right (by decide) (by unfold beta; omega)
  · apply (show 100*h b ≤ b by omega).trans
    exact Nat.le_mul_of_pos_left _ (by positivity)

theorem eventually_stage_guards : ∃ n₀, ∀ n ≥ n₀, StageGuards n (n.log2+1) := by
  obtain ⟨b₀,large⟩ := degree_grows 10004
  refine ⟨2^(b₀+1), fun n hn => ?_⟩
  have positive := (Nat.pow_pos (by decide : 0 < 2)).trans_le hn
  have bits := (Nat.le_log2 positive.ne').mpr hn
  have two : 2 ≤ n := by
    apply (show 2^1 ≤ 2^(b₀+1) from Nat.pow_le_pow_right (by decide) (by omega)).trans hn
  exact stage_guards two (large _ (by omega))

/-- The cube of v differs from b²z by a relative factor at most (1+1/d)^6.
    The binary logarithm z and the degree d have only additive rounding errors. -/
theorem rounding_bounds {b : ℕ} (hb : 0 < b) :
    2^(z b-1) ≤ b ∧ b < 2^(z b) ∧
    (v b)^3 ≤ b^2*z b ∧ b^2*z b*(d b)^6 ≤ (d b+1)^6*(v b)^3 := by
  have ⟨lo,hi⟩ := degree_floor b
  refine ⟨by simpa [z] using Nat.log2_self_le hb.ne', Nat.lt_log2_self, ?_, ?_⟩
  · calc (v b)^3 = ((d b)^3*z b)^2*z b := by unfold v h; ring
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left lo 2)
  · calc _ ≤ ((d b+1)^3*z b)^2*z b*(d b)^6 :=
           Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hi.le 2))
         _ = _ := by unfold v h; ring

/-- The correction to the coefficient 400000 in the candidate-count exponent
    is smaller than any prescribed positive fraction of v at large bit lengths. -/
theorem search_calls_leading (k : ℕ) (hk : 0 < k) :
    ∃ b₀, ∀ b ≥ b₀, ∀ n (hn : 2 ≤ n) (attempt : TryPair),
      (collect hn (searchBox n (2*b^2*U b*A b) (2*b^2*U b) attempt)
        (dyadicTargets (beta b)).sort).2 ≤ 2^(400000*v b+v b/k) := by
  obtain ⟨q₀,large⟩ := degree_grows (21012*k)
  refine ⟨q₀+1, fun b hb n hn attempt => ?_⟩
  have pos : 0 < b := by omega
  have deg := large b (by omega)
  have ⟨zp,zh,_⟩ := scales pos
  have lower : (21000*h b+8*z b+4)*k ≤ v b := by
    calc _ ≤ (21012*h b)*k := Nat.mul_le_mul_right _ (by omega)
         _ = (21012*k)*h b := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ deg
  have small := (Nat.le_div_iff_mul_le hk).mpr lower
  exact (search_calls hn pos attempt).trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- On this single schedule, only the large-input per-prime box coverage
    remains as a hypothesis of the qualitative prime-factor output theorem. -/
theorem fixed_factorization (line : DirichletLZerosOnLine) (attempt : ℕ → TryPair)
    (covered : ∃ n₀ : ℕ, ∀ n ≥ n₀, (parameters attempt n).Covers n) :
    ∃ (threshold k : ℕ) (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n)
      (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2 ≤ n), threshold ≤ n → (schedules n hn).parameters = parameters attempt n ∧
        (schedules n hn).candidates = (dyadicTargets (beta (n.log2+1))).sort) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (charge : ℕ → ℕ) (cap : ℕ),
        (∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) →
        let tree := factor (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        tree.work charge ≤ (2*n.log2-1)*cap :=
  factor_from_dyadic_boxes line (parameters attempt) (parameters_grow attempt) covered

end Cogentic.Fixed

#print axioms Cogentic.Fixed.fixed_factorization
#print axioms Cogentic.Fixed.splitter_exponent
#print axioms Cogentic.Fixed.stage_guards
