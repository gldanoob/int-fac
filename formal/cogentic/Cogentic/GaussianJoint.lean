import Cogentic.GaussianMarginal
import Cogentic.GaussianCRT

open Real
open scoped BigOperators

namespace Cogentic.Window

noncomputable section

private theorem scalar_normalizer_bounds (c μ M S e : ℝ) (hM : 0 < M) (hs : 2 ≤ S/M)
    (he : 3*Real.exp (-π*(S/M)^2) ≤ e) (hsmall : e ≤ 1/4) :
    let f := fun i : ℤ => coeffGaussian (c+M*i) μ S
    Summable f ∧ (1-e)*(S/M) ≤ ∑' i, f i ∧ (∑' i, f i) ≤ (1+e)*(S/M) := by
  dsimp only
  have ht : 0 < S/M := by linarith
  let Z := ∑' i : ℤ, coeffGaussian (c+M*i) μ S
  have hz : |Z/(S/M)-1| ≤ e := by
    dsimp [Z]
    simp_rw [coeffGaussian_progression _ _ _ _ _ hM]
    exact (shifted_gaussian_normalizer _ _ (by linarith)).trans he
  have lo := (le_div_iff₀ ht).mp (by linarith [(abs_le.mp hz).1] : 1-e ≤ Z/(S/M))
  have hi := (div_le_iff₀ ht).mp (by linarith [(abs_le.mp hz).2] : Z/(S/M) ≤ 1+e)
  refine ⟨?_,lo,hi⟩
  by_contra nons
  have eq : Z=0 := tsum_eq_zero_of_not_summable nons
  exact ((mul_pos (by linarith : 0 < 1-e) ht).trans_le lo).ne' eq

/-- The entire CRT lattice has finite Gaussian weight. Its normalizing
    constant is uniform in the second center and in both residue functions. -/
theorem gaussian_joint_normalizer (c Q S M t μ : ℝ) (r m : ℤ → ℝ)
    (hQ : 0 < Q) (hM : 0 < M) (hs : 2 ≤ S/Q) (ht : 2 ≤ t/M) :
    let τ := S/Q
    let υ := t/M
    let e := max (3*Real.exp (-π*τ^2)) (3*Real.exp (-π*υ^2))
    let W := fun k : ℤ × ℤ => coeffGaussian (c+Q*k.1) μ S * coeffGaussian (r k.1+M*k.2) (m k.1) t
    Summable W ∧ 0 < ∑' k, W k ∧ |τ*υ/(∑' k, W k)-1| ≤ 6*e := by
  dsimp only
  let τ := S/Q
  let υ := t/M
  let e := max (3*Real.exp (-π*τ^2)) (3*Real.exp (-π*υ^2))
  let p := fun i : ℤ => coeffGaussian (c+Q*i) μ S
  let g := fun i j : ℤ => coeffGaussian (r i+M*j) (m i) t
  let W := fun k : ℤ × ℤ => p k.1*g k.1 k.2
  have small (a : ℝ) (ha : 2 ≤ a) : 3*Real.exp (-π*a^2) ≤ 1/4 := by
    have big : 12 ≤ Real.exp (π*a^2) := by
      nlinarith [Real.add_one_le_exp (π*a^2), Real.pi_gt_three,
        mul_nonneg Real.pi_pos.le (show 0 ≤ a^2-4 by nlinarith)]
    rw [neg_mul,Real.exp_neg]
    have := inv_anti₀ (by norm_num : 0 < (12:ℝ)) big
    linarith
  have es : e ≤ 1/4 := max_le (small _ hs) (small _ ht)
  have ep : 0 ≤ e := (by positivity : 0 ≤ 3*Real.exp (-π*τ^2)).trans (le_max_left ..)
  have sp : 0 < τ := by dsimp [τ]; linarith
  have tp : 0 < υ := by dsimp [υ]; linarith
  have op : 0 < 1-e := by linarith
  have vp : 0 < 1+e := by linarith
  have pf := scalar_normalizer_bounds c μ Q S e hQ hs (le_max_left ..) es
  have gf (i : ℤ) := scalar_normalizer_bounds (r i) (m i) M t e hM ht (le_max_right ..) es
  change Summable p ∧ (1-e)*τ ≤ ∑' i, p i ∧ (∑' i, p i) ≤ (1+e)*τ at pf
  have gf' (i : ℤ) : Summable (g i) ∧ (1-e)*υ ≤ ∑' j, g i j ∧ (∑' j, g i j) ≤ (1+e)*υ := gf i
  have pp (i : ℤ) : 0 ≤ p i := (Real.exp_pos _).le
  have wn (k : ℤ × ℤ) : 0 ≤ W k := mul_nonneg (pp k.1) (Real.exp_pos _).le
  have lo (i : ℤ) : ((1-e)*υ)*p i ≤ ∑' j, W (i,j) := by
    simp only [W,tsum_mul_left]
    exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (gf' i).2.1 (pp i))
  have hi (i : ℤ) : (∑' j, W (i,j)) ≤ ((1+e)*υ)*p i := by
    simp only [W,tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left (gf' i).2.2 (pp i)).trans_eq (mul_comm ..)
  have rs := Summable.of_nonneg_of_le (fun i => tsum_nonneg (fun j => wn (i,j))) hi (pf.1.mul_left _)
  have ws : Summable W := (summable_prod_of_nonneg wn).mpr
    ⟨fun i => (gf' i).1.mul_left (p i),rs⟩
  let Z := ∑' k, W k
  have zlo : ((1-e)*υ)*((1-e)*τ) ≤ Z := by
    exact (mul_le_mul_of_nonneg_left pf.2.1 (mul_pos op tp).le).trans
      (by rw [← tsum_mul_left,show Z=(∑' i, ∑' j, W (i,j)) from ws.tsum_prod]
          exact (pf.1.mul_left _).tsum_le_tsum lo rs)
  have zhi : Z ≤ ((1+e)*υ)*((1+e)*τ) := by
    exact (show Z ≤ ((1+e)*υ)*(∑' i, p i) by
      rw [← tsum_mul_left,show Z=(∑' i, ∑' j, W (i,j)) from ws.tsum_prod]
      exact rs.tsum_le_tsum hi (pf.1.mul_left _)).trans
      (mul_le_mul_of_nonneg_left pf.2.2 (mul_pos vp tp).le)
  have zpos : 0 < Z := (mul_pos (mul_pos op tp) (mul_pos op sp)).trans_le zlo
  change Summable W ∧ 0 < Z ∧ |τ*υ/Z-1| ≤ 6*e
  refine ⟨ws,zpos,?_⟩
  have eb : e^2 ≤ e := by nlinarith [mul_nonneg ep (show 0 ≤ 1-e by linarith)]
  have base : 0 < τ*υ := mul_pos sp tp
  have half : τ*υ ≤ 2*Z := by
    have q : 1/2 ≤ (1-e)^2 := by nlinarith [sq_nonneg e]
    nlinarith only [mul_le_mul_of_nonneg_right q base.le,zlo]
  have dif : |τ*υ-Z| ≤ 3*e*(τ*υ) := by
    rw [abs_le]
    constructor <;> nlinarith only [zlo,zhi,mul_le_mul_of_nonneg_right eb base.le,
      mul_nonneg (sq_nonneg e) base.le,mul_nonneg ep base.le]
  rw [show τ*υ/Z-1=(τ*υ-Z)/Z by field_simp,abs_div,abs_of_pos zpos,div_le_iff₀ zpos]
  exact dif.trans ((mul_le_mul_of_nonneg_left half (show 0 ≤ 3*e by positivity)).trans_eq (by ring))

/-- Quantitative two-point reduction from the original distribution on
    coefficient pairs satisfying all the prescribed roots. For every event
    the scalar comparison is a product of one-dimensional Gaussian weights
    on the two CRT progressions, including the conditional displacement. -/
theorem root_conditioned_joint_probability (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (r L : ℕ → ℤ) (a : ℤ) (s₀ s₁ c₀ c₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    let H := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) = a), (q:ℤ)
    let M := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) ≠ a), (q:ℤ)
    let C := {v : ℤ × ℤ // ∀ q ∈ Q, (v.1:ZMod q)+(r q : ZMod q)*v.2 = L q}
    let v := s₀^2+(a:ℝ)^2*s₁^2
    let S := Real.sqrt v
    let t := s₀*s₁/S
    let μ := c₀+(a:ℝ)*c₁
    let τ := S/(H:ℝ)
    let υ := t/(M:ℝ)
    let ε := 6*max (3*Real.exp (-π*τ^2)) (3*Real.exp (-π*υ^2))
    let G := fun z : C => coeffGaussian z.val.1 c₀ s₀ * coeffGaussian z.val.2 c₁ s₁
    2 ≤ τ → 2 ≤ υ → ∃ (c : ℤ) (d : ℤ → ℤ), ∀ (E : ℤ × ℤ → Prop) [DecidablePred E],
      let x := fun i : ℤ => c+H*i
      let y := fun i j : ℤ => d i+M*j
      let m := fun i : ℤ => c₁+(a:ℝ)*s₁^2/v*((x i:ℝ)-μ)
      let A := (∑' k : ℤ × ℤ, if E (x k.1-a*y k.1 k.2, y k.1 k.2) then
        coeffGaussian (x k.1) μ S * coeffGaussian (y k.1 k.2) (m k.1) t else 0)/(τ*υ)
      let P := (∑' z : C, if E z.val then G z else 0)/(∑' z : C, G z)
      |P-A| ≤ ε*A := by
  classical
  let H := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) = a), (q:ℤ)
  let M := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) ≠ a), (q:ℤ)
  let C := {v : ℤ × ℤ // ∀ q ∈ Q, (v.1:ZMod q)+(r q : ZMod q)*v.2 = L q}
  let v := s₀^2+(a:ℝ)^2*s₁^2
  let S := Real.sqrt v
  let t := s₀*s₁/S
  let μ := c₀+(a:ℝ)*c₁
  let τ := S/(H:ℝ)
  let υ := t/(M:ℝ)
  let ε := 6*max (3*Real.exp (-π*τ^2)) (3*Real.exp (-π*υ^2))
  let G := fun z : C => coeffGaussian z.val.1 c₀ s₀ * coeffGaussian z.val.2 c₁ s₁
  have Hpos : (0:ℤ) < H := Finset.prod_pos (fun q hq => by
    exact_mod_cast (hp q (Finset.mem_filter.mp hq).1).pos)
  have Mpos : (0:ℤ) < M := Finset.prod_pos (fun q hq => by
    exact_mod_cast (hp q (Finset.mem_filter.mp hq).1).pos)
  dsimp only
  intro hs ht
  obtain ⟨c,d,e,eq⟩ := polynomial_root_lattice Q hp r L a
  refine ⟨c,d,?_⟩
  let x := fun i : ℤ => c+H*i
  let y := fun i j : ℤ => d i+M*j
  let m := fun i : ℤ => c₁+(a:ℝ)*s₁^2/v*((x i:ℝ)-μ)
  let f := fun k : ℤ × ℤ => (x k.1-a*y k.1 k.2,y k.1 k.2)
  let W := fun k : ℤ × ℤ => coeffGaussian (x k.1) μ S*coeffGaussian (y k.1 k.2) (m k.1) t
  have eqe (k : ℤ × ℤ) : (e k).val=f k := eq k.1 k.2
  have prod (k : ℤ × ℤ) : G (e k)=W k := by
    dsimp only [G]
    rw [eqe]
    dsimp only [f,W]
    have h := conditional_gaussian_weight (↑(x k.1-a*y k.1 k.2 : ℤ)) (↑(y k.1 k.2)) c₀ c₁ a s₀ s₁ hs₀ hs₁
    dsimp only at h
    push_cast at h ⊢
    simpa only [sub_add_cancel,m,μ,t,S,v] using h
  have proof := gaussian_joint_normalizer c H S M t μ (fun i => (d i:ℝ)) m
    (by exact_mod_cast Hpos) (by exact_mod_cast Mpos) hs ht
  have hZ : 0 < ∑' k, W k ∧ |τ*υ/(∑' k, W k)-1| ≤ ε := by
    simpa only [W,x,y,Int.cast_add,Int.cast_mul,τ,υ,ε] using proof.2
  have den : (∑' z : C, G z) = ∑' k, W k := by
    rw [← e.tsum_eq G]
    exact tsum_congr prod
  intro E inst
  let N := ∑' k : ℤ × ℤ, if E (f k) then W k else 0
  have num : (∑' z : C, if E z.val then G z else 0) = N := by
    rw [← e.tsum_eq (fun z => if E z.val then G z else 0)]
    apply tsum_congr
    intro k
    simp only [eqe,prod]
  have np : 0 ≤ N := by
    apply tsum_nonneg
    intro k
    split
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · rfl
  have τpos : 0 < τ := by change 2 ≤ τ at hs; linarith
  have υpos : 0 < υ := by change 2 ≤ υ at ht; linarith
  change |(∑' z : C, if E z.val then G z else 0)/(∑' z : C, G z)-N/(τ*υ)| ≤ ε*(N/(τ*υ))
  rw [num,den,show N/(∑' k, W k)-N/(τ*υ)=N/(τ*υ)*(τ*υ/(∑' k, W k)-1) by
    field_simp [hZ.1.ne',τpos.ne',υpos.ne'],abs_mul,
    abs_of_nonneg (div_nonneg np (mul_pos τpos υpos).le)]
  exact (mul_le_mul_of_nonneg_left hZ.2 (div_nonneg np (mul_pos τpos υpos).le)).trans_eq (mul_comm ..)

end

end Cogentic.Window
