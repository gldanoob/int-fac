import Cogentic.DividedMarkTilts
import Cogentic.RawGramTransfer
import Cogentic.TargetBranchEnergy

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- The ordinary entries of the target-miss reference bound the mass of marks
meeting a deleted row. The estimates hold before and after restricting the row list. -/
theorem miss_grid_ordinary_upper :
    ∃ b₀ : ℕ, ∀ {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ (α : GridPosition b→Bool→ℝ) (β τ : ℝ), 0≤β → 0≤τ → τ≤1 →
    (∀ z k, 199/200≤α z k) → InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ z k, InMarkSaddleRange n (saddleMean (primeBand b) (α z k))) →
    ∀ {ι : Type*} [DecidableEq ι] (p : ι→ℕ) (side : ι→Bool), (∀ i,p i∈primeBand b) →
    let w := fun i=>sqrt ((p i:ℝ)^(-β))
    let I := fun z k (q : ℕ)=>fullBandInsertion b q (α z k)/((q:ℝ)*(q:ℝ)^(-β))
    let m := fun z i=>w i*I z (side i) (p i)
    let R := fun z=>ordinaryRawEntry p side w (I z)
    let G := missGridGram τ m R
    (∀ i,G (.inr i) (.inr i)≤5) ∧ ∀ i j,i≠j → G (.inr i) (.inr j)≤5*w i*w j := by
  classical
  obtain ⟨C,cp,b₁,atoms⟩ := grid_scale_insertions
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows (max 2 ⌈C⌉₊)
  refine ⟨max b₁ b₂,?_⟩
  intro n b big α β τ bp tp t1 aa mb ma ι _ p side pm w I m R G
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have deg := degree b two
  let u := 90*(Fixed.d b:ℝ)
  have dr : (2:ℝ)≤Fixed.d b := by exact_mod_cast (le_max_left ..).trans deg
  have large : 88≤u := by dsimp only [u]; linarith only [dr]
  have up : 0<u := by linarith only [large]
  have cd : C≤(Fixed.d b:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right ..).trans deg)
  have c1 : C/u^2≤1 := (div_le_one (sq_pos_of_pos up)).mpr (by
    have cu : C≤u := by dsimp only [u]; linarith only [cd,dr]
    nlinarith only [cu,mul_nonneg up.le (show 0≤u-1 by linarith only [large])])
  have single (z k i) : 0≤I z k (p i) ∧ I z k (p i)≤2 := by
    have t := (atoms one (α z k) β (aa z k) bp (ma z k) mb (p i) (pm i) (p i) (pm i)).1
    change |I z k (p i)-1|≤88/u at t
    exact ⟨by linarith only [(abs_le.mp t).1,(div_le_one up).mpr large],
      by linarith only [(abs_le.mp t).2,(div_le_one up).mpr large]⟩
  have double (z k i j) : I z k (p i*p j)≤5 := by
    let V := saddleVariance (primeBand b) (primeProbability (α z k)) (fun q=>log q)
    have h := (atoms one (α z k) β (aa z k) bp (ma z k) mb (p i) (pm i) (p j) (pm j)).2
    change |I z k (p i*p j)-I z k (p i)*I z k (p j)*(1-log (p i)*log (p j)/V)|≤C/u^2 at h
    have vp : 0<V := (grid_variance_floor (by linarith only [aa z k] : 0≤α z k) (ma z k)).2
    have lp (t : ι) : 0≤log (p t) := log_nonneg (by exact_mod_cast (mem_primeBand.mp (pm t)).1.one_le)
    have corr := div_nonneg (mul_nonneg (lp i) (lp j)) vp.le
    have pi := single z k i
    have pj := single z k j
    have bound := mul_le_mul pi.2 pj.2 pj.1 (by norm_num : (0:ℝ)≤2)
    have small := mul_le_mul_of_nonneg_left (sub_le_self 1 corr) (mul_nonneg pi.1 pj.1)
    linarith only [(abs_le.mp h).2,c1,small,bound]
  let a : ℝ := (cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)
  have an : 0≤a := by dsimp only [a]; positivity
  have normalize : (∑ _ : GridPosition b,a)=1 := by
    have mc : (0:ℝ)<cellMarkCount b := Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0<2))
    have den : 0<2*(Fixed.d b:ℝ)+1 := by positivity
    simp only [GridPosition,sum_const,card_univ,Fintype.card_prod,Fintype.card_option,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,a]
    field_simp
  have averaged (i j : ι) (B : ℝ) (bn : 0≤B) (point : ∀ z,R z i j≤B) :
      G (.inr i) (.inr j)≤B := by
    change τ*(∑ z : GridPosition b,a*R z i j)≤B
    have s := sum_le_sum (s:=univ) (fun z _=>mul_le_mul_of_nonneg_left (point z) an)
    rw [←sum_mul,normalize,one_mul] at s
    exact (mul_le_mul_of_nonneg_left s tp).trans ((mul_le_mul_of_nonneg_right t1 bn).trans_eq (one_mul B))
  constructor
  · intro i
    apply averaged i i _ (by norm_num)
    intro z
    simpa only [R,ordinaryRawEntry,ite_true,eq_self] using (single z (side i) i).2.trans (by norm_num : (2:ℝ)≤5)
  · intro i j ne
    have wi : 0≤w i := sqrt_nonneg _
    have wj : 0≤w j := sqrt_nonneg _
    apply averaged i j _ (by positivity)
    intro z
    dsimp only [R,ordinaryRawEntry]
    by_cases pq : p i=p j
    · simp only [if_pos pq,if_neg ne]; positivity
    · rw [if_neg pq]
      by_cases ss : side i=side j
      · rw [if_pos ss]
        exact (mul_le_mul_of_nonneg_left (double z (side i) i j) (mul_nonneg wi wj)).trans_eq (by ring)
      · rw [if_neg ss]
        have h := mul_le_mul (single z (side i) i).2 (single z (side j) j).2
          (single z (side j) j).1 (by norm_num : (0:ℝ)≤2)
        have est := mul_le_mul_of_nonneg_left (h.trans (by norm_num : (2:ℝ)*2≤5)) (mul_nonneg wi wj)
        linarith only [est]

end
end Cogentic.Construction
#print axioms Cogentic.Construction.miss_grid_ordinary_upper
