import Cogentic.DistinctPrimeGram
import Cogentic.MarkSeparation

namespace Cogentic.Construction
open Finset Real
noncomputable section

/-- Each nominal log coordinate has total variation at most one across the
integer mesh of any cell, including the cell next to its own root. A step is
`1 / A` and the distance to that root throughout the cell is at least
`1 / invWidth`. -/
theorem raw_log_profile_bounds {n : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) :
    let b := n.log2+1; let M := cellMarkCount b
    let D := 3*(Fixed.h b:ℝ)
    let f := fun (side : Bool) (i : Fin (Fixed.d b)) (a : ℕ)=>
      log |(a:ℝ)/Fixed.A b-(center (Fixed.d b) side i.val:ℝ)|
    ∀ cell : Option (Bool×Fin (Fixed.d b)), let L := firstCellMark b cell
    (∀ side i, (∀ j<M,|f side i (L+j)|≤D) ∧
      (∑ j∈range (M-1),|f side i (L+(j+1))-f side i (L+j)|)≤1 ∧
      meshVariation L M (f side i)≤D+1) ∧
    ∀ s i t k, (∀ j<M,|f s i (L+j)*f t k (L+j)|≤D^2) ∧
      meshVariation L M (fun a=>f s i a*f t k a)≤D^2+2*D := by
  intro b M D f cell L
  let A : ℝ := Fixed.A b;let W : ℝ := Fixed.invWidth b
  have Ap : 0<A := by dsimp [A,Fixed.A];positivity
  have Wp : 0<W := by dsimp [W,Fixed.invWidth];positivity
  have Mp : 0<M := Nat.pow_pos (by decide)
  have Mr : (0:ℝ)<M := by exact_mod_cast Mp
  have dp : 1≤Fixed.d b := (by decide : 1≤10004).trans big
  have Dp : 0≤D := by dsimp only [D];positivity
  have scale : (M:ℝ)*W=A := by dsimp only [M,W,A];exact_mod_cast cell_scale b
  have invstep : A⁻¹/W⁻¹=(M:ℝ)⁻¹ := by rw [←scale];field_simp
  have lg : log W≤D := by
    dsimp only [W,Fixed.invWidth,D];rw [Nat.cast_pow,Nat.cast_ofNat,log_pow]
    push_cast
    have bound : log 2≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg (α:=ℝ) (Fixed.h b))]
  have data (side : Bool) (i : Fin (Fixed.d b)) (j : ℕ) (jm : j<M) :
      W⁻¹≤ |((L+j:ℕ):ℝ)/A-(center (Fixed.d b) side i.val:ℝ)| ∧
      |((L+j:ℕ):ℝ)/A-(center (Fixed.d b) side i.val:ℝ)|≤1 := by
    have grid := fixed_grid_interval dp cell (L+j) (mem_Ico.mpr ⟨Nat.le_add_right ..,Nat.add_lt_add_left jm L⟩)
    have low := (Rat.cast_le (K:=ℝ)).mpr (grid_separation (Fixed.stage_guards hn big).roots.1 grid.2.2 side i)
    have min := (Rat.cast_le (K:=ℝ)).mpr (center_range i.isLt side).1
    have max := (Rat.cast_le (K:=ℝ)).mpr (center_range i.isLt side).2
    have pos : 0≤((L+j:ℕ):ℝ)/A := div_nonneg (Nat.cast_nonneg _) Ap.le
    have one : ((L+j:ℕ):ℝ)/A≤1 := (div_le_one Ap).mpr (by dsimp only [A];exact_mod_cast grid.2.1)
    push_cast at low min max
    refine ⟨by simpa only [W,A,Nat.cast_add] using low,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith
  have bound (side : Bool) (i : Fin (Fixed.d b)) (j : ℕ) (jm : j<M) : |f side i (L+j)|≤D := by
    have ⟨lo,hi⟩ := data side i j jm
    have wp := inv_pos.mpr Wp
    have l := log_le_log wp lo
    have h := log_nonpos (abs_nonneg _) hi
    rw [log_inv] at l
    exact abs_le.mpr ⟨by change -D≤log _;linarith only [l,lg],h.trans Dp⟩
  have step (side : Bool) (i : Fin (Fixed.d b)) (j : ℕ) (jm : j∈range (M-1)) :
      |f side i (L+(j+1))-f side i (L+j)|≤(M:ℝ)⁻¹ := by
    have len := mem_range.mp jm
    let d := fun k : ℕ=>((L+k:ℕ):ℝ)/A-(center (Fixed.d b) side i.val:ℝ)
    have h := RootLogs.log_lipschitz (inv_pos.mpr Wp) (data side i (j+1) (by omega)).1 (data side i j (by omega)).1
    have dx : d (j+1)-d j=A⁻¹ := by dsimp only [d];push_cast;ring
    have diffAbs : abs (|d (j+1)|-|d j|) ≤ A⁻¹ := by simpa only [dx,abs_of_nonneg (inv_nonneg.mpr Ap.le)] using abs_abs_sub_abs_le (d (j+1)) (d j)
    exact h.trans ((div_le_div_of_nonneg_right diffAbs (inv_nonneg.mpr Wp.le)).trans_eq invstep)
  have count : (((M-1:ℕ):ℝ)*(M:ℝ)⁻¹)≤1 := by
    rw [←div_eq_mul_inv,div_le_one Mr];exact_mod_cast Nat.sub_le M 1
  have variation (side : Bool) (i : Fin (Fixed.d b)) :
      (∑ j∈range (M-1),|f side i (L+(j+1))-f side i (L+j)|)≤1 := by
    have h := sum_le_sum (s:=range (M-1)) (step side i)
    simpa only [sum_const,card_range,nsmul_eq_mul] using h.trans (by simpa only [sum_const,card_range,nsmul_eq_mul] using count)
  refine ⟨fun side i=>⟨bound side i,variation side i,add_le_add (bound side i _ (by omega)) (variation side i)⟩,?_⟩
  intro s i t k
  have size (j : ℕ) (jm : j<M) : |f s i (L+j)*f t k (L+j)|≤D^2 := by
    rw [abs_mul,sq];exact mul_le_mul (bound s i j jm) (bound t k j jm) (abs_nonneg _) Dp
  refine ⟨size,?_⟩
  have product (j : ℕ) (jm : j∈range (M-1)) :
      |f s i (L+(j+1))*f t k (L+(j+1))-f s i (L+j)*f t k (L+j)| ≤
      D*|f s i (L+(j+1))-f s i (L+j)|+D*|f t k (L+(j+1))-f t k (L+j)| := by
    have len := mem_range.mp jm
    rw [show _-_=f t k (L+j)*(f s i (L+(j+1))-f s i (L+j))+
      f s i (L+(j+1))*(f t k (L+(j+1))-f t k (L+j)) by ring]
    exact (abs_add_le ..).trans (by simp only [abs_mul];exact
      add_le_add (mul_le_mul_of_nonneg_right (bound t k j (by omega)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (bound s i (j+1) (by omega)) (abs_nonneg _)))
  have diff := sum_le_sum (s:=range (M-1)) product
  rw [sum_add_distrib,←mul_sum,←mul_sum] at diff
  dsimp only [meshVariation]
  nlinarith only [size (M-1) (by omega),diff,mul_le_mul_of_nonneg_left (variation s i) Dp,mul_le_mul_of_nonneg_left (variation t k) Dp]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.raw_log_profile_bounds
