import Cogentic.Rank
import Cogentic.FixedSchedule
import Mathlib.Analysis.Complex.ExponentialBounds
import TwoThirdsRank

/-! Quantitative energy of the nominal two-field root grid at the fixed schedule. -/

namespace Cogentic
open scoped BigOperators
open Real

private theorem total_to_finset {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    TwoThirdsRank.total Finset.univ.toList f = ∑ i, f i := by
  have aux (xs : List ι) : TwoThirdsRank.total xs f = (xs.map f).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [TwoThirdsRank.total,ih]
  rw [aux,Finset.sum_map_toList]

private theorem jensen_square {ι : Type*} [Fintype ι] (p h : ι → ℝ)
    (nonneg : ∀ i, 0 ≤ p i) (norm : ∑ i, p i = 1) :
    (∑ i, p i*h i)^2 ≤ ∑ i, p i*(h i)^2 := by
  let μ := ∑ i, p i*h i
  have q : 0 ≤ ∑ i, p i*(h i-μ)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (nonneg i) (sq_nonneg _)
  have eq : ∑ i, p i*(h i-μ)^2 = ∑ i, p i*(h i)^2 - μ^2 := by
    calc
      _ = ∑ i, (p i*(h i)^2 - (p i*h i)*(2*μ) + p i*μ^2) := Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,norm,one_mul,show (∑ i, p i*h i) = μ by rfl]; ring
  rw [eq] at q
  exact sub_nonneg.mp q

private theorem fixed_root_grid_margin {b : ℕ} (big : 130000 ≤ Fixed.d b) :
    let d := Fixed.d b
    let z := Fixed.z b
    let H := (d:ℝ)*z
    let gap := (1:ℝ)/(4*d)
    let w := (Fixed.invWidth b:ℝ)⁻¹
    0 < w ∧ 2*w ≤ gap/2 ∧ gap ≤ 1/2 ∧
    2*H*log 2 ≤ log (1/4)-log (2*w) ∧ -log (gap/2) ≤ (z:ℝ)*log 2/2 ∧
    8*(2*d:ℝ)*(4*(2*d)+1) ≤ (2*H*log 2)^2-2*((z:ℝ)*log 2/2)^2*(2*d)^2 := by
  intro d z H gap w
  have dp : 130000 ≤ d := big
  have zp : 1 ≤ z := Nat.succ_pos _
  have cube : d^3 ≤ b := (Nat.le_mul_of_pos_right (d^3) zp).trans (Fixed.degree_floor b).1
  have lb : b < 2^z := Nat.lt_log2_self
  have zlarge : 32 ≤ z := by
    by_contra! small
    have up := Nat.pow_le_pow_right (by decide : 1≤2) (show z≤31 by omega)
    have dn := Nat.pow_le_pow_left dp 3
    norm_num at dn up
    omega
  have dr : 130000 ≤ (d:ℝ) := by exact_mod_cast dp
  have zr : 32 ≤ (z:ℝ) := by exact_mod_cast zlarge
  have dpos : 0 < (d:ℝ) := by linarith
  have lpos : (1/2:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have lup : log 2 ≤ 1 := by linarith [log_two_lt_d9]
  have logd : 3*log d ≤ (z:ℝ)*log 2 := by
    have le : (d:ℝ)^3 ≤ (2:ℝ)^z := by exact_mod_cast cube.trans lb.le
    simpa [log_pow] using Real.log_le_log (by positivity) le
  have wval : w = ((2:ℝ)^(3*(d*z)))⁻¹ := by simp [w,Fixed.invWidth,Fixed.h,d,z]
  have wp : 0<w := wval ▸ (by positivity)
  have gn : 0<gap := by dsimp [gap]; positivity
  have loff : -log (gap/2) = 3*log 2+log d := by
    rw [show gap/2 = ((2:ℝ)^3*d)⁻¹ by dsimp [gap]; field_simp; ring, log_inv,neg_neg,log_mul (by norm_num) dpos.ne',log_pow]
    norm_num
  have ldiag : log (1/4)-log (2*w) = (3*H-3)*log 2 := by
    rw [show (1/4:ℝ)=((2:ℝ)^2)⁻¹ by norm_num,log_inv,log_pow,log_mul (by norm_num) wp.ne',wval,log_inv,log_pow]
    push_cast
    dsimp [H]
    ring
  have off : -log (gap/2) ≤ (z:ℝ)*log 2/2 := by
    rw [loff]
    nlinarith [mul_le_mul_of_nonneg_right zr (by linarith : 0 ≤ log 2)]
  have diag : 2*H*log 2 ≤ log (1/4)-log (2*w) := by
    rw [ldiag]
    have three : 3 ≤ H := by dsimp [H]; nlinarith [mul_le_mul_of_nonneg_right dr (by positivity : 0 ≤ (z:ℝ))]
    nlinarith [mul_le_mul_of_nonneg_right three (by linarith : 0 ≤ log 2)]
  refine ⟨wp,?_,?_,diag,off,?_⟩
  · apply Real.log_le_log_iff (by positivity : 0<2*w) (by positivity : 0<gap/2) |>.mp
    rw [log_mul (by norm_num) wp.ne',wval,log_inv,log_pow]
    push_cast
    have dz : (z:ℝ) ≤ (d:ℝ)*z := by nlinarith [mul_le_mul_of_nonneg_right dr (by positivity : 0 ≤ (z:ℝ))]
    nlinarith [mul_le_mul_of_nonneg_right dz (by linarith : 0≤log 2),mul_le_mul_of_nonneg_right zr (by linarith : 0≤log 2)]
  · dsimp [gap]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  · have l2sq : (1/4:ℝ) ≤ (log 2)^2 := by nlinarith [sq_nonneg (log 2-1/2)]
    have zsq : 1024 ≤ (z:ℝ)^2 := by nlinarith [sq_nonneg ((z:ℝ)-32)]
    have a : (1:ℝ) ≤ d := by linarith
    have bound : 256 ≤ (z:ℝ)^2*(log 2)^2 := by nlinarith [mul_le_mul_of_nonneg_left l2sq (sq_nonneg (z:ℝ))]
    dsimp [H]
    nlinarith [mul_le_mul_of_nonneg_right bound (sq_nonneg (d:ℝ)),mul_le_mul_of_nonneg_right a dpos.le]

/-- Pinned root centers in increasing order, interleaving the two fields. -/
noncomputable def nominalCenter (d : ℕ) (i : Fin (2*d)) : ℝ := (i.val+1)/(4*(d:ℝ))

/-- For arbitrary normalized, nonnegative empirical measures in the actual
fixed-width intervals, the affine score has uniformly positive mean square.
Summing over intervals costs a single factor of their count if equal interval
weights are used. -/
theorem fixed_nominal_grid_energy {b : ℕ} (big : 130000 ≤ Fixed.d b) :
    let d := Fixed.d b
    let w := (Fixed.invWidth b:ℝ)⁻¹
    ∀ {β : Option (Fin (2*d)) → Type*} [∀ k, Fintype (β k)]
      (point mass : (k : Option (Fin (2*d))) → β k → ℝ),
      (∀ a, 3/4 ≤ point none a ∧ point none a ≤ 1) →
      (∀ i a, nominalCenter d i+w ≤ point (some i) a ∧ point (some i) a ≤ nominalCenter d i+2*w) →
      (∀ k a, 0 ≤ mass k a) → (∀ k, ∑ a, mass k a = 1) →
    ∀ (v₀ : ℝ) (v : Fin (2*d) → ℝ),
      let score := fun k a => v₀ + ∑ j, Real.log |point k a-nominalCenter d j| * v j
      v₀^2 + ∑ j, (v j)^2 ≤ 3*((∑ a, mass none a*(score none a)^2) +
        ∑ i, ∑ a, mass (some i) a*(score (some i) a)^2) := by
  classical
  intro d w β _ point mass base localMark positive norm v₀ v score
  let root := nominalCenter d
  let gap := (1:ℝ)/(4*d)
  let H := (d:ℝ)*Fixed.z b
  let M := fun k j => ∑ a, mass k a*log |point k a-root j|
  let μ := fun k => ∑ a, mass k a*score k a
  have dp : 0 < d := by change 0 < Fixed.d b; omega
  have dr : 0 < (d:ℝ) := by exact_mod_cast dp
  have denom : 0 < 4*(d:ℝ) := by positivity
  have rootBound (i : Fin (2*d)) : 0 ≤ root i ∧ root i ≤ 1/2 := by
    change 0 ≤ _/(4*(d:ℝ)) ∧ _/(4*(d:ℝ)) ≤ 1/2
    refine ⟨by positivity,(div_le_iff₀ denom).mpr ?_⟩
    have hv : i.val+1 ≤ 2*d := i.isLt
    have hr : (i.val:ℝ)+1 ≤ 2*(d:ℝ) := by exact_mod_cast hv
    linarith
  have sep (i j : Fin (2*d)) (ne : i≠j) : gap ≤ |root i-root j| := by
    change 1/(4*(d:ℝ)) ≤ |((i.val:ℝ)+1)/(4*d)-((j.val:ℝ)+1)/(4*d)|
    rw [← sub_div,abs_div,abs_of_pos denom]
    apply (div_le_div_iff_of_pos_right denom).mpr
    have n : i.val≠j.val := fun h => ne (Fin.ext h)
    rcases lt_or_gt_of_ne n with h|h
    · have nh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
      exact (show 1 ≤ -(((i.val:ℝ)+1)-((j.val:ℝ)+1)) by linarith).trans (neg_le_abs _)
    · have nh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
      exact (show 1 ≤ ((i.val:ℝ)+1)-((j.val:ℝ)+1) by linarith).trans (le_abs_self _)
  obtain ⟨wp,narrow,gsize,diagonal,off,margin⟩ := fixed_root_grid_margin big
  obtain ⟨diagEntries,offEntries⟩ := root_grid_log_entries root point mass w gap wp narrow gsize
    rootBound sep base localMark positive norm
  have meanScore (k) : μ k = v₀+∑ j, M k j*v j := by
    change ∑ a, mass k a*(v₀ + ∑ j, log |point k a-root j| * v j) = _
    simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,norm,one_mul]
    congr 1
    simp only [M,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
  have bsz (j : Fin (2*d)) : (M none j)^2 ≤ 4 := by
    have L (a : β none) : -2 ≤ log |point none a - root j| ∧ log |point none a-root j| ≤ 0 := by
      obtain ⟨xl,xu⟩ := base a
      obtain ⟨rl,ru⟩ := rootBound j
      have pos : 1/4 ≤ point none a - root j := by linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ point none a-root j)]
      have lg := Real.log_le_log (by norm_num : (0:ℝ)<1/4) pos
      rw [show (1/4:ℝ)=((2:ℝ)^2)⁻¹ by norm_num,log_inv,log_pow] at lg
      norm_num at lg
      exact ⟨by linarith [log_two_lt_d9],Real.log_nonpos (by linarith) (by linarith)⟩
    have low : ∑ a, mass none a * (-2) ≤ M none j :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (L a).1 (positive none a))
    have up : M none j ≤ 0 := Finset.sum_nonpos (fun a _ => mul_nonpos_of_nonneg_of_nonpos (positive none a) (L a).2)
    rw [←Finset.sum_mul,norm,one_mul] at low
    nlinarith [mul_nonneg (by linarith : 0≤M none j+2) (by linarith : 0≤2-M none j)]
  have totalBase : ∑ j, (M none j)^2 ≤ 4*(2*d:ℝ) := by
    simpa [mul_comm] using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => bsz j)
  let diff := fun i j => M (some i) j-M none j
  let err := fun i j => if j=i then 0 else diff i j
  let diag := fun i => diff i i
  let idx := (Finset.univ : Finset (Fin (2*d))).toList
  have cnt : TwoThirdsRank.countR (R:=ℝ) idx=2*d := by simp [TwoThirdsRank.countR,idx,total_to_finset]
  have positiveD : 0 ≤ 2*H*log 2 := by dsimp [H]; positivity
  have positiveB : 0 ≤ (Fixed.z b:ℝ)*log 2/2 := by positivity
  have squaredD : ∀ i∈idx, (2*H*log 2)^2 ≤ (diag i)^2 := by
    intro i _
    have ub : 2*H*log 2 ≤ -diag i := by
      change 2*H*log 2 ≤ -(M (some i) i-M none i)
      simpa only [neg_sub] using diagonal.trans (diagEntries i)
    nlinarith [sq_le_sq' (by linarith : -(-diag i) ≤ 2*H*log 2) ub]
  have squaredE : ∀ i∈idx, ∀ j∈idx, (err i j)^2 ≤ ((Fixed.z b:ℝ)*log 2/2)^2 := by
    intro i _ j _
    by_cases h : j=i
    · simpa [err,h] using sq_nonneg ((Fixed.z b:ℝ)*log 2/2)
    · have v' := (offEntries i j (Ne.symm h)).trans off
      change |M none j-M (some i) j| ≤ _ at v'
      rw [abs_sub_comm] at v'
      simpa [err,h,diff,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) v' 2
  have eq (i) : μ (some i)-μ none=diag i*v i+TwoThirdsRank.dot idx (err i) v := by
    rw [meanScore,meanScore,TwoThirdsRank.dot,total_to_finset]
    rw [show v₀ + (∑ j, M (some i) j*v j)-(v₀+∑ j, M none j*v j) =
      ∑ j, diff i j*v j by simp [diff,sub_mul,Finset.sum_sub_distrib]]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    calc
      ∑ j ∈ Finset.univ.erase i, diff i j * v j = ∑ j ∈ Finset.univ.erase i, err i j*v j :=
        Finset.sum_congr rfl (fun j hj => by simp [err,(Finset.mem_erase.mp hj).1])
      _ = ∑ j, err i j*v j := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; simp [err]
  have energy := TwoThirdsRank.affine_grid idx v (M none) diag (fun i => μ (some i)) err v₀ (μ none)
    ((2*H*log 2)^2) (((Fixed.z b:ℝ)*log 2/2)^2)
    (by simpa only [TwoThirdsRank.dot,idx,total_to_finset] using meanScore none)
    squaredD squaredE (fun i _ => eq i) (by
      rw [cnt]
      have : 1 ≤ (d:ℝ) := by exact_mod_cast dp
      linarith)
    (by rw [cnt,TwoThirdsRank.energy,total_to_finset]; exact
      (mul_le_mul_of_nonneg_left (add_le_add totalBase (le_refl (1:ℝ))) (by positivity : 0≤8*(2*(d:ℝ)))).trans margin)
  simp only [TwoThirdsRank.energy,idx,total_to_finset] at energy
  have jensen (k) := jensen_square (mass k) (score k) (positive k) (norm k)
  exact energy.trans (mul_le_mul_of_nonneg_left (add_le_add (jensen none)
    (Finset.sum_le_sum fun i _ => jensen (some i))) (by norm_num))

end Cogentic

#print axioms Cogentic.fixed_nominal_grid_energy
