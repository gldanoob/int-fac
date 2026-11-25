import Cogentic.PolynomialProbability
import Mathlib.Analysis.Normed.Ring.InfiniteSum
namespace Cogentic.Construction
open Real Cogentic.Window
noncomputable section

/-- The signed integer coefficient pair lies in the deterministic nonnegative
    enumeration rectangle. -/
def inCoefficientBox (n : ℕ) (k : ℤ×ℤ) : Prop :=
  let b := n.log2+1
  0≤k.1 ∧ k.1≤2*(b:ℤ)^2*Fixed.U b*Fixed.A b ∧ 0≤k.2 ∧ k.2≤2*(b:ℤ)^2*Fixed.U b

instance (n : ℕ) (k : ℤ×ℤ) : Decidable (inCoefficientBox n k) := by unfold inCoefficientBox; infer_instance

private theorem gaussian_interval (b σ : ℕ) (sb : 2≤σ) :
    let μ := (b:ℝ)^2*σ
    let G := fun j : ℤ => coeffGaussian j μ σ
    let cut := fun j : ℤ => if (j:ℝ)<0 ∨ 2*μ<(j:ℝ) then G j else 0
    Summable G ∧ Summable cut ∧ (∑' j,G j)≤4*σ ∧
      (∑' j,cut j)≤8*(σ:ℝ)*exp (-π*((b:ℝ)^2)^2/2) := by
  let μ := (b:ℝ)^2*σ; let G := fun j : ℤ => coeffGaussian j μ σ
  let cut := fun j : ℤ => if (j:ℝ)<0 ∨ 2*μ<(j:ℝ) then G j else 0
  have sp : 0<(σ:ℝ) := by exact_mod_cast (by omega : 0<σ)
  have hτ : 1≤(σ:ℝ) := by exact_mod_cast (by omega : 1≤σ)
  have pos : 0<∑' j, G j := by
    have h := (conditional_progression_probability 0 1 μ σ zero_lt_one (by simpa using (show 2≤(σ:ℝ) by exact_mod_cast sb)) (fun _ => True)).1
    simpa only [zero_add,one_mul,G] using h
  have ss : Summable G := by by_contra h; exact pos.ne' (tsum_eq_zero_of_not_summable h)
  have normal := shifted_gaussian_normalizer μ σ hτ
  have expOne : exp (-π*(σ:ℝ)^2)≤1 := exp_le_one_iff.mpr (by nlinarith [mul_nonneg pi_pos.le (sq_nonneg (σ:ℝ))])
  have upper : (∑' j,G j)≤4*(σ:ℝ) := by
    have h := (abs_le.mp normal).2
    apply (div_le_iff₀ sp).mp
    change (∑' j : ℤ, coeffGaussian j μ σ)/(σ:ℝ)≤_
    linarith only [h,expOne]
  let T := fun j : ℤ => if (b:ℝ)^2*σ ≤ |(j:ℝ)-μ| then G j else 0
  have gn (j : ℤ) : 0≤G j := (exp_pos _).le
  have st : Summable T := Summable.of_nonneg_of_le (fun j => by dsimp [T]; split <;> first | exact gn j | rfl)
    (fun j => by dsimp [T]; split <;> first | exact gn j | rfl) ss
  have sc : Summable cut := Summable.of_nonneg_of_le (fun j => by dsimp [cut]; split <;> first | exact gn j | rfl)
    (fun j => by dsimp [cut]; split <;> first | exact gn j | rfl) ss
  have le (j : ℤ) : cut j ≤ T j := by
    dsimp [cut,T]
    split
    next bad =>
      rw [if_pos]
      rcases bad with neg|big
      · have a := neg_abs_le ((j:ℝ)-μ); dsimp [μ] at *; linarith
      · have a := le_abs_self ((j:ℝ)-μ); dsimp [μ] at *; linarith
    next => split <;> first | exact gn j | rfl
  exact ⟨ss,sc,upper,(sc.tsum_le_tsum le st).trans (lattice_gaussian_tail μ σ ((b:ℝ)^2) hτ (sq_nonneg _))⟩

/-- The unconditioned total Gaussian weight assigned outside the original
    rectangle, with both discrete coordinates and the original scaling. -/
theorem coefficient_outside_weight (n : ℕ) :
    let b := n.log2+1; let U : ℝ := Fixed.U b; let A : ℝ := Fixed.A b
    let bad := fun k : ℤ×ℤ => if ¬inCoefficientBox n k then coefficientWeight n k else 0
    Summable bad ∧ (∑' k, bad k)≤64*(U*A*U)*exp (-π*((b:ℝ)^2)^2/2) := by
  let b := n.log2+1; let U := Fixed.U b; let A := Fixed.A b
  let σ := U*A
  let g := fun j : ℤ => coeffGaussian j ((b:ℝ)^2*σ) σ
  let h := fun j : ℤ => coeffGaussian j ((b:ℝ)^2*U) U
  let cut := fun (q : ℕ) (j : ℤ) => (j:ℝ)<0 ∨ 2*((b:ℝ)^2*q)<(j:ℝ)
  let f := fun j : ℤ => if cut σ j then g j else 0
  let t := fun j : ℤ => if cut U j then h j else 0
  let V := fun k : ℤ×ℤ => f k.1*h k.2+g k.1*t k.2
  let bad := fun k : ℤ×ℤ => if ¬inCoefficientBox n k then coefficientWeight n k else 0
  have dp := Fixed.degree_pos (b := b) (Nat.succ_pos _)
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have up : 2≤U := Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) (show 1≤100000*Fixed.v b by omega)
  have ap : 0<A := Nat.pow_pos (by decide)
  have ⟨gs,fs,gu,fu⟩ := gaussian_interval b σ (up.trans (Nat.le_mul_of_pos_right _ ap))
  have ⟨hs,ts,hu,tu⟩ := gaussian_interval b U up
  have gn (j : ℤ) : 0≤g j := (exp_pos _).le
  have hn (j : ℤ) : 0≤h j := (exp_pos _).le
  have fnn (j : ℤ) : 0≤f j := by dsimp [f]; split <;> first | exact gn j | rfl
  have tn (j : ℤ) : 0≤t j := by dsimp [t]; split <;> first | exact hn j | rfl
  have as := fs.mul_of_nonneg hs fnn hn
  have bs := gs.mul_of_nonneg ts gn tn
  have vs : Summable V := as.add bs
  have weight (k : ℤ×ℤ) : coefficientWeight n k=g k.1*h k.2 := by simp only [g,h,σ,coefficientWeight,b,U,A,Nat.cast_mul,mul_assoc]
  have dn (k : ℤ×ℤ) : 0≤bad k := by dsimp only [bad]; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
  have le (k : ℤ×ℤ) : bad k ≤ V k := by
    dsimp only [bad,V,f,t]
    rw [weight]
    by_cases i : cut σ k.1
    · rw [if_pos i]; split <;> split <;> nlinarith [mul_nonneg (gn k.1) (hn k.2)]
    · rw [if_neg i,zero_mul,zero_add]
      split
      next outside =>
        rw [if_pos]
        by_contra! no
        apply outside
        dsimp only [cut] at i no
        push_neg at i no
        change 0≤k.1 ∧ k.1≤2*(b:ℤ)^2*U*A ∧ 0≤k.2 ∧ k.2≤2*(b:ℤ)^2*U
        exact ⟨by exact_mod_cast i.1,by have bound := i.2; dsimp only [σ] at bound; push_cast at bound; exact_mod_cast (by linarith only [bound] : (k.1:ℝ)≤2*(b:ℝ)^2*U*A),
          by exact_mod_cast no.1,by exact_mod_cast (by linarith only [no.2] : (k.2:ℝ)≤2*(b:ℝ)^2*U)⟩
      next => split <;> nlinarith [mul_nonneg (gn k.1) (hn k.2)]
  have ds := Summable.of_nonneg_of_le dn le vs
  have sum : (∑' k,V k)=(∑' i,f i)*(∑' j,h j)+(∑' i,g i)*(∑' j,t j) := by
    exact (as.tsum_add bs).trans (congrArg₂ (·+·) (fs.tsum_mul_tsum hs as).symm
      (gs.tsum_mul_tsum ts bs).symm)
  have e₀ : 0≤8*(σ:ℝ)*exp (-π*((b:ℝ)^2)^2/2) := by positivity
  have ub₁ := mul_le_mul fu hu (tsum_nonneg hn) e₀
  have ub₂ := mul_le_mul gu tu (tsum_nonneg tn) (by positivity)
  refine ⟨ds,(ds.tsum_le_tsum le vs).trans ?_⟩
  rw [sum]
  change (∑' i,f i)*(∑' j,h j)+(∑' i,g i)*(∑' j,t j)≤_
  calc _ ≤ (8*σ*exp (-π*((b:ℝ)^2)^2/2))*(4*U)+(4*σ)*(8*U*exp (-π*((b:ℝ)^2)^2/2)) := add_le_add ub₁ ub₂
       _ = _ := by
         change _ = 64*((U:ℝ)*A*U)*exp (-π*((b:ℝ)^2)^2/2)
         simp only [σ,Nat.cast_mul]
         ring

end
end Cogentic.Construction

#print axioms Cogentic.Construction.coefficient_outside_weight
