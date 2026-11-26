import Cogentic.OrdinaryMass
import Cogentic.DividedMarkTilts

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The common-scale error in the ordinary finite block costs at most one
sixteenth of its energy, simultaneously on all integer mesh branches of one protected draw.
Deleting additional rows restricts the same bound to their coordinate subspace. -/
theorem protected_ordinary_pair_remainder (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let J := primeBand b; let H := log (Fixed.B b)
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ a₀∈(construct n ell 0 0 0 0).marks, ∀ (side₀ : Bool) (β : ℝ), 0≤β →
    saddleMean J β=dividedLogCenter n ell a₀ side₀ →
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ (cost : Ω→ℝ) (budget : ℝ), (∀ k,0 ≤ cost k) →
    HasSum (fun k=>twoFieldWeight O O k*cost k) budget → budget≤1/2 →
    ∃ k : Ω, retainedDenominatorGood n ell mix k.1.val k.2.val ∧
      protectedDrawRank n ell k.1.val k.2.val ∧ cost k<1 ∧
      let S := admittedOrdinaryRows n ell k.1.val k.2.val
      let p := fun i : ↥S=>bandRowPrime i.val
      let w := fun i : ↥S=>sqrt ((p i:ℝ)^(-β))
      ∀ α : Bool→ℝ, (∀ s,199/200≤α s) →
      (∀ s,InMarkSaddleRange n (saddleMean J (α s))) →
      let I := fun (s : Bool) (Q : ℕ)=>fullBandInsertion b Q (α s)/((Q:ℝ)*(Q:ℝ)^(-β))
      let V := fun s=>saddleVariance J (primeProbability (α s)) (fun q=>log q)
      let E := fun (i j : ↥S)=>if i.val.1=j.val.1 ∧ p i≠p j then
        let s := i.val.1
        w i*w j*(I s (p i*p j)-I s (p i)*I s (p j)*(1-log (p i)*log (p j)/V s)) else 0
      ∀ v : ↥S→ℝ, 16*|∑ i,∑ j,v i*E i j*v j|≤∑ i,(v i)^2 := by
  obtain ⟨C,cp,b₀,pairs⟩ := grid_scale_insertions
  obtain ⟨b₁,degree⟩ := Fixed.degree_grows (max 10004 ⌈32*C⌉₊)
  obtain ⟨n₁,draw⟩ := protected_rank_ordinary_mass line
  refine ⟨max n₁ (max 2 (2^(max b₀ b₁))),?_⟩
  intro n large ell target comp absent b J H O Ω a₀ ref side₀ β bp refEq mix nonneg norm cost budget cn ce bound
  obtain ⟨old,other⟩ := max_le_iff.mp large
  obtain ⟨hn,lg⟩ := max_le_iff.mp other
  have ⟨b0,b1⟩ := max_le_iff.mp (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  have big := degree b b1
  have hd : 10004≤Fixed.d b := (le_max_left ..).trans big
  have cLim : 32*C≤(Fixed.d b:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right ..).trans big)
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _)))
    (by decide) : 1<Fixed.B b))
  let u := dividedLogCenter n ell a₀ side₀/H
  let u₀ := 90*(Fixed.d b:ℝ)
  have dr : (10004:ℝ)≤Fixed.d b := by exact_mod_cast hd
  have u0p : 0<u₀ := by dsimp [u₀];linarith only [dr]
  have uc := divided_center_range hn hd target ref side₀
  have up : 0<u := div_pos (lt_of_lt_of_le (mul_pos hp u0p) uc.1) hp
  have upper : u≤110*(Fixed.d b:ℝ) := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using uc.2.1)
  have sampleEq : saddleMean J β=H*u := by rw [refEq]; dsimp only [u]; field_simp
  obtain ⟨k,den,rank,tests,small⟩ := draw n old ell target comp absent β u bp up sampleEq mix nonneg norm cost budget cn ce bound
  refine ⟨k,den,rank,tests,?_⟩
  intro S p w α ae law I V E v
  have mass : (∑ i : ↥S, (w i)^2)≤128*u := by
    simp only [w,Real.sq_sqrt (rpow_nonneg (Nat.cast_nonneg _) _)]
    rw [sum_coe_sort S (fun j=>(bandRowPrime j:ℝ)^(-β))]
    exact small.le
  let ρ := C/u₀^2
  have nn : 0≤ρ := div_nonneg cp.le (sq_nonneg _)
  have entries (i j : ↥S) : |E i j|≤ρ*w i*w j := by
    have wi : 0≤w i := sqrt_nonneg _; have wj : 0≤w j := sqrt_nonneg _
    by_cases mask : i.val.1=j.val.1 ∧ p i≠p j
    · dsimp only [E]; rw [if_pos mask]
      change |w i*w j*(I i.val.1 (p i*p j)-I i.val.1 (p i)*I i.val.1 (p j)*(1-log (p i)*log (p j)/V i.val.1))|≤_
      rw [abs_mul,abs_mul,abs_of_nonneg wi,abs_of_nonneg wj]
      have localLaw := pairs b0 (α i.val.1) β (ae _) bp (law _) (refEq ▸ uc)
        (p i) i.val.2.1.property (p j) j.val.2.1.property
      calc _ ≤ (w i*w j)*ρ := mul_le_mul_of_nonneg_left localLaw.2 (mul_nonneg wi wj)
           _ = _ := by ring
    · simp only [E,mask,if_false,abs_zero]
      exact mul_nonneg (mul_nonneg nn wi) wj
  have err := covariance_remainder E v w ρ nn entries
  have lim : 16*ρ*(128*u)≤1 := by
    have ub := mul_le_mul_of_nonneg_left upper (mul_nonneg (by norm_num : (0:ℝ)≤2048) cp.le)
    have refB := mul_le_mul_of_nonneg_right cLim (Nat.cast_nonneg (α:=ℝ) (Fixed.d b))
    dsimp only [ρ]
    rw [show 16*(C/u₀^2)*(128*u)=2048*C*u/u₀^2 by ring,div_le_one (sq_pos_of_pos u0p)]
    dsimp only [u₀]; nlinarith only [ub,refB,sq_nonneg (Fixed.d b:ℝ)]
  have scale := (mul_le_mul_of_nonneg_left mass (mul_nonneg (by norm_num : (0:ℝ)≤16) nn)).trans lim
  calc
    16*|∑ i,∑ j,v i*E i j*v j| ≤ 16*(ρ*(∑ i,(w i)^2)*∑ i,(v i)^2) := by linarith only [err]
    _ = (16*ρ*(∑ i,(w i)^2))*(∑ i,(v i)^2) := by ring
    _ ≤ 1*(∑ i,(v i)^2) := mul_le_mul_of_nonneg_right scale (sum_nonneg (fun _ _=>sq_nonneg _))
    _ = _ := one_mul _

end
end Cogentic.Construction

#print axioms Cogentic.Construction.protected_ordinary_pair_remainder
