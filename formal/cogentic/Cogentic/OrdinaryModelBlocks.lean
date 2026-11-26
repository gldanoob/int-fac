import Cogentic.DividedMarkTilts
import Cogentic.SamePrimeBlocks

namespace Cogentic.Construction
open Finset Real Window
noncomputable section

/-- A single ordinary prime has small reference mass even after summing all
the roots of a degree-`d` polynomial at that prime. -/
theorem single_prime_row_mass {b p : ℕ} (bp : 0<b) (pm : p∈primeBand b) {β : ℝ} (ba : 1/2≤β) :
    (p:ℝ)^(-β)≤1/(65536*(Fixed.d b:ℝ)) := by
  let d := Fixed.d b
  have dp : 0<d := Fixed.degree_pos bp
  have h : d≤Fixed.h b := Nat.le_mul_of_pos_right d (Nat.succ_pos _)
  obtain ⟨pp,_,lower⟩ := mem_primeBand.mp pm
  have first : 65536*d≤2^(16+d) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_left _ (Nat.lt_two_pow_self.le)
  have cap := Nat.pow_le_pow_left first 2
  rw [←Nat.pow_mul] at cap
  have q : 2^((16+d)*2)≤p := by
    by_contra! np
    have low := (Nat.pow_le_pow_left np.le 2).trans (show (2^((16+d)*2))^2≤Fixed.B b by
      rw [←Nat.pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      change ((16+d)*2)*2 ≤ 1000*Fixed.h b
      omega)
    exact lower.not_ge low
  have rt : 65536*(d:ℝ)≤ sqrt (p:ℝ) := (le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr (by exact_mod_cast cap.trans q)
  have one : (1:ℝ)≤p := by exact_mod_cast pp.one_le
  calc (p:ℝ)^(-β) ≤ (p:ℝ)^(-(1/2):ℝ) := rpow_le_rpow_of_exponent_le one (by linarith only [ba])
       _ = (sqrt (p:ℝ))⁻¹ := by rw [rpow_neg (Nat.cast_nonneg _),sqrt_eq_rpow]
       _ ≤ _ := by rw [one_div];exact inv_anti₀ (by positivity) rt

/-- Compensation for every equal-prime pair, including diagonal entries.
The retained equal-prime matrix consists of the exact diagonal alone. The
operator cost of removing the model mean and curvature on these blocks is
less than one sixty-fourth of the ordinary-row energy. -/
theorem grid_same_prime_compensation :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → ell∈dyadicTargets (Fixed.beta b) → ∀ a c e f : ℕ,
    let s := TryPair.fixedInput n ell (construct n ell a c e f)
    ∀ A : Finset Marking.Row, A⊆s.rows.toFinset → (∀ i∈A,i.q∈primeBand b) →
    ∀ (α : Bool→ℝ) (β : ℝ), 1/2≤β → (∀ k, 199/200≤α k) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    (∀ k, InMarkSaddleRange n (saddleMean (primeBand b) (α k))) →
    let m := fun p : ℕ=>(p:ℝ)^(-β)
    let I := fun k p=>fullBandInsertion b p (α k)/((p:ℝ)*m p)
    let V := fun k=>saddleVariance (primeBand b) (primeProbability (α k)) (fun p=>log p)
    let E := fun i j : Marking.Row=>if i.q=j.q then
      m i.q*I i.second i.q*I j.second j.q*(if i.second=j.second then 1-(log i.q)^2/V i.second else 1) else 0
    (∀ i∈A, 63/64 ≤ I i.second i.q) ∧ ∀ v : Marking.Row→ℝ,
      64*|∑ i∈A,∑ j∈A,v i*E i j*v j| ≤ ∑ i∈A,(v i)^2 := by
  obtain ⟨_,_,b₁,atoms⟩ := grid_scale_insertions
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b big target a c e f s A sub rows α β ba αa mb ma m I V E
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have bigD := deg b two
  let d : ℝ := Fixed.d b; let u := 90*d; let H := log (Fixed.B b)
  have dr : (10004:ℝ)≤d := by dsimp only [d];exact_mod_cast bigD
  have dp : 0<d := by linarith only [dr]
  have up : 0<u := by dsimp [u]; positivity
  have drift (k : Bool) (p : ℕ) (pm : p∈primeBand b) : |I k p-1|≤1/64 := by
    have h := (atoms one (α k) β (αa k) (by linarith only [ba]) (ma k) mb p pm p pm).1
    apply h.trans
    change 88/u≤1/64
    rw [div_le_iff₀ up];dsimp [u];linarith only [dr]
  refine ⟨fun i hi=>by linarith only [(abs_le.mp (drift i.second i.q (rows i hi))).1],?_⟩
  let δ := 4/(65536*d)
  have maxI (k : Bool) (p : ℕ) (pm : p∈primeBand b) : |I k p|≤2 := by
    have h := abs_le.mp (drift k p pm)
    exact abs_le.mpr ⟨by linarith only [h.1],by linarith only [h.2]⟩
  have loss (k : Bool) (p : ℕ) (pm : p∈primeBand b) : |1-(log p)^2/V k|≤1 := by
    obtain ⟨floor,vp⟩ := grid_variance_floor (by linarith only [αa k] : 0≤α k) (ma k)
    change H^2*u≤4*V k at floor
    have cap := (mem_primeBand.mp pm).2.1
    have lt := log_le_log (by exact_mod_cast (mem_primeBand.mp pm).1.pos : 0<(p:ℝ)) (show (p:ℝ)≤Fixed.B b by exact_mod_cast cap)
    have lg := log_nonneg (by exact_mod_cast (mem_primeBand.mp pm).1.one_le : (1:ℝ)≤p)
    have hp : (log p)^2≤H^2 := sq_le_sq' (by change log p≤H at lt; linarith only [lt,lg]) lt
    have ge : 4≤u := by dsimp [u]; linarith only [dr]
    have F := mul_le_mul_of_nonneg_left ge (sq_nonneg H)
    have ratio : (log p)^2/V k≤1 := (div_le_one vp).mpr (by nlinarith only [hp,F,floor])
    exact abs_le.mpr ⟨by linarith only [ratio],by linarith only [div_nonneg (sq_nonneg (log p)) vp.le]⟩
  have bound (i : Marking.Row) (hi : i∈A) (j : Marking.Row) (hj : j∈A) (eq : i.q=j.q) : |E i j|≤δ := by
    have mm := single_prime_row_mass (Nat.succ_pos n.log2) (rows i hi) ba
    change m i.q≤_ at mm
    have term : |(if i.second=j.second then 1-(log i.q)^2/V i.second else 1)|≤1 := by
      split <;> first | exact loss i.second i.q (rows i hi) | norm_num
    dsimp only [E];rw [if_pos eq,abs_mul,abs_mul,abs_mul,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _ : 0≤ m i.q)]
    exact (mul_le_mul (mul_le_mul (mul_le_mul mm (maxI i.second i.q (rows i hi)) (abs_nonneg _)
      (by positivity)) (maxI j.second j.q (rows j hj)) (abs_nonneg _) (by positivity)) term (abs_nonneg _)
      (by positivity)).trans_eq (by dsimp only [δ,d];ring)
  intro v
  have result := same_prime_gram_error (by omega : 3≤Fixed.d b) target a c e f A sub rows E δ (by dsimp [δ];positivity)
    (fun i _ j _ neq=>by dsimp only [E];rw [if_neg neq]) bound v
  change _ ≤ 2*d*δ*_ at result
  have small : 64*(2*d*δ)≤1 := by dsimp only [δ];field_simp;norm_num
  have last := mul_le_mul_of_nonneg_right small (Finset.sum_nonneg (s:=A) (fun i _=>sq_nonneg (v i)))
  linarith only [mul_le_mul_of_nonneg_left result (by norm_num : (0:ℝ)≤64),last]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.grid_same_prime_compensation
