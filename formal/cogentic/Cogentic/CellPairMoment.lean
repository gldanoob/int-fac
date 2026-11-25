import Cogentic.MarkIntervals
import Cogentic.PairCentering

namespace Cogentic.Construction
open Finset Real

/-- The squared two-point correction for a centered weight on the actual
constructor marks in a cell, including the contribution of large divisors. -/
theorem centered_cell_pair_moment (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
    let b := n.log2+1
    ∀ (cell : Option (Bool × Fin (Fixed.d b))) (u v s t : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) (D V : ℝ),
    let lo := firstCellMark b cell
    let M := cellMarkCount b
    let B := Fixed.B b
    let X := (Ico lo (lo+M)).filter (fun x => x ∈ (construct n ell u v s t).marks)
    (∀ p∈P, p.Prime ∧ Fixed.d b < p ∧ p ≤ B) →
    0≤D → 0≤V → (∀ x∈X, |w x|≤D) → (∑ i ∈ range M, w (lo+i))=0 →
    |w (lo+(M-1))|+(∑ i ∈ range (M-1), |w (lo+(i+1))-w (lo+i)|) ≤ V →
    (∑ x∈X, ∑ y∈X, w x*w y*(pairGamma P (Fixed.rootBase n) x y)^2) ≤
      (V*((1+2*exp 6)*M)*exp (-K*(Fixed.z b:ℝ)^2))^2*exp (8/(Fixed.d b:ℝ))+
      (D*((M:ℝ)/B+1)*(D*M))*exp (48*(Fixed.z b:ℝ)) := by
  classical
  obtain ⟨n₁,weighted⟩ := weighted_constructed_marks line K hK
  obtain ⟨b₀,weights⟩ := fixed_pair_weight_sum line
  refine ⟨max n₁ (2^b₀),?_⟩
  intro n hn ell target comp absent b cell u v s t P w D V lo M B X primes Dp Vp bounded center variation
  have ⟨one,two⟩ := max_le_iff.mp hn
  have npos := (Nat.pow_pos (by decide : 0<2)).trans_le two
  have bbig : b₀≤b := ((Nat.le_log2 npos.ne').mpr two).trans (Nat.le_succ _)
  have dp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have grid := fixed_grid_interval dp cell
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  let c := V*((1+2*exp 6)*M)*e
  have Bpos : 0<B := Nat.pow_pos (by decide)
  have Bs : B^2 ≤ M := by
    dsimp only [B,Fixed.B,Fixed.beta,M,cellMarkCount]
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have pr (p) (h : p∈P) := (primes p h).1
  have short (T : Finset ℕ) (sub : T ⊆ P) (low : sieveProduct T ≤ B) (r : ℕ)
      (lt : r < sieveProduct T) (good : ∀ p∈T, ¬r ≡ Fixed.rootBase n [MOD p]) :
      |∑ x ∈ X with x%(sieveProduct T)=r, w x| ≤ c/(sieveProduct T:ℝ) := by
    let q := sieveProduct T
    let marks := (construct n ell u v s t).marks
    let ρ := ∏ p ∈ (markModulus n ell).primeFactors with ¬p ∣ q, (1-(p:ℝ)⁻¹)
    have qp : 0<q := prod_pos (fun p hp => (pr p (sub hp)).pos)
    have elig (p : ℕ) (hp : p∈(markModulus n ell).primeFactors) (divp : p∣q) : ¬r ≡ Fixed.rootBase n [MOD p] := by
      have pp := Nat.prime_of_mem_primeFactors hp
      obtain ⟨a,atT,pa⟩ := (pp.prime.dvd_finsetProd_iff id).mp divp
      have heq := (Nat.prime_dvd_prime_iff_eq pp (pr a (sub atT))).mp pa
      exact good p (heq ▸ atT)
    have est := weighted n one ell target comp absent lo M q r u v s t (fun i => w (lo+i)) qp elig
      (fun x hx _ => grid x hx)
    have eq : (∑ i ∈ range M, w (lo+i)*(if lo+i ≡ r [MOD q] ∧ lo+i ∈ marks then 1 else 0)) =
        ∑ x ∈ X with x%q=r, w x := by
      simp_rw [mul_ite,mul_one,mul_zero]
      have shift := sum_Ico_eq_sum_range (fun x => if x ≡ r [MOD q] ∧ x∈marks then w x else 0) lo (lo+M)
      simp only [Nat.add_sub_cancel_left] at shift
      rw [←shift,←sum_filter]
      congr 1
      ext x
      have rr : r%q = r := Nat.mod_eq_of_lt lt
      constructor
      · intro h
        obtain ⟨xi,xq,xm⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨xi,xm⟩,(show x%q = r%q from xq).trans rr⟩
      · intro h
        obtain ⟨xx,xq⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_filter.mp xx).1,xq.trans rr.symm,(mem_filter.mp xx).2⟩
    change |∑ i ∈ range M, w (lo+i)*((if lo+i ≡ r [MOD q] ∧ lo+i ∈ marks then 1 else 0)-ρ/q)| ≤ _ at est
    simp_rw [mul_sub] at est
    rw [sum_sub_distrib,eq,←sum_mul,center,zero_mul,sub_zero] at est
    have bq : (B:ℝ)*q ≤ M := by exact_mod_cast (Nat.mul_le_mul_left B low).trans ((sq B) ▸ Bs)
    have qr : 0<(q:ℝ) := by exact_mod_cast qp
    have len : (B:ℝ) ≤ (M:ℝ)/q := (le_div_iff₀ qr).mpr bq
    have up := add_le_add len (le_refl (2*((M:ℝ)/q)*exp 6))
    have bound := mul_le_mul variation (mul_le_mul_of_nonneg_right up (exp_pos (-K*(Fixed.z b:ℝ)^2)).le)
      (show 0 ≤ ((B:ℝ)+2*((M:ℝ)/q)*exp 6)*e by dsimp [e]; positivity) Vp
    apply est.trans
    apply bound.trans_eq
    change V*((M/q+2*(M/q)*exp 6)*e) = c/(q:ℝ)
    dsimp only [c]
    ring
  let A := D*((M:ℝ)/B+1)
  have Ap : 0≤A := by dsimp only [A]; positivity
  have mid (T : Finset ℕ) (_ : T⊆P) (low : B < sieveProduct T) (_ : sieveProduct T ≤ B^2) (r : ℕ) :
      (∑ x ∈ X with x ≡ r [MOD sieveProduct T], |w x|) ≤ A := by
    let q := sieveProduct T
    let F := X.filter (fun x => x ≡ r [MOD q])
    let G := (Ico lo (lo+M)).filter (fun x => x ≡ r [MOD q])
    have card : (F.card:ℝ)≤G.card := by
      exact_mod_cast card_le_card (show F⊆G from fun x h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩)
    have cnt := (abs_le.mp (interval_residue_error (Nat.le_add_right lo M) (Bpos.trans low) r)).2
    change (G.card:ℝ)-(((lo+M:ℕ):ℝ)-lo)/q ≤ 1 at cnt
    simp only [Nat.cast_add,add_sub_cancel_left] at cnt
    have frac := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) M)
      (show 0<(B:ℝ) by exact_mod_cast Bpos) (show (B:ℝ)≤q by exact_mod_cast low.le)
    calc _ ≤ ∑ _x ∈ F, D := sum_le_sum (fun x h => bounded x (mem_filter.mp h).1)
         _ = D*F.card := by simp [mul_comm]
         _ ≤ A := mul_le_mul_of_nonneg_left (by linarith only [card,cnt,frac]) Dp
  have cap : X.card ≤ M := (card_le_card (filter_subset ..)).trans_eq (by simp)
  have mass : (∑ x∈X, |w x|) ≤ D*M := by
    calc _ ≤ ∑ _x∈X, D := sum_le_sum bounded
         _ = D*X.card := by simp [mul_comm]
         _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast cap) Dp
  have result := centered_pair_bound X P pr (Fixed.rootBase n) (Fixed.d b) B dp Bpos
    (fun p h => (primes p h).2) w c A short mid Ap
  have totalPos : 0 ≤ ∑ T∈P.powerset, pairDivisorWeight T := sum_nonneg (fun T h =>
    prod_nonneg (fun p hp => by
      have q : (2:ℝ)≤p := by exact_mod_cast (pr p (mem_powerset.mp h hp)).two_le
      exact div_nonneg (by linarith) (sq_nonneg _)))
  exact result.trans (add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left mass Ap)
    (weights b bbig P primes) totalPos (by positivity)))

end Cogentic.Construction
