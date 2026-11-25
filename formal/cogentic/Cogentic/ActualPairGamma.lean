import Cogentic.PairGridSieve
import Cogentic.ScalarSteps
import Cogentic.FixedErrorBudget

namespace Cogentic.Construction
open Finset Real Cogentic.Window

/-- Small primes whose coincidences are retained in the pair sieve. -/
def pairCorrectionPrimes (b : ℕ) : Finset ℕ :=
  (Nat.primesLE (2^(200*Fixed.h b))).filter (Fixed.d b < ·)

theorem mem_pairCorrectionPrimes {b p : ℕ} : p∈pairCorrectionPrimes b ↔
    p.Prime ∧ Fixed.d b < p ∧ p ≤ 2^(200*Fixed.h b) := by
  simp only [pairCorrectionPrimes,mem_filter,Nat.mem_primesLE]
  tauto

private theorem coincidence_product (a y m b : ℕ) (diff : y≠a) :
    let D := ((y:ℤ)-a).natAbs
    let S := D.primeFactors.filter (fun p : ℕ => Fixed.d b<p ∧ (p:ℝ) ≤ (2^(200*Fixed.h b):ℕ) ∧ ¬(p:ℤ)∣(a:ℤ)-m)
    ∏ p∈S,(p:ℝ)/((p:ℝ)-1) = pairGamma (pairCorrectionPrimes b) m a y := by
  classical
  intro D S
  dsimp only [pairGamma]
  apply Finset.prod_congr _ (fun _ _=>rfl)
  ext p
  have nz : D≠0 := by dsimp only [D]; omega
  have congr : (p∣D) ↔ a ≡ y [MOD p] := by
    rw [Nat.modEq_iff_dvd,Int.natCast_dvd]
  have shift : (p:ℤ)∣(a:ℤ)-m ↔ a ≡ m [MOD p] := by
    rw [←Nat.modEq_iff_dvd]; exact ⟨Nat.ModEq.symm,Nat.ModEq.symm⟩
  simp only [S,mem_filter,mem_pairCorrectionPrimes,Nat.mem_primeFactors_of_ne_zero nz,congr,shift,
    Nat.cast_le]
  tauto

private theorem remaining_prime_count {k b : ℕ} (hp : 0<Fixed.h b) (kp : 0<k)
    (cap : k≤2^(12000*Fixed.h b)) :
    (k.primeFactors.filter (fun p : ℕ => (2^(200*Fixed.h b):ℕ)<p)).card≤60 := by
  let T := k.primeFactors.filter (fun p : ℕ => (2^(200*Fixed.h b):ℕ)<p)
  have prod := (prod_dvd_prod_of_subset T k.primeFactors id (filter_subset ..)).trans (Nat.prod_primeFactors_dvd _)
  have pow : 2^(200*Fixed.h b*T.card) ≤ 2^(12000*Fixed.h b) := calc
    _ = ∏ _p∈T, 2^(200*Fixed.h b) := by simp [pow_mul]
    _ ≤ ∏ p∈T, p := Finset.prod_le_prod' (fun p h=>(mem_filter.mp h).2.le)
    _ ≤ _ := (Nat.le_of_dvd kp prod).trans cap
  have ex := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp pow
  change T.card≤60
  exact Nat.le_of_mul_le_mul_left (c:=200*Fixed.h b) (by nlinarith only [ex]) (by omega)

private theorem correction_decay {b : ℕ} (hp : 0<Fixed.h b) :
    exp (60/(((2^(200*Fixed.h b):ℕ):ℝ)-1))-1 ≤ (Fixed.B b:ℝ)^(-17/200:ℝ) := by
  let Y : ℕ := 2^(100*Fixed.h b)
  have ylarge : 128≤Y := calc
    _ = 2^7 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have yl : 128≤(Y:ℝ) := by exact_mod_cast ylarge
  have yp : (0:ℝ)<Y := by linarith
  have eqT : (2^(200*Fixed.h b):ℕ)=Y^2 := by dsimp only [Y]; rw [←pow_mul]; congr 1; ring
  have eqB : (Fixed.B b:ℝ)=(Y:ℝ)^10 := by
    exact_mod_cast (show Fixed.B b=Y^10 by change 2^(1000*Fixed.h b)=(2^(100*Fixed.h b))^10; rw [←pow_mul]; congr 1; ring)
  rw [eqT,Nat.cast_pow]
  let x := 60/((Y:ℝ)^2-1)
  have t : (0:ℝ)<(Y:ℝ)^2-1 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤128) yl]
  have xn : 0≤x := div_nonneg (by norm_num) t.le
  have loss : 2*x ≤ (Y:ℝ)⁻¹ := by
    rw [←one_div,le_div_iff₀ yp]
    change 2*(60/((Y:ℝ)^2-1))*(Y:ℝ) ≤ 1
    field_simp
    nlinarith [mul_nonneg yp.le (sub_nonneg.mpr yl)]
  have small : x≤1 := by
    have iy : (Y:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have err := abs_le.mp (Real.abs_exp_sub_one_le (by rwa [abs_of_nonneg xn]))
  have rem : exp x-1 ≤ (Y:ℝ)⁻¹ := by simpa only [abs_of_nonneg xn] using err.2.trans (by simpa only [abs_of_nonneg xn] using loss)
  apply rem.trans
  rw [eqB,←Real.rpow_natCast_mul yp.le]
  norm_num
  rw [←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤(Y:ℝ)) (by norm_num)

/-- In the actual lattice at two different eligible positions, the ratio of
the two conductor factors differs from the sieve's pair correction by a
relative error of at most the specified logarithmic-square decay. -/
theorem PrescribedRows.pair_gamma_correction (K : ℝ) (hK : 1≤K) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → ell∈dyadicTargets (Fixed.beta b) → a≤Fixed.A b → y≤Fixed.A b →
    y<Fixed.rootBase n → y≠a → ∀ side : Bool,
    let γ := pairGamma (pairCorrectionPrimes b) (Fixed.rootBase n) a y
    let corr := coprimeFactor (R.secondStep a y side).natAbs/coprimeFactor (firstStep n ell y side).natAbs
    1≤γ ∧ γ≤corr ∧ corr≤γ*(1+exp (-K*(Fixed.z b:ℝ)^2)) := by
  classical
  obtain ⟨b₀,save⟩ := fixed_band_power_savings K hK
  refine ⟨b₀,?_⟩
  intro n ell a y R b large target ac yc ym diff side γ corr
  let m := Fixed.rootBase n; let d := Fixed.d b; let h := Fixed.h b; let T : ℕ := 2^(200*h)
  let D := ((y:ℤ)-a).natAbs
  let G := prodPrimes (R.hit a ∩ R.hit y); let F := prodPrimes (R.miss a \ R.hit y)
  let U := primorial d*(if hitsTarget n ell y side then 1 else ell)
  let k := D/G*F
  have hp : 0<h := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _)
  have tp : 1<T := Nat.one_lt_two_pow (by omega)
  have tc : 1<(T:ℝ) := by exact_mod_cast tp
  have te : T<ell := (Nat.pow_le_pow_right (by decide : 0<2)
    (show 200*h≤Fixed.beta b-1 by change 200*h≤1000*h-1; omega)).trans_lt (mem_dyadicTargets.mp target).2.1
  have ep := (mem_dyadicTargets.mp target).1
  have factors := R.second_factors a y
  have gd : G∣D := Int.natCast_dvd.mp factors.2.2.1
  have gp : 0<G := factors.2.2.2.1
  have fp : 0<F := factors.2.2.2.2.2.1
  have dp : 0<D := by dsimp [D]; omega
  have kp : 0<k := Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd dp gd) gp) fp
  have ub : 0<U := Nat.mul_pos (primorial_pos _) (by split <;> omega)
  have loc (p : ℕ) (pp : p.Prime) (le : (p:ℝ)≤T) : (p∣U ↔ p≤d) ∧ ¬p∣F ∧ ¬p∣G := by
    have lt : p≤T := by exact_mod_cast le
    have pe : ¬p∣ell := fun div => (lt.trans_lt te).ne ((Nat.prime_dvd_prime_iff_eq pp ep).mp div)
    have pf : p∉R.primes := by
      intro pm
      have log := (mem_primeBand.mp (mem_filter.mp (R.member pm)).1).2.2
      have small : T^2 ≤ Fixed.B b := by
        change (2^(200*h))^2 ≤ 2^(1000*h)
        rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
      exact log.not_ge ((Nat.pow_le_pow_left lt 2).trans small)
    have notDiv (s : Finset ℕ) (hs : s⊆R.primes) : ¬p∣prodPrimes s := by
      intro dvd
      have eq : (prodPrimes s).primeFactors = s := Nat.primeFactors_prod (fun t ht => R.prime (hs ht))
      exact pf (hs (eq ▸ pp.mem_primeFactors dvd (R.subprod_bounds hs).1.ne'))
    refine ⟨?_,notDiv _ (sdiff_subset.trans sdiff_subset),notDiv _ (inter_subset_left.trans (filter_subset ..))⟩
    dsimp only [U]; split <;> simp [pp.dvd_mul,pp.dvd_primorial_iff,pe]
  have res := two_point_coprime_correction (a:ℤ) (y:ℤ) (m:ℤ) G F U d (T:ℝ)
    tc (by exact_mod_cast diff) (by exact_mod_cast ym.ne) fp.ne' ub.ne' gd loc
  have absGap : ((y:ℤ)-m).natAbs=m-y := natAbs_gap ym.le
  have dist : ((y:ℤ)-a).natAbs=y.dist a := by simp [Nat.dist]; omega
  have size1 := (firstStep_size ym ep.pos side).1
  have size2 := (R.secondStep_size ym ep.pos diff side).1
  have form : corr = coprimeFactor ((U*((y:ℤ)-m).natAbs)*k)/coprimeFactor (U*((y:ℤ)-m).natAbs) := by
    dsimp only [corr]; rw [size1,size2,absGap]
    dsimp only [secondModulus,firstModulus,U,k,D,G,F]
    simp only [dist,m,d,b,Nat.mul_assoc]
  have gamma := coincidence_product a y m b diff
  change _=γ at gamma
  dsimp only at res
  rw [gamma,←form] at res
  have gp1 : 1≤γ := by
    apply Finset.one_le_prod
    intro p pm
    have pos : 1<(p:ℝ) := by exact_mod_cast (mem_pairCorrectionPrimes.mp (mem_filter.mp pm).1).1.one_lt
    exact (one_le_div (sub_pos.mpr pos)).mpr (by linarith)
  have cap : k ≤ 2^(12000*h) := calc
    _ ≤ Fixed.A b * (Fixed.B b)^2 := Nat.mul_le_mul ((Nat.div_le_self ..).trans (by dsimp only [D]; omega)) factors.2.2.2.2.2.2
    _ = _ := by change 2^(10000*h)*(2^(1000*h))^2=2^(12000*h); rw [←pow_mul,←pow_add]; congr 1; ring
  have count := remaining_prime_count hp kp cap
  have cc : (((k.primeFactors.filter (fun p:ℕ => (T:ℝ) < p)).card:ℕ):ℝ)≤60 := by
    exact_mod_cast (by simpa only [Nat.cast_lt] using count : (k.primeFactors.filter (fun p:ℕ => (T:ℝ) < p)).card ≤60)
  have monot := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right cc (sub_nonneg.mpr tc.le))
  have err := (correction_decay hp).trans (save b large)
  refine ⟨gp1,res.1,res.2.trans (mul_le_mul_of_nonneg_left (monot.trans (by linarith only [err])) (zero_le_one.trans gp1))⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.pair_gamma_correction
