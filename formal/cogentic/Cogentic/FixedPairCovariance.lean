import Cogentic.FixedOmissions
import Cogentic.SaddleNormalization

namespace Cogentic.Window
open Real

private theorem relative_budget {u m D : ℝ} (hu : 1 ≤ u)
    (md : m ≤ D) (d : D ≤ 1/u^5) :
    (4*D+16*u*m)*sqrt u ≤ 20/u^2 := by
  have up : 0<u := by linarith
  have su : sqrt u ≤ u := (sqrt_le_left up.le).mpr (by nlinarith [mul_nonneg up.le (sub_nonneg.mpr hu)])
  have elev (n : ℕ) : u^n ≤ u^(n+1) := pow_le_pow_right₀ hu (Nat.le_succ _)
  have wt : 4*D+16*u*m ≤ 20*u*(1/u^5) := by
    have x := mul_le_mul_of_nonneg_left (md.trans d) (by positivity : 0 ≤ 16*u)
    have y := mul_le_mul_of_nonneg_right hu (show 0 ≤ 1/u^5 by positivity)
    linarith only [x,y,d]
  calc _ ≤ (20*u*(1/u^5))*u := mul_le_mul wt su (sqrt_nonneg _) (by positivity)
       _ = 20/u^3 := by field_simp
       _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) (elev 2)

private theorem covariance_budget {u E m δ ε η : ℝ} (hu : 1 ≤ u) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hε : ε ≤ E/u^2) (hh : η ≤ 9/u) (hd : δ ≤ 2/u) (hm : m ≤ 1/u) :
    4*(4*ε+2*η^2+δ*(2*η+η^2))+18*m*δ ≤ (16*E+2000)/u^2 := by
  have up : 0<u := by linarith
  have η2 := pow_le_pow_left₀ hη hh 2
  have ds : δ*(2*η+η^2) ≤ (2/u)*(2*(9/u)+(9/u)^2) :=
    mul_le_mul hd (by linarith only [hh,η2]) (by positivity) (by positivity)
  have ms := mul_le_mul hm hd hδ (by positivity : 0 ≤ 1/u)
  have cubic : 1/u^3 ≤ 1/u^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ hu (by decide : 2 ≤ 3))
  have poly : 4*(4*(E/u^2)+2*(9/u)^2+(2/u)*(2*(9/u)+(9/u)^2))+18*(1/u)*(2/u) =
      (16*E+828)/u^2+648/u^3 := by field_simp; ring
  calc _ ≤ 4*(4*(E/u^2)+2*(9/u)^2+(2/u)*(2*(9/u)+(9/u)^2))+18*(1/u)*(2/u) := by linarith only [ds,ms,η2,hε]
       _ = _ := poly
       _ ≤ (16*E+828)/u^2+648/u^2 := by
           apply add_le_add_right
           exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
             (pow_le_pow_right₀ hu (by decide : 2 ≤ 3)))
       _ ≤ _ := by rw [←add_div]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The fixed degree schedule gives simultaneous first and second
    normalized insertion estimates on the actual squarefree central mass.
    The covariance uses the Bernoulli variance at the individual mark. -/
theorem fixed_central_insertions (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α h j : ℝ) (D : ℝ → Finset ℕ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    let r := primeProbability α
    let ell := fun p : ℕ => log p
    let f := fun a : ℝ => omittedMass J (D a) r ell H a
    let V := saddleVariance J r ell
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    saddleMean J α = H*u → |h| ≤ H → |j| ≤ H →
    (∀ a : ℝ, |a| ≤ 2*H → (D a).card ≤ b^k) →
    0 < f 0 ∧ (∀ x : ℝ, |x| ≤ 2*H → |f x/f 0-1| ≤ 36/u ∧ |f x/f 0| ≤ 3) ∧
    |f (h+j)/f 0-(f h/f 0)*(f j/f 0)*(1-h*j/V)| ≤ C/u^2 := by
  let A := 8000*(exp 1+3)*saddleEdgeworthConstant
  let E := 20+A
  have ap : 0 ≤ A := by dsimp [A]; exact mul_nonneg (by positivity) saddleEdgeworthConstant_nonneg
  have ep : 0 ≤ E := by dsimp [E]; linarith
  obtain ⟨n₁,del⟩ := fixed_prime_deletions k
  obtain ⟨n₂,deg⟩ := Fixed.degree_grows (max 50000 ⌈E⌉₊)
  refine ⟨16*E+2000,by positivity,max n₁ n₂,?_⟩
  intro b big u α h j D B H J r ell f V lo hi ha mean h1 h2 sizes
  obtain ⟨one,two⟩ := max_le_iff.mp big
  have db := deg b two
  have Eu : E ≤ (Fixed.d b:ℝ) := (Nat.le_ceil E).trans (by exact_mod_cast (le_max_right ..).trans db)
  have Du : (50000:ℝ) ≤ Fixed.d b := by exact_mod_cast (le_max_left ..).trans db
  obtain ⟨hp,large,mp,md,dsmall,rb,dels⟩ := del b one u α lo hi ha
  let m := B^(-199/400:ℝ)
  let d := (b:ℝ)^k*m
  change 0 ≤ m at mp
  change m ≤ d at md
  change d ≤ 1/u^5 at dsmall
  have dp := mp.trans md
  have up : 0<u := by linarith
  have hu : 1 ≤ u := by linarith
  have r0 (p) (_ : p∈J) : 0 ≤ r p := by dsimp [r,primeProbability]; positivity
  have rm (p) (hx : p∈J) : r p ≤ m := (rb p hx).1
  have band (p) (hx : p∈J) : H/2 ≤ ell p ∧ ell p ≤ H := (rb p hx).2
  have hb (p) (hx : p∈J) : |ell p| ≤ H := abs_le.mpr ⟨by linarith [(band p hx).1],(band p hx).2⟩
  have oneu : m ≤ 1/u := (md.trans dsmall).trans (div_le_div_of_nonneg_left zero_le_one up
    (by simpa using pow_le_pow_right₀ hu (by decide : 1 ≤ 5)))
  have half : m ≤ 1/2 := oneu.trans (div_le_div_of_nonneg_left zero_le_one (by norm_num) large)
  have rh (p) (hx : p∈J) : r p ≤ 1/2 := (rm p hx).trans half
  have hD (x : ℝ) (hx : |x| ≤ 2*H) : (∑ p∈J, if p∈D x then r p else 0) ≤ d :=
    dels (D x) (sizes x hx)
  let W := poissonMoment J r ell 2
  let δ := H^2/W
  let ε := insertionError J r ell H d
  let η := 4*δ+ε
  obtain ⟨wlo,_,err,_⟩ := insertion_error_bound r ell hp up dp mp r0 rm band mean
  change H^2*u/2 ≤ W at wlo
  have wp : 0<W := (by positivity : 0<H^2*u/2).trans_le wlo
  have δp : 0 ≤ δ := by dsimp [δ]; positivity
  have δu : δ ≤ 2/u := (div_le_div_iff₀ wp up).mpr (by linarith only [wlo])
  have εp : 0 ≤ ε := by
    dsimp [ε,insertionError]
    have edge := saddleEdgeworthConstant_nonneg
    positivity
  have ηp : 0 ≤ η := by dsimp [η]; positivity
  have εu : ε ≤ E/u^2 := by
    change ε ≤ (4*d+16*u*m)*sqrt u+A/u^2 at err
    refine err.trans ((add_le_add_left (relative_budget hu md dsmall) _).trans_eq ?_)
    dsimp only [E]; ring
  have Eu' : E ≤ u := by linarith only [Eu,lo,Du]
  have smallε : ε ≤ 1/u := εu.trans ((div_le_div_iff₀ (by positivity) up).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_right Eu' up.le]))
  have ηu : η ≤ 9/u := (add_le_add (mul_le_mul_of_nonneg_left δu (by norm_num : (0:ℝ)≤4)) smallε).trans_eq (by ring)
  have small : η ≤ 1/2 := ηu.trans ((div_le_div_iff₀ up (by norm_num)).mpr (by linarith only [lo,Du]))
  have single (x : ℝ) (hx' : |x| ≤ 2*H) : 0<f 0 ∧ |f x/f 0-1| ≤ 36/u ∧ |f x/f 0| ≤ 3 := by
    have p := saddle_single_ratio J (D 0) (D x) r ell H x d hp r0 rh hb wp hx'
      (hD 0 (by rw [abs_zero]; positivity)) (hD x hx') small
    exact ⟨p.1,p.2.1.trans ((mul_le_mul_of_nonneg_left ηu (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by ring)),p.2.2⟩
  refine ⟨(single 0 (by rw [abs_zero]; positivity)).1,fun x hx => (single x hx).2,?_⟩
  have pair := saddle_pair_covariance_bernoulli J D r ell H h j d m hp mp r0 rh rm hb wp h1 h2 hD small
  exact pair.trans (covariance_budget hu δp ηp εu ηu δu oneu)

end Cogentic.Window
