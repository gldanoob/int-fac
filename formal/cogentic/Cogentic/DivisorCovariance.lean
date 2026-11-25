import Cogentic.FullPairCovariance
import Cogentic.CleanArithmetic

namespace Cogentic.Window
open Real

/-- The actual smooth Gaussian restricted to multiples of a divisor. -/
noncomputable def divisorGaussian (J : Finset ℕ) (d : ℕ) (Y S : ℝ) : ℝ :=
  ∑ n ∈ (squarefreeSupport J).filter (d ∣ ·), gaussian Y S n

theorem divisorGaussian_one (J : Finset ℕ) (Y S : ℝ) : divisorGaussian J 1 Y S=gaussianMass J Y S := by
  simp [divisorGaussian,gaussianMass]

/-- Dividing the marked squarefree support removes a single prime
    from both the available factors and the divisibility condition. -/
theorem divisorGaussian_insert (J : Finset ℕ) (pj : ∀ p∈J, p.Prime) (p d : ℕ) (hp : p∈J)
    (Y S : ℝ) (sp : 0<S) :
    divisorGaussian J (p*d) Y S = (1/(p:ℝ))*divisorGaussian (J.erase p) d (Y/p) (S/p) := by
  classical
  have pp := (pj p hp).pos
  have pr : (0:ℝ)<p := by exact_mod_cast pp
  have filt : (squarefreeSupport J).filter (p*d ∣ ·)=
      ((squarefreeSupport J).filter (p ∣ ·)).filter (p*d ∣ ·) := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, (dvd_mul_right p d).trans h.2⟩,h.2⟩,fun h => ⟨h.1.1,h.2⟩⟩
  rw [divisorGaussian,divisorGaussian,filt,marked_prime_support J pj p hp,Finset.sum_filter,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left pp h),Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Nat.mul_dvd_mul_iff_left pp]
  split <;> rename_i h
  · have eq := gaussian_rescale 1 (p:ℝ) Y S ((p:ℝ)*m) pr.ne' sp.ne'
    rw [mul_div_cancel_left₀ _ pr.ne',one_mul] at eq
    simpa only [Nat.cast_mul] using eq.symm
  · simp

/-- Divisor mass in the common Euler normalization. -/
noncomputable def divisorAtom (J : Finset ℕ) (d : ℕ) (Y S α : ℝ) : ℝ :=
  2*π*divisorGaussian J d Y S /(Y^(α-1)*eulerMass J α)

/-- Each actual divisibility insertion contributes exactly its Bernoulli
    weight to the tilted Gaussian with that prime deleted. -/
theorem divisorAtom_insert (J : Finset ℕ) (pj : ∀ p∈J, p.Prime) (p d : ℕ) (hp : p∈J)
    (Y S α : ℝ) (yp : 0<Y) (sp : 0<S) :
    divisorAtom J (p*d) Y S α =
      primeProbability α p*divisorAtom (J.erase p) d (Y/p) (S/p) α := by
  let G := divisorGaussian (J.erase p) d (Y/p) (S/p)
  let F := Y^(α-1)*eulerMass J α
  let E := (Y/(p:ℝ))^(α-1)*eulerMass (J.erase p) α
  have prime := (pj p hp).pos
  have pp : (0:ℝ)<p := by exact_mod_cast prime
  have fp : 0<F := mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)
  have ep : 0<E := mul_pos (rpow_pos_of_pos (div_pos yp pp) _) (eulerMass_pos _ _)
  have tilt : (1/(p:ℝ))*E=primeProbability α p*F := inserted_tilted_mass J p hp prime Y α yp
  rw [divisorAtom,divisorAtom,divisorGaussian_insert J pj p d hp Y S sp]
  change 2*π*(1/(p:ℝ)*G)/F=primeProbability α p*(2*π*G/E)
  apply (div_eq_iff fp.ne').mpr
  rw [show primeProbability α p*(2*π*G/E)*F=(primeProbability α p*F)*(2*π*G/E) by ring,←tilt]
  field_simp

/-- All conditional divisor probabilities are invariant under the common
    Euler normalization. -/
theorem divisorAtom_ratio (J : Finset ℕ) (d : ℕ) (Y S α : ℝ) (yp : 0<Y) :
    divisorGaussian J d Y S / gaussianMass J Y S = divisorAtom J d Y S α/divisorAtom J 1 Y S α := by
  let F := Y^(α-1)*eulerMass J α
  have fp : F ≠ 0 := (mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)).ne'
  rw [divisorAtom,divisorAtom,divisorGaussian_one]
  change _ = (2*π*divisorGaussian J d Y S/F)/(2*π*gaussianMass J Y S/F)
  rw [div_div_div_cancel_right₀ fp,mul_div_mul_left _ _ (mul_ne_zero (by norm_num) pi_pos.ne')]

/-- Individual one-prime frequencies and the two-prime covariance of
    the actual squarefree smooth indicator, on its genuine full Gaussian
    distribution. The curvature is the variance of the uncut saddle. -/
theorem fixed_divisibility_covariance (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α Y S : ℝ) (D₀ : Finset ℕ) (p q : ℕ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    let K := J\D₀
    let V := saddleVariance J (primeProbability α) (fun r=>log r)
    let P := fun d : ℕ => divisorGaussian K d Y S/gaussianMass K Y S
    let w := primeProbability α
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    saddleMean J α = H*u → log Y = H*u → 0 < Y → 0 < S →
    B^(17/200:ℝ) ≤ Y/S → Y/S ≤ B^(17/100:ℝ) → D₀.card+2 ≤ b^k →
    D₀ ⊆ J → p ∈ K → q ∈ K → p≠q →
    |P p/w p-1| ≤ 48/u ∧ |P q/w q-1| ≤ 48/u ∧
    |P (p*q)-P p*P q*(1-log p*log q/V)| ≤ (w p*w q)*(C/u^2) := by
  classical
  obtain ⟨C,cp,n₀,full⟩ := fixed_full_insertions line k
  refine ⟨C,cp,n₀,?_⟩
  intro b big u α Y S D₀ p q B H J K V P w lo hi ha mean logY yp sp rlo rhi dc sub pm qm ne
  let h := log (p:ℝ)
  let j := log (q:ℝ)
  have pJ := (Finset.mem_sdiff.mp pm).1
  have qJ := (Finset.mem_sdiff.mp qm).1
  have primeK (n) (hn : n∈K) : n.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).2
  have pp := primeK p pm
  have qp := primeK q qm
  have pR : (0:ℝ)<p := by exact_mod_cast pp.pos
  have qR : (0:ℝ)<q := by exact_mod_cast qp.pos
  have hp : 0<h := log_pos (by exact_mod_cast pp.one_lt)
  have jp : 0<j := log_pos (by exact_mod_cast qp.one_lt)
  have hj : h≠j := by
    intro eq
    apply ne
    exact_mod_cast (log_injOn_pos pR qR eq)
  let D := fun x : ℝ => if x=h+j then insert p (insert q D₀) else if x=h then insert p D₀
    else if x=j then insert q D₀ else D₀
  have d0 : D 0=D₀ := by simp [D,ne_of_lt hp,ne_of_lt jp,show 0≠h+j by linarith]
  have dh : D h=insert p D₀ := by simp [D,show h≠h+j by linarith]
  have dj : D j=insert q D₀ := by simp [D,show j≠h+j by linarith,hj.symm]
  have dhj : D (h+j)=insert p (insert q D₀) := by simp [D]
  have sets (x : ℝ) (_ : |x| ≤2*H) : (D x).card ≤ b^k ∧ D x⊆J := by
    have choose : D x⊆insert p (insert q D₀) := by
      intro z mem
      dsimp only [D] at mem
      split at mem
      · exact mem
      split at mem
      · rcases Finset.mem_insert.mp mem with rfl | h
        · exact Finset.mem_insert_self ..
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      split at mem
      · exact Finset.mem_insert_of_mem mem
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem)
    have size := (Finset.card_le_card choose).trans (Finset.card_insert_le ..)
    have qq := Finset.card_insert_le q D₀
    refine ⟨by omega,choose.trans (Finset.insert_subset pJ (Finset.insert_subset qJ sub))⟩
  have top (n : ℕ) (mem : n∈J) : log n ≤ H := by
    obtain ⟨s,pr⟩ := Finset.mem_filter.mp mem
    have hi' := (Finset.mem_Ioc.mp s).2
    apply log_le_log (by exact_mod_cast pr.pos)
    exact (Nat.cast_le.mpr hi').trans (Nat.floor_le (by dsimp [B,Fixed.B]; positivity))
  have hh : |h| ≤ H := by rw [abs_of_pos hp]; exact top p pJ
  have jj : |j| ≤ H := by rw [abs_of_pos jp]; exact top q qJ
  let g := fun x => shiftedGaussianAtom J (D x) Y S α x
  obtain ⟨gpos,ph,qh,pqh⟩ := full b big u α Y S h j D lo hi ha mean logY yp sp rlo rhi hh jj sets
  have base : divisorAtom K 1 Y S α=g 0 := by simp [g,shiftedGaussianAtom,d0,divisorAtom,divisorGaussian_one,K]
  have onep (r : ℕ) (mem : r∈K) (rr : 0 < (r:ℝ)) (dx : D (log r)=insert r D₀) :
      divisorAtom K r Y S α=w r*g (log r) := by
    have step := divisorAtom_insert K primeK r 1 mem Y S α yp sp
    rw [Nat.mul_one] at step
    rw [step]
    congr 1
    have eq : J \ insert r D₀ = K.erase r := by ext z; simp [K]; tauto
    simp [divisorAtom,divisorGaussian_one,g,shiftedGaussianAtom,exp_log rr,dx,eq]
  have qerase : q∈K.erase p := Finset.mem_erase.mpr ⟨ne.symm,qm⟩
  have pair : divisorAtom K (p*q) Y S α = (w p*w q)*g (h+j) := by
    rw [divisorAtom_insert K primeK p q pm Y S α yp sp]
    have step := divisorAtom_insert (K.erase p) (fun r hr=>primeK r (Finset.mem_erase.mp hr).2)
      q 1 qerase (Y/p) (S/p) α (div_pos yp pR) (div_pos sp pR)
    rw [Nat.mul_one] at step
    rw [step,mul_assoc]
    congr 2
    have eq : J \ insert p (insert q D₀) = (K.erase p).erase q := by ext z; simp [K]; tauto
    simp [divisorAtom,divisorGaussian_one,g,shiftedGaussianAtom,dhj,eq,exp_add,h,j,
      exp_log pR,exp_log qR,div_div]
  have prob (r : ℕ) : P r=divisorAtom K r Y S α/g 0 := by
    rw [←base]
    exact divisorAtom_ratio K r Y S α yp
  have wp : 0<w p := by dsimp [w,primeProbability]; positivity
  have wq : 0<w q := by dsimp [w,primeProbability]; positivity
  have e1 : P p=w p*(g h/g 0) := by rw [prob,onep p pm pR dh]; ring
  have e2 : P q=w q*(g j/g 0) := by rw [prob,onep q qm qR dj]; ring
  have e12 : P (p*q)=(w p*w q)*(g (h+j)/g 0) := by rw [prob,pair]; ring
  rw [e1,e2,e12,mul_div_cancel_left₀ _ wp.ne',mul_div_cancel_left₀ _ wq.ne']
  refine ⟨ph,qh,?_⟩
  have eq : (w p*w q)*(g (h+j)/g 0)-
      w p*(g h/g 0)*(w q*(g j/g 0))*(1-log p*log q/V)=
      (w p*w q)*(g (h+j)/g 0-(g h/g 0)*(g j/g 0)*(1-h*j/V)) := by ring
  rw [eq,abs_mul,abs_of_pos (mul_pos wp wq)]
  exact mul_le_mul_of_nonneg_left pqh (mul_pos wp wq).le


end Cogentic.Window
