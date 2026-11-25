import Cogentic.DivisorCovariance
import Cogentic.RelativeClass

namespace Cogentic.Window
open Real

/-- Real mass of one reduced scalar class on the finite squarefree support. -/
noncomputable def classWeight {q : ℕ} (J : Finset ℕ) (Y S : ℝ) (r : (ZMod q)ˣ) : ℝ :=
  ∑ n∈squarefreeSupport J, if (r:ZMod q)=n then gaussian Y S n else 0

theorem coe_classWeight {q : ℕ} (J : Finset ℕ) (Y S : ℝ) (r : (ZMod q)ˣ) :
    (classWeight J Y S r:ℂ)=classMass (squarefreeSupport J) (fun n=>(gaussian Y S n:ℂ)) r := by
  unfold classWeight classMass
  simp [apply_ite Complex.ofReal]

/-- The unit classes partition all Gaussian mass on a sieve band
    coprime to the modulus. -/
theorem classWeight_sum {q : ℕ} [NeZero q] (J : Finset ℕ) (Y S : ℝ)
    (cop : ∀ n∈squarefreeSupport J, n.Coprime q) :
    (∑ r : (ZMod q)ˣ, classWeight J Y S r)=gaussianMass J Y S := by
  unfold classWeight gaussianMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let v := ZMod.unitOfCoprime n (cop n hn)
  have val : (v:ZMod q)=n := ZMod.coe_unitOfCoprime n (cop n hn)
  have eq (r : (ZMod q)ˣ) : (r:ZMod q)=n ↔ r=v := by rw [←val,Units.val_inj]
  simp only [eq]
  simp

/-- A unit class cannot contain a smooth integer with a factor
    dividing its modulus. -/
theorem classWeight_coprime {q : ℕ} [NeZero q] (J : Finset ℕ) (primes : ∀ p∈J, p.Prime)
    (Y S : ℝ) (r : (ZMod q)ˣ) :
    classWeight J Y S r = classWeight (J\q.primeFactors) Y S r := by
  classical
  let K := J\q.primeFactors
  have subset : squarefreeSupport K⊆squarefreeSupport J := by
    intro n hn
    obtain ⟨sq,fac⟩ := (mem_squarefreeSupport K (fun p h=>primes p (Finset.mem_sdiff.mp h).1) n).mp hn
    exact (mem_squarefreeSupport J primes n).mpr ⟨sq,fac.trans Finset.sdiff_subset⟩
  unfold classWeight
  symm
  apply Finset.sum_subset subset
  intro n hn miss
  apply if_neg
  intro he
  have cop := (ZMod.isUnit_iff_coprime n q).mp (he ▸ r.isUnit)
  apply miss
  obtain ⟨sq,fac⟩ := (mem_squarefreeSupport J primes n).mp hn
  exact (mem_squarefreeSupport _ (fun p h=>primes p (Finset.mem_sdiff.mp h).1) n).mpr
    ⟨sq,fun p hp=>Finset.mem_sdiff.mpr ⟨fac hp,Finset.disjoint_left.mp cop.disjoint_primeFactors hp⟩⟩

/-- Multiplicative coarse equidistribution against the actual full
    smooth Gaussian on a band coprime to q. -/
def classBalanced (J : Finset ℕ) (q : ℕ) (Y S : ℝ) : Prop :=
  ∀ r : (ZMod q)ˣ, gaussianMass J Y S ≤ 3*q.totient*classWeight J Y S r ∧
    (q.totient:ℝ)*classWeight J Y S r ≤ 3*gaussianMass J Y S

theorem classBalanced_of_uniform {q : ℕ} [NeZero q] (J : Finset ℕ) (Y S c : ℝ)
    (cop : ∀ n∈squarefreeSupport J, n.Coprime q) (uniform : ∀ r : (ZMod q)ˣ,
      c ≤ classWeight J Y S r ∧ classWeight J Y S r ≤ 3*c) :
    classBalanced J q Y S := by
  have lo := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => (uniform r).1)
  have hi := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => (uniform r).2)
  rw [classWeight_sum J Y S cop] at lo hi
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul] at lo hi
  intro r
  have a := mul_le_mul_of_nonneg_left (uniform r).1 (Nat.cast_nonneg (α:=ℝ) q.totient)
  have b := mul_le_mul_of_nonneg_left (uniform r).2 (Nat.cast_nonneg (α:=ℝ) q.totient)
  constructor <;> linarith only [lo,hi,a,b]

theorem fixed_class_accuracy (C : ℝ) :
    ∃ n₀ : ℕ, ∀ b ≥ n₀, C*exp (-(Fixed.z b:ℝ)^2) ≤ 1/2 := by
  refine ⟨⌈2*C⌉₊,?_⟩
  intro b hb
  let z := (Fixed.z b:ℝ)
  have z1 : 1 ≤ z := by dsimp [z,Fixed.z]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le b.log2)
  have bz : (b:ℝ) ≤ exp z := by
    have n : (b:ℝ) ≤ (2:ℝ)^(Fixed.z b) := by exact_mod_cast (Nat.lt_log2_self.le : b ≤ 2^(Fixed.z b))
    have t := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (by linarith [exp_one_gt_d9] : (2:ℝ) ≤ exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at t
    exact n.trans t
  have cb : 2*C≤b := (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have bound := (cb.trans bz).trans (exp_le_exp.mpr
    (show z≤z^2 by nlinarith only [mul_nonneg (by linarith : 0≤z) (sub_nonneg.mpr z1)]))
  have t := mul_le_mul_of_nonneg_right bound (exp_pos (-(z^2))).le
  rw [←exp_add,add_neg_cancel,exp_zero] at t
  change C*exp (-(z^2))≤1/2
  linarith

/-- The true first-coordinate scalar mass restricted to a local event. -/
noncomputable def classPart {q : ℕ} (J : Finset ℕ) (Y S : ℝ) (r : (ZMod q)ˣ)
    (event : ℕ → Prop) [DecidablePred event] : ℝ :=
  ∑ n∈(squarefreeSupport J).filter event, if (r:ZMod q)=n then gaussian Y S n else 0

theorem coe_classPart {q : ℕ} (J : Finset ℕ) (Y S : ℝ) (r : (ZMod q)ˣ)
    (event : ℕ → Prop) [DecidablePred event] :
    (classPart J Y S r event:ℂ)=classMass ((squarefreeSupport J).filter event) (fun n=>(gaussian Y S n:ℂ)) r := by
  unfold classPart classMass
  simp [apply_ite Complex.ofReal]

theorem gaussianMass_monotone {K J : Finset ℕ} (pr : ∀ p∈J, p.Prime) (sub : K⊆J)
    (Y S : ℝ) (sp : 0<S) : gaussianMass K Y S ≤ gaussianMass J Y S := by
  unfold gaussianMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨sf,fac⟩ := (mem_squarefreeSupport K (fun p h=>pr p (sub h)) n).mp hn
    exact (mem_squarefreeSupport J pr n).mpr ⟨sf,fac.trans sub⟩
  · intro n _ _; unfold gaussian; positivity

/-- A specified nonzero exceptional class has relative mass at most
    9/(p−1), including the loss from the two actual class estimates. -/
theorem nonzero_extra_class_cost {q p : ℕ} [NeZero q] (J : Finset ℕ)
    (pr : ∀ t∈J, t.Prime) (pp : p.Prime) (cop : q.Coprime p)
    (Y S : ℝ) (sp : 0<S) (r : (ZMod q)ˣ) (s : (ZMod p)ˣ)
    (main : classBalanced J q Y S) (extra : classBalanced (J\(q*p).primeFactors) (q*p) Y S) :
    classPart J Y S r (fun n => (s:ZMod p)=(n:ZMod p)) ≤
      (9/((p:ℝ)-1))*classWeight J Y S r := by
  classical
  have qp : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  let : NeZero (q*p) := ⟨Nat.ne_of_gt (Nat.mul_pos qp pp.pos)⟩
  obtain ⟨c,crt⟩ := extra_reduced_class cop r s
  have eq : classPart J Y S r (fun n => (s:ZMod p)=(n:ZMod p))=classWeight J Y S c := by
    apply Complex.ofReal_injective
    rw [coe_classPart,coe_classWeight]
    exact crt ..
  rw [eq,classWeight_coprime J pr Y S c]
  let K := J\(q*p).primeFactors
  have pq : 0 < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast pp.one_lt)
  have tot : ((q*p).totient:ℝ)=(q.totient:ℝ)*((p:ℝ)-1) := by
    rw [Nat.totient_mul cop,Nat.totient_prime pp,Nat.cast_mul,Nat.cast_sub pp.one_le,Nat.cast_one]
  have up := ((extra c).2).trans (mul_le_mul_of_nonneg_left (gaussianMass_monotone pr (K:=K) Finset.sdiff_subset Y S sp) (by norm_num))
  rw [tot] at up
  have low := (main r).1
  have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr qp
  rw [div_mul_eq_mul_div,le_div_iff₀ pq]
  apply (mul_le_mul_iff_right₀ tp).mp
  nlinarith only [up,low]

/-- A zero exceptional class has relative mass at most nine times the
    actual tilted-window divisibility probability for its prime. -/
theorem zero_extra_class_cost {q : ℕ} [NeZero q] (J : Finset ℕ) (pr : ∀ t∈J, t.Prime)
    (p : ℕ) (mem : p∈J) (cop : p.Coprime q) (Y S : ℝ) (sp : 0<S) (r : (ZMod q)ˣ)
    (main : classBalanced J q Y S) (extra : classBalanced (J.erase p) q (Y/p) (S/p))
    (probBound : ℝ) (pb : 0≤probBound) (rate : divisorGaussian J p Y S ≤ probBound*gaussianMass J Y S) :
    classPart J Y S r (p ∣ ·) ≤ (9*probBound)*classWeight J Y S r := by
  let c := r/ZMod.unitOfCoprime p cop
  have eq : classPart J Y S r (p∣·)=1/(p:ℝ)*classWeight (J.erase p) (Y/p) (S/p) c := by
    apply Complex.ofReal_injective
    rw [coe_classPart,Complex.ofReal_mul,coe_classWeight]
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast] using marked_prime_classMass J pr p mem cop r Y S sp
  have upper := (extra c).2
  have lo := (main r).1
  have step := divisorGaussian_insert J pr p 1 mem Y S sp
  rw [Nat.mul_one,divisorGaussian_one] at step
  rw [step] at rate
  have pp : 0<(p:ℝ) := by exact_mod_cast (pr p mem).pos
  have tp : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [eq]
  apply (mul_le_mul_iff_right₀ tp).mp
  nlinarith only [mul_le_mul_of_nonneg_left upper (show 0≤1/(p:ℝ) by positivity),
    mul_le_mul_of_nonneg_left lo pb,rate]

end Cogentic.Window

namespace Cogentic.Construction
open Real Cogentic.Window

/-- Every actual surviving class on the executable polynomial conductor
    range has mass within a factor three of the true average class mass. -/
theorem constructed_classes_balanced (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ {n ell forced q₀ q : ℕ} {Y S : ℝ},
    let b := n.log2+1
    let J := (sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)
    n₀ ≤ b → 2 ≤ n → ¬n.Prime → ell ∈ dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    0<forced → forced ≤ (Fixed.B b)^3 → 0<q → q∣q₀ → 0<q₀ → q₀≤conductorCap n →
    InWindow b Y S → classBalanced J q Y S := by
  obtain ⟨C,cp,n₁,model⟩ := constructed_class_relative line 1 le_rfl
  obtain ⟨n₂,small⟩ := fixed_class_accuracy C
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ (max n₂ n₃),?_⟩
  intro n ell forced q₀ q Y S b J big hn comp target absent pf fc qp div q₀p cap win
  let : NeZero q := ⟨qp.ne'⟩
  obtain ⟨one,g⟩ := max_le_iff.mp big
  obtain ⟨two,three⟩ := max_le_iff.mp g
  let H := log (Fixed.B b)
  let u := log Y/H
  have db := deg b three
  have hH : 0<H := by
    have L := (fixed_band_log_bounds b (Nat.succ_pos _) (by omega)).1
    have d : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast db
    change 1000*(Fixed.d b:ℝ) ≤ H at L
    linarith only [d,L]
  have eq : H*u=log Y := by dsimp [u]; field_simp
  have shift : |H*u-log Y|≤2*H := by rw [eq,sub_self,abs_zero]; positivity
  obtain ⟨α,ha,mean,mp,cl⟩ := model one hn comp target absent pf fc qp div q₀p cap win
    win.2.2.1 win.2.2.2.1 shift
  let F := Y^(α-1)*eulerMass J α
  let M := omittedMass (primeBand b) (primeBand b\J) (primeProbability α) (fun p=>log p) H (H*u-log Y)
  let T := ((q:ℝ)/q.totient)*F*M
  let W := 2*π*(q:ℝ)
  have yp : 0<Y := zero_lt_one.trans_le win.2.1
  have Fp : 0<F := mul_pos (rpow_pos_of_pos yp _) (eulerMass_pos _ _)
  have Tp : 0<T := mul_pos (mul_pos (div_pos (by exact_mod_cast qp) (by exact_mod_cast Nat.totient_pos.mpr qp)) Fp) mp
  have Wp : 0<W := mul_pos (by positivity) (by exact_mod_cast qp)
  have eps := small b two
  have pr (p : ℕ) (mem : p∈J) : p.Prime :=
    (mem_primeBand.mp (Finset.mem_filter.mp (Finset.mem_filter.mp mem).1).1).1
  have cop (x : ℕ) (mem : x∈squarefreeSupport J) : x.Coprime q := by
    obtain ⟨sf,fac⟩ := (mem_squarefreeSupport J pr x).mp mem
    apply Nat.coprime_of_dvd
    intro p pp xp qd
    exact (Finset.mem_filter.mp (fac (Nat.mem_primeFactors.mpr ⟨pp,xp,sf.ne_zero⟩))).2 (qd.trans div)
  apply classBalanced_of_uniform J Y S ((T/2)/W) cop
  intro r
  have raw := cl r
  change ‖(2*π:ℝ) • ((q:ℂ)*classMass (squarefreeSupport J) (fun t => (gaussian Y S t:ℂ)) r)
    -(T:ℂ)‖ ≤ C*T*exp (-1*(Fixed.z b:ℝ)^2) at raw
  rw [←coe_classWeight] at raw
  have cast : (2*π:ℝ) • ((q:ℂ)*(classWeight J Y S r:ℂ))-(T:ℂ)=
      ((W*classWeight J Y S r-T:ℝ):ℂ) := by simp [W,Complex.real_smul]; ring
  rw [cast,Complex.norm_real,Real.norm_eq_abs] at raw
  have z := mul_le_mul_of_nonneg_left eps Tp.le
  have bnd : |W*classWeight J Y S r-T| ≤ T/2 := raw.trans (by simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using z)
  obtain ⟨l,h⟩ := abs_le.mp bnd
  constructor
  · exact (div_le_iff₀ Wp).mpr (by linarith)
  · rw [←mul_div_assoc,le_div_iff₀ Wp]; linarith

end Cogentic.Construction
