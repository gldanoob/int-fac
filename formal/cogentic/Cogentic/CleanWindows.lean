import Cogentic.GaussianMeans
import Cogentic.MarkDensity
import Cogentic.PrincipalResidue
import Cogentic.GaussianClass

namespace Cogentic.Construction
open Real
open Cogentic.Window

noncomputable def primeBand (b : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.sqrt (Fixed.B b)⌋₊ (Fixed.B b)).filter Nat.Prime

theorem mem_primeBand {q b : ℕ} :
    q ∈ primeBand b ↔ q.Prime ∧ q ≤ Fixed.B b ∧ Fixed.B b < q^2 := by
  simp only [primeBand,Finset.mem_filter,Finset.mem_Ioc]
  have sqrtLt : ⌊Real.sqrt (Fixed.B b)⌋₊ < q ↔ Fixed.B b < q^2 := by
    rw [Nat.floor_lt (Real.sqrt_nonneg _),Real.sqrt_lt (Nat.cast_nonneg (α := ℝ) _) (Nat.cast_nonneg (α := ℝ) q)]
    exact_mod_cast Iff.rfl
  rw [sqrtLt]; tauto

/-- Primes removed from the construction's band after the two cofactor
    tests and removal of forced or already-used prime factors. -/
noncomputable def sieveBand (n ell forced : ℕ) : Finset ℕ :=
  (primeBand (n.log2+1)).filter (fun q => ¬q ∣ markModulus n ell ∧ ¬q ∣ forced)

theorem sieveBand_base (n ell u₀ u₁ v₀ v₁ : ℕ) :
    sieveBand n ell 1 = (construct n ell u₀ u₁ v₀ v₁).factorBase.toFinset := by
  ext q
  rw [sieveBand,Finset.mem_filter,mem_primeBand,List.mem_toFinset,constructed_factorBase_iff]
  constructor
  · rintro ⟨⟨pr,hi,lo⟩,exc,_⟩; exact ⟨pr,hi,lo,exc⟩
  · rintro ⟨pr,hi,lo,exc⟩; exact ⟨⟨pr,hi,lo⟩,exc,pr.not_dvd_one⟩

def firstModulus (n ell a : ℕ) (targetHit : Bool) : ℕ :=
  primorial (Fixed.d (n.log2+1))*(if targetHit then 1 else ell)*(Fixed.rootBase n-a)

def secondModulus (n ell a a' : ℕ) (targetHit : Bool) (both free : ℕ) : ℕ :=
  firstModulus n ell a' targetHit*((a'.dist a)/both)*free

/-- A uniform envelope for both conductors and the extra primes used to
    exclude a bad class in the first projection. -/
def conductorCap (n : ℕ) : ℕ :=
  let b := n.log2+1
  primorial (Fixed.d b)*Fixed.rootBase n*Fixed.A b*(Fixed.B b)^10

theorem actual_conductor_caps {n ell a a' both free aux : ℕ}
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (cap : a ≤ Fixed.A (n.log2+1)) (cap' : a' ≤ Fixed.A (n.log2+1))
    (cf : free ≤ (Fixed.B (n.log2+1))^2) (extra : aux ≤ (Fixed.B (n.log2+1))^7)
    (targetHit : Bool) :
    firstModulus n ell a targetHit*aux ≤ conductorCap n ∧
      secondModulus n ell a a' targetHit both free*aux ≤ conductorCap n := by
  let b := n.log2+1; let B := Fixed.B b; let A := Fixed.A b; let P := primorial (Fixed.d b)
  let m := Fixed.rootBase n
  have bp : 0<B := Nat.pow_pos (by decide)
  have ap : 0<A := Nat.pow_pos (by decide)
  have ep : ell ≤ B := (mem_dyadicTargets.mp target).2.2
  have f (z : ℕ) : firstModulus n ell z targetHit ≤ P*m*B := by
    unfold firstModulus
    have lim : (if targetHit then 1 else ell) ≤ B := by split <;> omega
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ lim) (Nat.sub_le m z)).trans_eq (by ring)
  have diff : (a'.dist a)/both ≤ A := by
    apply (Nat.div_le_self _ _).trans
    rw [Nat.dist_eq_max_sub_min]; exact (Nat.sub_le ..).trans (max_le (show a' ≤ A from cap') cap)
  have B8 : B^8 ≤ B^10 := Nat.pow_le_pow_right bp (by decide)
  have s : firstModulus n ell a targetHit*aux ≤ P*m*B^8 := by
    apply (Nat.mul_le_mul (f a) extra).trans_eq
    rw [show B^8 = B*B^7 by ring]; ring
  constructor
  · calc _ ≤ P*m*B^8 := s
         _ ≤ P*m*A*B^10 := Nat.mul_le_mul (Nat.le_mul_of_pos_right _ ap) B8
  · change firstModulus n ell a' targetHit*((a'.dist a)/both)*free*aux ≤ P*m*A*B^10
    apply (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (f a') diff) cf) extra).trans_eq
    ring

private theorem cap_size {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1; let d := Fixed.d b; let x := dyadicUnit b
    conductorCap n ≤ x^(12*d) := by
  let b := n.log2+1; let d := Fixed.d b; let x := dyadicUnit b
  have ⟨x2,_,_,B,A,_,m⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have dh : d ≤ Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have P : primorial d ≤ x^2 := by
    apply (primorial_le_four_pow _).trans
    change (2^2)^d ≤ (2^Fixed.h b)^2
    rw [←Nat.pow_mul,←Nat.pow_mul,Nat.mul_comm (Fixed.h b) 2]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ dh)
  have cap := Nat.mul_le_mul_right ((Fixed.B b)^10) (Nat.mul_le_mul_right (Fixed.A b)
    (Nat.mul_le_mul P ((rootBase_bound hn).trans_eq m)))
  apply cap.trans
  rw [A,B,←Nat.pow_mul,←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
  apply Nat.pow_le_pow_right (by omega)
  change 2+8*d+10000+1000*10 ≤ 12*d
  change 10004 ≤ d at big; omega

private theorem sf_count {v b : ℕ} (vp : 0 < v) (width : v ≤ 2^b) : v.primeFactors.card ≤ b := by
  have rad : 2^v.primeFactors.card ≤ v := by
    calc _ = ∏ _q ∈ v.primeFactors, 2 := by simp
         _ ≤ ∏ q ∈ v.primeFactors, q := Finset.prod_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)
         _ ≤ v := Nat.le_of_dvd vp (Nat.prod_primeFactors_dvd _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (rad.trans width)

theorem omitted_card {n ell forced q₀ : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none)
    (pf : 0 < forced) (ff : forced ≤ (Fixed.B (n.log2+1))^3) (pq : 0 < q₀) (cq : q₀ ≤ conductorCap n) :
    let b := n.log2+1
    let J := (sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)
    ((primeBand b) \ J).card ≤ b^3 := by
  let b := n.log2+1; let d := Fixed.d b; let v := Fixed.v b; let h := Fixed.h b
  let k := markModulus n ell
  have ⟨kp,kcap,_,_⟩ := markModulus_spec hn big composite target none
  have kc := mark_factor_count hn kp kcap
  have qcap := cq.trans (cap_size hn big)
  have qcount : q₀.primeFactors.card ≤ 12*v := by
    apply sf_count pq
    change q₀ ≤ 2^(12*(d*h))
    calc q₀ ≤ (2^h)^(12*d) := qcap
         _ = _ := by rw [←Nat.pow_mul]; congr 1; ring
  have fcount : forced.primeFactors.card ≤ 3000*h := by
    apply sf_count pf
    apply ff.trans_eq
    change (2^(1000*h))^3 = _; rw [←Nat.pow_mul]; congr 1; ring
  have missing : (primeBand b) \ ((sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)) ⊆
      (k.primeFactors ∪ forced.primeFactors) ∪ q₀.primeFactors := by
    intro p hp
    obtain ⟨band,exc⟩ := Finset.mem_sdiff.mp hp
    have prime := (mem_primeBand.mp band).1
    by_cases qk : p ∣ k
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨prime,qk,kp.ne'⟩))
    by_cases qf : p ∣ forced
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨prime,qf,pf.ne'⟩))
    by_cases qq : p ∣ q₀
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨prime,qq,pq.ne'⟩)
    exact (exc (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨band,qk,qf⟩,qq⟩)).elim
  let S := (k.primeFactors ∪ forced.primeFactors)
  have cardinal := (Finset.card_le_card missing).trans ((Finset.card_union_le S q₀.primeFactors).trans
    (Nat.add_le_add_right (Finset.card_union_le k.primeFactors forced.primeFactors) _))
  have dp := Fixed.degree_pos (b := b) (Nat.succ_pos _)
  have vp : v ≤ b := by
    apply le_trans ?_ (Fixed.degree_floor b).1
    change d*(d*Fixed.z b) ≤ d^3*Fixed.z b
    apply (show d*(d*Fixed.z b) = d^2*Fixed.z b by ring).le.trans
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right dp (by decide))
  have hv : h ≤ v := Nat.le_mul_of_pos_left _ dp
  have bb : 10004 ≤ b := big.trans (Fixed.degree_le_bits b)
  have square := Nat.pow_le_pow_left bb 2
  have cube : 300000*b ≤ b^3 := by
    calc _ ≤ b^2*b := Nat.mul_le_mul_right _ (by omega)
         _ = _ := by ring
  change _ ≤ b^3
  exact cardinal.trans ((show k.primeFactors.card+forced.primeFactors.card+q₀.primeFactors.card ≤ 300000*b by
    change k.primeFactors.card ≤ 2+222240*v at kc; omega).trans cube)

private theorem clean_guards {n q Y₀ : ℕ} {Y S : ℝ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (pq : 0 < q) (cq : q ≤ conductorCap n) (om : Y₀ ≤ (n.log2+1)^3) (window : InWindow (n.log2+1) Y S) :
    let B : ℝ := Fixed.B (n.log2+1)
    4 ≤ B ∧ S ≤ Y ∧ 404 ≤ B^(3/200:ℝ) ∧ 1+Real.log (3*q*B) ≤ B^(1/100:ℝ) ∧
      (Y₀:ℝ) ≤ B^(1/100:ℝ) ∧ (q:ℝ) ≤ Y^(1/1000:ℝ) := by
  let b := n.log2+1; let d := Fixed.d b; let x : ℝ := dyadicUnit b; let B : ℝ := Fixed.B b
  have ⟨xx,bx,_,Bpow,_,_,_⟩ := dyadic_data (b := b) (Nat.succ_pos _)
  have dg : 10004 ≤ d := big
  have dx : d ≤ dyadicUnit b := (Fixed.degree_le_bits b).trans bx
  have dr : (d:ℝ) ≤ x := by dsimp [x]; exact_mod_cast dx
  have bR : (b:ℝ) ≤ x := by dsimp [x]; exact_mod_cast bx
  have xhi : (10004:ℝ) ≤ x := by dsimp [x]; exact_mod_cast dg.trans dx
  have xp : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have Bp : B = x^1000 := by dsimp [B,x]; exact_mod_cast Bpow
  have Bhi : 4 ≤ B := by
    rw [Bp]; exact (by linarith : (4:ℝ)≤x).trans (le_self_pow₀ x1 (by decide))
  have logB := Real.log_pos (by linarith : 1<B)
  have qpos : 0 < (q:ℝ) := by exact_mod_cast pq
  have qc : (q:ℝ) ≤ x^(12*d) := by dsimp [x]; exact_mod_cast cq.trans (cap_size hn big)
  have logQ := Real.log_le_log qpos qc
  rw [Real.log_pow] at logQ
  push_cast at logQ
  have lp : 0 ≤ Real.log x := Real.log_nonneg x1
  have lx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos xp).trans (by linarith)
  have lB : Real.log B = 1000*Real.log x := by rw [Bp,Real.log_pow]; norm_num
  have powers (α : ℝ) (j : ℕ) (eq : 1000*α=j) : B^α=x^j := by
    rw [Bp,←Real.rpow_natCast,←Real.rpow_mul xp.le,←Real.rpow_natCast x j]
    exact congrArg (x^·) (by exact_mod_cast eq)
  have pow10 := powers (1/100) 10 (by norm_num)
  have pow15 := powers (3/200) 15 (by norm_num)
  have ⟨sp,Y1,ulo,_,rlo,_,_⟩ := window
  have sy : S ≤ Y := (one_le_div sp).mp ((Real.one_le_rpow (by linarith : 1≤B) (by norm_num)).trans rlo)
  have cy : (q:ℝ) ≤ Y^(1/1000:ℝ) := by
    apply (Real.le_rpow_iff_log_le qpos (zero_lt_one.trans_le Y1)).mpr
    have u := (le_div_iff₀ logB).mp ulo
    rw [lB] at u
    change _ ≤ Real.log Y at u
    nlinarith only [u,logQ,mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) lp]
  have logs : 1+Real.log (3*q*B) ≤ x^10 := by
    rw [Real.log_mul (by positivity) (by linarith : B≠0),Real.log_mul (by norm_num) qpos.ne',lB]
    have r : (12:ℝ)*d+1000 ≤ 13*x := by linarith
    have est := mul_le_mul r lx lp (by positivity : 0≤13*x)
    have log3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    have x2 : 13*x^2+3 ≤ x^3 := by
      have an := mul_le_mul_of_nonneg_right (show 16 ≤ x by linarith) (sq_nonneg x)
      nlinarith [one_le_pow₀ (n := 2) x1]
    have ten : x^3 ≤ x^10 := pow_le_pow_right₀ x1 (by decide)
    nlinarith only [log3,logQ,est,x2,ten]
  have count : (Y₀:ℝ) ≤ x^10 := by
    have o : (Y₀:ℝ) ≤ (b:ℝ)^3 := by exact_mod_cast om
    exact o.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) bR 3).trans (pow_le_pow_right₀ x1 (by decide)))
  exact ⟨Bhi,sy,pow15 ▸ (show 404 ≤ x^15 from (by linarith : (404:ℝ)≤x).trans (le_self_pow₀ x1 (by decide))),
    pow10 ▸ logs,pow10 ▸ count,cy⟩

/-- Discrepancy of a character class from its principal contribution on
    the actual squarefree support, after removing the prescribed factors,
    the cofactor primes, and primes in the unreduced scalar step. -/
def Discrepancy (J : Finset ℕ) (q : ℕ) (r : (ZMod q)ˣ) (Y S C : ℝ) : Prop :=
  ‖(q:ℂ)*classMass (squarefreeSupport J) (fun t => (gaussian Y S t:ℂ)) r -
     ((q:ℂ)/q.totient)*(gaussianMass (J \ q.primeFactors) Y S:ℂ)‖ ≤ C*Y^(-3/1000:ℝ)

theorem clean_window_discrepancy (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n ell forced q₀ q : ℕ} {Y S : ℝ},
      2 ≤ n → 10004 ≤ Fixed.d (n.log2+1) → ¬n.Prime → ell ∈ dyadicTargets (Fixed.beta (n.log2+1)) →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none →
      0 < forced → forced ≤ (Fixed.B (n.log2+1))^3 → 0 < q → q ≤ q₀ → q₀ ≤ conductorCap n →
      InWindow (n.log2+1) Y S → ∀ r : (ZMod q)ˣ,
        Discrepancy ((sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)) q r Y S C := by
  obtain ⟨C,pos,main⟩ := clean_residue_saddle_input line
  refine ⟨C,pos,?_⟩
  intro n ell forced q₀ q Y S hn big comp target none pf ff pq qq cap window r
  let b := n.log2+1
  let J := (sieveBand n ell forced).filter (fun p => ¬p ∣ q₀)
  let rem := primeBand b \ J
  have card := omitted_card hn big comp target none pf ff (pq.trans_le qq) cap
  have ⟨B4,sy,Bbig,logs,limit,qy⟩ := clean_guards hn big pq (qq.trans cap) card window
  let : NeZero q := ⟨pq.ne'⟩
  have inclusion : rem ⊆ (Finset.Ioc ⌊Real.sqrt (Fixed.B b)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime := by
    simpa only [rem,primeBand,Nat.floor_natCast] using (Finset.sdiff_subset (s := primeBand b) (t := J))
  have subset : J ⊆ primeBand b := fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have result := main q (Fixed.B b) Y S rem B4 window.1 sy window.2.1 Bbig logs limit
    window.2.2.2.2.2.1 qy window.2.2.2.2.2.2 inclusion r
  simp only [Nat.floor_natCast] at result
  change Discrepancy (primeBand b \ rem) q r Y S C at result
  change Discrepancy (primeBand b \ (primeBand b \ J)) q r Y S C at result
  rw [Finset.sdiff_sdiff_eq_self subset] at result
  exact result

end Cogentic.Construction

#print axioms Cogentic.Construction.clean_window_discrepancy
