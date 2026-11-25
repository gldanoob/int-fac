import Cogentic.PolynomialEvents

namespace Cogentic.Construction
open Real Cogentic.Window

theorem horner_eval_int (x : ℤ) (f : List ℤ) : (Marking.horner x f).1=eval x f := by
  induction f with
  | nil => rfl
  | cons c cs ih => simp only [Marking.horner,eval,ih,Int.cast_id]

/-- Inside the actual finite search box the signed affine extension agrees
    exactly with the absolute integer value accepted by Step 1. -/
theorem signed_box_value_size {n ell a u v : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) (side : Bool) :
    let p := construct n ell u v u v; let f := if side then p.second else p.first
    markSign n a side*affineValue n ell a side ((u:ℤ)+a*v)=(Marking.value f a:ℤ) ∧
      Fixed.A (n.log2+1)<Marking.value f a := by
  let b := n.log2+1; let A := Fixed.A b; let d := Fixed.d b; let h := Fixed.h b
  let amp : ℚ := leadingCoefficient n*(A:ℚ)^d; let y := affineValue n ell a side ((u:ℤ)+a*v)
  let p := construct n ell u v u v; let f := if side then p.second else p.first
  have ap : 0<A := Nat.pow_pos (by decide)
  have amp₀ : 0≤amp := by dsimp [amp]; positivity
  have eq : eval (a:ℤ) f=y := by
    have ⟨one,two⟩ := affine_at_constructed (ell := ell) (by omega : 3≤Fixed.d (n.log2+1)) a u v u v
    cases side <;> assumption
  have val : (Marking.value f a:ℤ)=|y| := by
    unfold Marking.value
    rw [horner_eval_int,eq,Int.natCast_natAbs]
  have err := normalized_error hn big target side box ((a:ℚ)/A)
    (by rw [abs_of_nonneg (by positivity)]; exact (div_le_one (by exact_mod_cast ap)).mpr (by exact_mod_cast cap))
  have raw : |(y:ℚ)-amp*idealAt n a side|≤amp/(Fixed.K₁ b) := by
    have shape : f=perturb (primorial d*ell) (Fixed.rootBase n) u v
        (corrected n (Fixed.rootBase n) (primorial d*ell) (leadingCoefficient n)
          (preliminary d A (Fixed.rootBase n) (primorial d) ell (leadingCoefficient n) side)) := by
      cases side <;> rfl
    rw [←eq,←normalized_at_mark ap a f,shape]; exact err
  have size := (grid_ideal_value hn big cap grid side).1
  change (1/2:ℚ)^(4*h) ≤ |idealAt n a side| at size
  have width : (1:ℚ)/(Fixed.K₁ b) ≤ (1/2:ℚ)^(4*h) := by
    change 1/((2^(100*h):ℕ):ℚ)≤_
    rw [Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have sign := mul_le_mul_of_nonneg_left (width.trans size) amp₀
  rw [←mul_div_assoc,mul_one] at sign
  have hp : 0<h := Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _)
  have kp : (0:ℚ)<Fixed.K₁ b := by dsimp only [Fixed.K₁]; positivity
  have gap : (2:ℚ)/(Fixed.K₁ b) ≤ |idealAt n a side| := by
    apply le_trans _ size
    rw [div_pow,one_pow]
    apply (div_le_div_iff₀ kp (by positivity)).mpr
    simpa only [one_mul] using (show (2:ℚ)*2^(4*h) ≤ Fixed.K₁ b by
      exact_mod_cast (show 2*2^(4*h) ≤ Fixed.K₁ b by
        change 2^1*2^(4*h)≤2^(100*h)
        rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)))
  have half := Nat.div_pos (Nat.le_of_dvd (primorial_pos d)
    (Nat.prime_two.dvd_primorial_iff.mpr (show 2≤d by dsimp only [d,b]; omega))) (by decide)
  have lead : 1≤leadingCoefficient n := Nat.mul_pos half (Nat.pow_pos (by decide))
  have KA : Fixed.K₁ b<A := Nat.pow_lt_pow_right (by decide : 1<2) (by change 100*h<10000*h; omega)
  have bigAmp : (A:ℚ)*(Fixed.K₁ b:ℚ) < amp := by
    have apow := Nat.pow_le_pow_right ap (show 2≤d by dsimp only [d,b]; omega)
    have sq : A*Fixed.K₁ b < leadingCoefficient n*A^d := calc
      _ < A*A := Nat.mul_lt_mul_of_pos_left KA ap
      _ ≤ A^d := by simpa only [pow_two] using apow
      _ ≤ _ := Nat.le_mul_of_pos_left _ lead
    dsimp only [amp]; exact_mod_cast sq
  have g := mul_le_mul_of_nonneg_left gap amp₀
  rw [←abs_of_nonneg amp₀,←abs_mul] at g
  rw [abs_of_nonneg amp₀,show amp*(2/(Fixed.K₁ b:ℚ))=2*(amp/(Fixed.K₁ b)) by ring] at g
  have tri := abs_sub_abs_le_abs_sub (amp*idealAt n a side) (y:ℚ)
  rw [abs_sub_comm] at tri
  have valQ := congrArg (fun k : ℤ => (k:ℚ)) val
  push_cast at valQ
  have bigger : (A:ℚ)<(Marking.value f a:ℚ) := by
    rw [valQ]
    have below := (lt_div_iff₀ kp).mpr bigAmp
    linarith only [raw,tri,g,below]
  refine ⟨?_,by exact_mod_cast bigger⟩
  change markSign n a side*y=(Marking.value f a:ℤ)
  rw [val]
  unfold markSign
  split
  next neg =>
    rw [abs_of_neg neg] at sign
    have yn : (y:ℚ)≤0 := by linarith [(abs_le.mp raw).2]
    rw [neg_one_mul,abs_of_nonpos (by exact_mod_cast yn)]
  next pos =>
    rw [abs_of_nonneg (le_of_not_gt pos)] at sign
    have yn : 0≤(y:ℚ) := by linarith [(abs_le.mp raw).1]
    rw [one_mul,abs_of_nonneg (by exact_mod_cast yn)]

theorem signed_box_value {n ell a u v : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) (side : Bool) :
    let p := construct n ell u v u v; let f := if side then p.second else p.first
    markSign n a side*affineValue n ell a side ((u:ℤ)+a*v)=(Marking.value f a:ℤ) := by
  exact (signed_box_value_size hn big target cap grid box side).1

/-- A band prime of a surviving input passes the additional leading-
    coefficient and input-modulus filters used by the executable marker. -/
theorem sieveBand_executable {n ell : ℕ} (hn : 2≤n) (big : 3≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (u v w z : ℕ) :
    sieveBand n ell 1 = (TryPair.fixedInput n ell (construct n ell u v w z)).base.toFinset := by
  let b := n.log2+1; let d := Fixed.d b; let P := primorial d; let B := Fixed.B b
  ext q
  have base := sieveBand_base n ell u v w z
  rw [List.mem_toFinset,Marking.mem_base]
  constructor
  · intro mem
    have ⟨pr,high,low⟩ := mem_primeBand.mp (Finset.mem_filter.mp mem).1
    have raw := base ▸ mem
    have dx := (Fixed.degree_le_bits b).trans (dyadic_data (b := b) (Nat.succ_pos _)).2.1
    have xp : 0<dyadicUnit b := Nat.pow_pos (by decide)
    have dd : d^2 ≤ B := by dsimp only [B]; rw [(dyadic_data (b := b) (Nat.succ_pos _)).2.2.2.1]; exact (Nat.pow_le_pow_left dx 2).trans (Nat.pow_le_pow_right xp (by decide))
    have dq : d<q := by by_contra! bad; exact low.not_ge ((Nat.pow_le_pow_left bad 2).trans dd)
    have copP : q.Coprime P := pr.coprime_iff_not_dvd.mpr (fun h => dq.not_ge (pr.dvd_primorial_iff.mp h))
    have three : q.Coprime 3 := (Nat.coprime_primes pr Nat.prime_three).mpr (by change 3≤d at big; omega)
    have two : 2∣P := Nat.prime_two.dvd_primorial_iff.mpr (by change 3≤d at big; omega)
    have lead : q.Coprime (leadingCoefficient n) := Nat.coprime_mul_iff_right.mpr
      ⟨copP.of_dvd_right (Nat.div_dvd_of_dvd two),three.pow_right _⟩
    have copn : q.Coprime n := pr.coprime_iff_not_dvd.mpr (fun h => by
      have proper : TwoThirdsSearch.ProperDivisor n q := ⟨pr.one_lt,
        lt_of_le_of_ne (Nat.le_of_dvd (by omega) h) (fun eq => comp (eq ▸ pr)),h⟩
      have bc : B ≤ indexCap b (Fixed.beta b) := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0<2))
      exact presieve_hits proper (high.trans bc) none)
    exact ⟨List.mem_toFinset.mp raw,pr,high,Nat.coprime_mul_iff_right.mpr ⟨lead,copn⟩⟩
  · intro mem
    rw [base]; exact List.mem_toFinset.mpr mem.1

theorem PrescribedRows.prefactor_supported {n ell a : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (target : ell∈sieveBand n ell 1) : R.prefactor a side∈squarefreeSupport (sieveBand n ell 1) := by
  classical
  let Q := R.hit a
  have sub : Q⊆sieveBand n ell 1 := (Finset.filter_subset _ _).trans R.member
  have miss : ell∉Q := fun h => R.excluded (Finset.mem_filter.mp h).1
  unfold PrescribedRows.prefactor targetPart
  split
  · refine Finset.mem_image.mpr ⟨insert ell Q,Finset.mem_powerset.mpr (Finset.insert_subset target sub),?_⟩
    rw [Finset.prod_insert miss]; rfl
  · refine Finset.mem_image.mpr ⟨Q,Finset.mem_powerset.mpr sub,?_⟩; simp [Q,PrescribedRows.hitProduct,prodPrimes]

/-- Dividing a full smooth value by the prescribed factor removes exactly
    its prime factors from the squarefree factor base. -/
theorem prescribed_smooth_iff {n ell z pre : ℕ} (positive : 0<pre) (dvd : pre∣z)
    (sf : pre∈squarefreeSupport (sieveBand n ell 1)) :
    z∈squarefreeSupport (sieveBand n ell 1) ↔ z/pre∈squarefreeSupport (sieveBand n ell pre) := by
  let J := sieveBand n ell 1; let K := sieveBand n ell pre
  have prime (p : ℕ) (h : p∈J) := (mem_primeBand.mp (Finset.mem_filter.mp h).1).1
  have prime' (p : ℕ) (h : p∈K) := (mem_primeBand.mp (Finset.mem_filter.mp h).1).1
  have valid : (fun p => p∈J ∧ ¬p∣pre)=(fun p => p∈K) := by
    funext p
    by_cases base : p∈primeBand (n.log2+1)
    · have pr := (mem_primeBand.mp base).1
      simp [J,K,sieveBand,base,pr.ne_one]
    · simp [J,K,sieveBand,base]
  change pre∈squarefreeSupport J at sf
  have law := TwoThirdsWindow.divide_squarefree_class (fun p => p∈J) z 0 pre positive
  simp only [Nat.gcd_zero_left,Nat.div_self positive,Nat.mod_one,Nat.zero_mod,Nat.zero_div,
    Nat.mod_eq_zero_of_dvd dvd,dvd,true_and,valid,supported_iff_euler J prime,supported_iff_euler K prime',sf] at law
  exact law

/-- The signed event in the probability calculation is precisely the
    marker's full squarefree-smooth predicate on finite-box coefficients. -/
theorem PrescribedRows.box_smooth_iff {n ell a u v : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (none : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=Option.none)
    (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b) (side : Bool)
    (ok : R.compatible side u v) :
    let inp := TryPair.fixedInput n ell (construct n ell u v u v)
    supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side u v) ↔
      Marking.SquarefreeSmooth inp.base (Marking.value (inp.coeffs side) a) := by
  let inp := TryPair.fixedInput n ell (construct n ell u v u v)
  let z := Marking.value (inp.coeffs side) a; let pre := R.prefactor a side
  let J := sieveBand n ell 1
  have pg (p : ℕ) (h : p∈J) := (mem_primeBand.mp (Finset.mem_filter.mp h).1).1
  have full := sieveBand_executable (ell := ell) hn (by omega) comp none u v u v
  have complete : z∈squarefreeSupport J ↔ Marking.SquarefreeSmooth inp.base z := by
    rw [mem_squarefreeSupport J pg]
    constructor
    · rintro ⟨sz,sub⟩; refine ⟨sz.ne_zero,sz,fun p pp dvd => ?_⟩
      have mem := sub (Nat.mem_primeFactors.mpr ⟨pp,dvd,sz.ne_zero⟩)
      change p∈sieveBand n ell 1 at mem
      rw [full] at mem; exact List.mem_toFinset.mp mem
    · rintro ⟨nz,sz,sub⟩; refine ⟨sz,fun p hp => ?_⟩
      rw [show J=sieveBand n ell 1 from rfl,full,List.mem_toFinset]
      exact sub p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have et : ell∈J := by rw [show J=sieveBand n ell 1 from rfl,full,List.mem_toFinset]; exact target_in_base hn (by omega) comp target none u v u v
  have sign := signed_box_value hn big target cap grid box side
  change markSign n a side*affineValue n ell a side ((u:ℤ)+a*v)=(z:ℤ) at sign
  have div := dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) (markSign n a side)
  rw [sign] at div
  have ds : pre∣z := Int.natCast_dvd_natCast.mp div
  have eq : R.intercept a side u v=((z/pre:ℕ):ℤ) := by unfold PrescribedRows.intercept; rw [sign,Int.natCast_ediv]
  change supportedValue (sieveBand n ell pre) (R.intercept a side u v) ↔ _
  rw [eq]
  have criterion := prescribed_smooth_iff (R.pre_bounds target a side).1 ds (R.prefactor_supported side et)
  simpa only [supportedValue,Finset.mem_image,Int.natCast_inj,exists_eq_right] using criterion.symm.trans complete

end Cogentic.Construction

#print axioms Cogentic.Construction.signed_box_value
#print axioms Cogentic.Construction.sieveBand_executable
#print axioms Cogentic.Construction.prescribed_smooth_iff

#print axioms Cogentic.Construction.PrescribedRows.box_smooth_iff
