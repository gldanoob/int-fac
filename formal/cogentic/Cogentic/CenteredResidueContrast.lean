import Cogentic.CellPairMoment
import Cogentic.PairVarianceTransfer
import Cogentic.CellAtomVariation

namespace Cogentic.Construction
open Finset Real

/-- The signed mass on a small divisor class, with its exact full-mesh drift.
The drift is common to all admissible residues of the small divisor. -/
theorem residue_class_contrast_drift (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (h q s r : ℕ),
    0<h → 0<q → h.Coprime q → q.Coprime (markModulus n ell) → h*q≤(Fixed.B b)^4 →
    (∀ p∈(markModulus n ell).primeFactors, p∣h → ¬s ≡ Fixed.rootBase n [MOD p]) →
    let L := firstCellMark b cell; let M := cellMarkCount b
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ s [MOD h])
    ∀ f g : ℕ→ℝ,
    let V := fun w : ℕ→ℝ => |w (L+(M-1))|+∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|
    let δ := (∑ j∈range M,f (L+j))-(∑ j∈range M,g (L+j))
    let ρ := ∏ p∈(markModulus n ell).primeFactors with ¬p∣h, (1-(p:ℝ)⁻¹)
    |((q:ℝ)*(∑ a∈X with a ≡ r [MOD q],f a)-(∑ a∈X,g a))-δ*(ρ/h)| ≤
      (V f+V g)*(1+2*exp 6)*((M:ℝ)/h)*exp (-K*(Fixed.z b:ℝ)^2) := by
  classical
  obtain ⟨n₀,counts⟩ := weighted_constructed_marks line K hK
  refine ⟨n₀,?_⟩
  intro n large ell target comp absent b cell h q s r hp qp cop clean cap eligible L M X f g V δ density
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  let B := Fixed.B b
  let P := (markModulus n ell).primeFactors
  let ρ (u : ℕ) := ∏ p∈P with ¬p∣u,(1-(p:ℝ)⁻¹)
  let cls (u v : ℕ) := (constructorCellMarks n ell cell).filter (fun a=>a ≡ v [MOD u])
  let t := Nat.chineseRemainder cop s r
  have hpos : 0<(h:ℝ) := by exact_mod_cast hp
  have qpos : 0<(q:ℝ) := by exact_mod_cast qp
  have nodvd (p : ℕ) (pm : p∈P) : ¬p∣q := by
    intro dvd
    exact (Nat.prime_of_mem_primeFactors pm).not_dvd_one (clean.gcd_eq_one ▸ Nat.dvd_gcd dvd (Nat.dvd_of_mem_primeFactors pm))
  have densities : ρ (h*q)=ρ h := by
    apply Finset.prod_congr _ (fun _ _=>rfl); ext p
    simp only [mem_filter]
    constructor
    · exact fun ⟨pP,no⟩=>⟨pP,fun ph=>no (dvd_mul_of_dvd_left ph _)⟩
    · exact fun ⟨pP,no⟩=>⟨pP,fun ph=>(Nat.prime_of_mem_primeFactors pP).dvd_mul.mp ph |>.elim no (nodvd p pP)⟩
  have ct : cls (h*q) t.val = X.filter (fun a=>a ≡ r [MOD q]) := by
    ext a; simp only [cls,X,mem_filter,←Nat.modEq_and_modEq_iff_modEq_mul cop]
    exact ⟨fun ⟨z,x,y⟩=>⟨⟨z,x.trans t.property.1⟩,y.trans t.property.2⟩,
      fun ⟨⟨z,x⟩,y⟩=>⟨z,x.trans t.property.1.symm,y.trans t.property.2.symm⟩⟩
  have Mlarge : B^5≤M := by
    change (2^(1000*Fixed.h b))^5≤2^(9997*Fixed.h b)
    rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have bound (u v : ℕ) (up : 0<u) (uc : u≤B^4)
      (allowed : ∀ p∈P,p∣u → ¬v ≡ Fixed.rootBase n [MOD p]) (w : ℕ → ℝ) :
      |(∑ a ∈ cls u v,w a)-(∑ j∈range M,w (L+j))*(ρ u/u)| ≤ V w*(1+2*exp 6)*((M:ℝ)/u)*e := by
    have grid := fixed_grid_interval (Fixed.degree_pos (Nat.succ_pos n.log2)) cell
    have est := counts n large ell target comp absent L M u v 0 0 0 0 (fun j=>w (L+j)) up allowed (fun a ha _=>grid a ha)
    let marks := (construct n ell 0 0 0 0).marks
    have eq : (∑ j∈range M,w (L+j)*(if L+j ≡ v [MOD u] ∧ L+j∈marks then 1 else 0))=∑ a∈cls u v,w a := by
      simp_rw [mul_ite,mul_one,mul_zero]
      have shift := sum_Ico_eq_sum_range (fun x=>if x ≡ v [MOD u] ∧ x∈marks then w x else 0) L (L+M)
      simp only [Nat.add_sub_cancel_left] at shift
      rw [←shift,←sum_filter];congr 1;ext a
      simp only [cls,constructorCellMarks,mem_filter,marks,L,M,b];tauto
    change |∑ j∈range M,w (L+j)*((if L+j ≡ v [MOD u] ∧ L+j∈marks then 1 else 0)-ρ u/u)| ≤ V w*((B+2*((M:ℝ)/u)*exp 6)*e) at est
    simp_rw [mul_sub] at est
    rw [sum_sub_distrib,eq,←sum_mul] at est
    have capB : B*u≤M := (Nat.mul_le_mul_left _ uc).trans ((by ring : B*B^4=B^5) ▸ Mlarge)
    have realCap : (B:ℝ)≤(M:ℝ)/u := (le_div_iff₀ (by exact_mod_cast up)).mpr (by exact_mod_cast capB)
    have Vpos : 0≤V w := by dsimp only [V]; positivity
    have corrected := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (add_le_add_left realCap (2*((M:ℝ)/u)*exp 6)) (le_of_lt (show 0<e from exp_pos _))) Vpos
    calc _ ≤ _ := est
         _ ≤ V w*((M/u+2*((M:ℝ)/u)*exp 6)*e) := corrected
         _ = _ := by ring
  have hsmall := (Nat.le_mul_of_pos_right h qp).trans cap
  have high := bound (h*q) t.val (Nat.mul_pos hp qp) cap (fun p pm dv=>by
    have ph := ((Nat.prime_of_mem_primeFactors pm).dvd_mul.mp dv).resolve_right (nodvd p pm)
    exact fun eq=>eligible p pm ph ((t.property.1.of_dvd ph).symm.trans eq)) f
  have low := bound h s hp hsmall eligible g
  rw [ct,densities,Nat.cast_mul] at high
  let μ := (∑ j∈range M,g (L+j))*(ρ h/h)
  let ν := (∑ j∈range M,f (L+j))*(ρ h/h)
  have scaled := mul_le_mul_of_nonneg_left high qpos.le
  rw [←abs_of_pos qpos,←abs_mul,abs_of_pos qpos] at scaled
  have cancel : (q:ℝ)*((∑ j∈range M,f (L+j))*(ρ h/((h:ℝ)*q)))=ν := by dsimp only [ν]; field_simp
  have id : (q:ℝ)*((∑ a∈X with a ≡ r [MOD q], f a) -(∑ j∈range M,f (L+j))*(ρ h/((h:ℝ)*q))) =
      (q:ℝ)*(∑ a∈X with a ≡ r [MOD q], f a)-ν := by rw [mul_sub,cancel]
  rw [id] at scaled
  change |(∑ a∈X,g a)-μ|≤_ at low
  have small := (abs_sub ((q:ℝ)*(∑ a∈X with a ≡ r [MOD q],f a)-ν) ((∑ a∈X,g a)-μ)).trans (add_le_add scaled low)
  have rearrange : ((q:ℝ)*(∑ a∈X with a ≡ r [MOD q],f a)-(∑ a∈X,g a))-δ*(density/h) =
      ((q:ℝ)*(∑ a∈X with a ≡ r [MOD q],f a)-ν)-((∑ a∈X,g a)-μ) := by dsimp only [μ,ν,δ,density,ρ,P]; ring
  rw [rearrange]
  exact small.trans_eq (by dsimp only [e]; field_simp)

/-- On a small sieve class modulo `h`, a congruence indicator of modulus `q`
may be centered before taking the pair moment. Both exact mesh weights may
vary, provided their mesh means agree. The discrepancy depends only on the
variation of the two weights, even when the indicator itself oscillates. -/
theorem centered_residue_class_mean (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (h q s r : ℕ),
    0<h → 0<q → h.Coprime q → q.Coprime (markModulus n ell) → h*q≤(Fixed.B b)^4 →
    (∀ p∈(markModulus n ell).primeFactors, p∣h → ¬s ≡ Fixed.rootBase n [MOD p]) →
    let L := firstCellMark b cell; let M := cellMarkCount b
    let X := (constructorCellMarks n ell cell).filter (fun a=>a ≡ s [MOD h])
    ∀ f g : ℕ→ℝ, (∑ j∈range M,f (L+j))=(∑ j∈range M,g (L+j)) →
    let V := fun w : ℕ→ℝ => |w (L+(M-1))|+∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|
    |(q:ℝ)*(∑ a∈X with a ≡ r [MOD q],f a)-(∑ a∈X,g a)| ≤
      (V f+V g)*(1+2*exp 6)*((M:ℝ)/h)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨n₀,estimate⟩ := residue_class_contrast_drift line K hK
  refine ⟨n₀,?_⟩
  intro n large ell target comp absent b cell h q s r hp qp cop clean cap eligible L M X f g same V
  have h := estimate n large ell target comp absent cell h q s r hp qp cop clean cap eligible f g
  dsimp only [L,M,b] at same
  simpa only [same,sub_self,zero_mul,sub_zero] using h

/-- For arbitrary cell weights and any admissible class modulo a small divisor,
the signed contrast is proportional to its *actual* pooled mass. In particular
one global zero mean suffices, even when individual cell means differ. -/
theorem pooled_residue_class_contrast {ι : Type*} (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let M := cellMarkCount b
    ∀ (S : Finset ι) (cell : ι → Option (Bool×Fin (Fixed.d b))) (q r : ι→ℕ) (t : ι→ℝ)
      (f g : ι→ℕ→ℝ) (h s : ℕ), 0<h →
    (∀ i∈S,0<q i ∧ h.Coprime (q i) ∧ (q i).Coprime (markModulus n ell) ∧ h*q i≤(Fixed.B b)^4) →
    (∀ p∈(markModulus n ell).primeFactors, p∣h → ¬s ≡ Fixed.rootBase n [MOD p]) →
    let ρ := fun u=> ∏ p∈(markModulus n ell).primeFactors with ¬p∣u, (1-(p:ℝ)⁻¹)
    let X := fun i u v=>(constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ v [MOD u])
    let A := fun i u v=> (q i:ℝ)*(∑ a∈X i u v with a ≡ r i [MOD q i], f i a)-(∑ a∈X i u v,g i a)
    let W := fun u v => ∑ i∈S,t i*A i u v
    let V := fun i (w : ℕ→ℝ) => (let L := firstCellMark b (cell i); |w (L+(M-1))|+∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|)
    |ρ 1*h*W h s-ρ h*W 1 0| ≤
      (∑ i∈S, |t i| *(V i (f i)+V i (g i)))*(ρ 1+ρ h)*(1+2*exp 6)*M*exp (-K*(Fixed.z b:ℝ)^2) := by
  classical
  obtain ⟨n₀,drift⟩ := residue_class_contrast_drift line K hK
  refine ⟨n₀,?_⟩
  intro n large ell target comp absent b M S cell q r t f g h s hp size eligible ρ X A W V
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  have rp (u : ℕ) : 0≤ρ u := by
    apply prod_nonneg; intro p pm
    have pr := Nat.prime_of_mem_primeFactors (mem_filter.mp pm).1
    have gt : (1:ℝ)≤p := by exact_mod_cast pr.one_le
    exact sub_nonneg.mpr ((inv_le_one₀ (zero_lt_one.trans_le gt)).mpr gt)
  let U := (ρ 1+ρ h)*(1+2*exp 6)*M*e
  have each (i : ι) (im : i∈S) : |ρ 1*h*A i h s-ρ h*A i 1 0|≤(V i (f i)+V i (g i))*U := by
    obtain ⟨qp,cop,clean,cap⟩ := size i im
    have basecap := (Nat.le_mul_of_pos_left (q i) hp).trans cap
    have ok1 (p : ℕ) (pm : p∈(markModulus n ell).primeFactors) (one : p∣1) : ¬0 ≡ Fixed.rootBase n [MOD p] := by
      exact ((Nat.prime_of_mem_primeFactors pm).not_dvd_one one).elim
    have rawh := drift n large ell target comp absent (cell i) h (q i) s (r i) hp qp cop clean cap eligible (f i) (g i)
    have raw1 := drift n large ell target comp absent (cell i) 1 (q i) 0 (r i) (by decide) qp (Nat.coprime_one_left _) clean
      (by simpa only [one_mul] using basecap) ok1 (f i) (g i)
    let L := firstCellMark b (cell i)
    let δ := (∑ j∈range M,f i (L+j))-(∑ j∈range M,g i (L+j))
    let D := (V i (f i)+V i (g i))*(1+2*exp 6)
    change |A i h s-δ*(ρ h/h)| ≤ D*((M:ℝ)/h)*e at rawh
    change |A i 1 0-δ*(ρ 1/(1:ℕ))| ≤ D*((M:ℝ)/(1:ℕ))*e at raw1
    simp only [Nat.cast_one,div_one] at raw1
    have hn : (0:ℝ)<h := by exact_mod_cast hp
    have rh := mul_le_mul_of_nonneg_left rawh (mul_nonneg (rp 1) hn.le)
    have r1 := mul_le_mul_of_nonneg_left raw1 (rp h)
    rw [←abs_of_nonneg (mul_nonneg (rp 1) hn.le),←abs_mul,abs_of_nonneg (mul_nonneg (rp 1) hn.le)] at rh
    rw [←abs_of_nonneg (rp h),←abs_mul,abs_of_nonneg (rp h)] at r1
    have sum := (abs_sub (ρ 1*h*(A i h s-δ*(ρ h/h))) (ρ h*(A i 1 0-δ*ρ 1))).trans (add_le_add rh r1)
    have same : ρ 1*h*(A i h s-δ*(ρ h/h))-ρ h*(A i 1 0-δ*ρ 1)=ρ 1*h*A i h s-ρ h*A i 1 0 := by
      field_simp; ring
    rw [same] at sum
    exact sum.trans_eq (by dsimp only [U,D]; field_simp)
  have cancel : ρ 1*h*W h s-ρ h*W 1 0=∑ i∈S,t i*(ρ 1*h*A i h s-ρ h*A i 1 0) := by
    dsimp only [W]; rw [mul_sum,mul_sum,←sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
  rw [cancel]
  apply (abs_sum_le_sum_abs ..).trans
  have total := sum_le_sum (s:=S) (fun i im=>mul_le_mul_of_nonneg_left (each i im) (abs_nonneg (t i)))
  simp_rw [abs_mul]
  exact total.trans_eq (by simp_rw [←mul_assoc,←sum_mul]; dsimp only [U,e]; ring)

private theorem contrast_mass {L M h q s r : ℕ} (hp : 0<h) (qp : 0<q) (cop : h.Coprime q)
    (X : Finset ℕ) (sub : X⊆Ico L (L+M)) (f g : ℕ→ℝ) (D : ℝ) (dn : 0≤D)
    (bound : ∀ a∈X, |f a|≤D ∧ |g a|≤D) :
    let w := fun a=> (if a ≡ r [MOD q] then (q:ℝ)*f a else 0)-g a
    (∑ a∈X with a ≡ s [MOD h], |w a|) ≤ D*(2*((M:ℝ)/h)+q+1) := by
  classical
  intro w
  let Y := X.filter (fun a=>a ≡ s [MOD h]); let Z := Y.filter (fun a=>a ≡ r [MOD q])
  let t := Nat.chineseRemainder cop s r
  have size (u v : ℕ) (up : 0<u) (S : Finset ℕ) (mem : ∀ a∈S, a∈X ∧ a ≡ v [MOD u]) : (S.card:ℝ)≤(M:ℝ)/u+1 := by
    have inc : S ⊆ (Ico L (L+M)).filter (fun a=>a ≡ v [MOD u]) := fun a am=>mem_filter.mpr ⟨sub (mem a am).1,(mem a am).2⟩
    have cnt := (abs_le.mp (interval_residue_error (Nat.le_add_right L M) up v)).2
    simp only [Nat.cast_add,add_sub_cancel_left] at cnt
    exact (Nat.cast_le.mpr (card_le_card inc)).trans (by linarith only [cnt])
  have yc := size h s hp Y (fun _ am=>mem_filter.mp am)
  have zc := size (h*q) t.val (Nat.mul_pos hp qp) Z (fun _ am=>by
    obtain ⟨ay,aq⟩ := mem_filter.mp am
    exact ⟨(mem_filter.mp ay).1,Nat.chineseRemainder_modEq_unique cop (mem_filter.mp ay).2 aq⟩)
  have terms := sum_le_sum (s:=Y) (fun a am=>show |w a|≤(if a ≡ r [MOD q] then (q:ℝ)*D else 0)+D by
    have limits := bound a (mem_filter.mp am).1
    apply (abs_sub ..).trans; apply add_le_add _ limits.2
    by_cases aq : a ≡ r [MOD q]
    · simp only [if_pos aq,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) q)]; exact mul_le_mul_of_nonneg_left limits.1 (Nat.cast_nonneg (α:=ℝ) q)
    · simp [aq])
  rw [sum_add_distrib,←sum_filter,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul] at terms
  change (∑ a∈Y,|w a|) ≤ (Z.card:ℝ)*(q*D)+(Y.card:ℝ)*D at terms
  refine terms.trans ((add_le_add (mul_le_mul_of_nonneg_right zc (by positivity : 0≤(q:ℝ)*D))
    (mul_le_mul_of_nonneg_right yc dn)).trans_eq ?_)
  push_cast; field_simp; ring

/-- The full squared singular series for a congruence indicator after its
exact mesh mean is subtracted. Signed class sums handle small divisors and
an interval CRT count controls the tail. -/
theorem centered_residue_pair_model (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (q r : ℕ), 0<q → q≤(Fixed.B b)^3 → q.Coprime (markModulus n ell) →
    let P := pairCorrectionPrimes b
    (∀ p∈P, p.Coprime q) → let L := firstCellMark b cell; let M := cellMarkCount b
    let X := constructorCellMarks n ell cell
    ∀ (f g : ℕ→ℝ) (D : ℝ), 0≤D → (∀ a∈X, |f a|≤D ∧ |g a|≤D) →
    (∑ j∈range M,f (L+j))=(∑ j∈range M,g (L+j)) →
    let V := fun w : ℕ→ℝ => |w (L+(M-1))|+∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|
    let w := fun a=> (if a ≡ r [MOD q] then (q:ℝ)*f a else 0)-g a
    let z := (Fixed.z b:ℝ); let e := exp (-K*z^2); let B := (Fixed.B b:ℝ)
    (∑ a∈X, ∑ y∈X,w a*w y*(pairGamma P (Fixed.rootBase n) a y)^2) ≤
      ((V f+V g)*(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ)) + 16*D^2*(M:ℝ)^2/B*exp (48*z) := by
  classical
  obtain ⟨n₁,center⟩ := centered_residue_class_mean line K hK
  obtain ⟨b₀,weight⟩ := fixed_pair_weight_sum line
  refine ⟨max n₁ (2^b₀),?_⟩
  intro n large ell target comp absent b cell q r qp cq ok P prcop L M X f g D dp bound eq V w z e B
  obtain ⟨old,two⟩ := max_le_iff.mp large
  have npos := (Nat.pow_pos (by decide : 0<2)).trans_le two
  have big : b₀≤b := ((Nat.le_log2 npos.ne').mpr two).trans (Nat.le_succ _)
  have hp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have pr (p : ℕ) (pm : p∈P) := (mem_pairCorrectionPrimes.mp pm).1
  have sizes (p : ℕ) (pm : p∈P) : Fixed.d b<p ∧ p≤Fixed.B b :=
    ⟨(mem_pairCorrectionPrimes.mp pm).2.1,(mem_pairCorrectionPrimes.mp pm).2.2.trans (Nat.pow_le_pow_right (by decide)
      (by change 200*Fixed.h b≤1000*Fixed.h b; omega))⟩
  have cop (T : Finset ℕ) (sub : T⊆P) : (sieveProduct T).Coprime q :=
    (Nat.coprime_prod_right_iff.mpr (fun p pm=>(prcop p (sub pm)).symm)).symm
  let c := (V f+V g)*(1+2*exp 6)*M*e
  have short (T : Finset ℕ) (sub : T⊆P) (low : sieveProduct T≤Fixed.B b) (s : ℕ) (ls : s<sieveProduct T)
      (good : ∀ p∈T, ¬s ≡ Fixed.rootBase n [MOD p]) : |∑ a∈X with a%(sieveProduct T)=s,w a|≤c/(sieveProduct T:ℝ) := by
    let h := sieveProduct T
    have hpos : 0<h := prod_pos (fun p h=> (pr p (sub h)).pos)
    have hq : h*q≤(Fixed.B b)^4 := (Nat.mul_le_mul low cq).trans_eq (by ring)
    have elig (p : ℕ) (pm : p∈(markModulus n ell).primeFactors) (ph : p∣h) : ¬s ≡ Fixed.rootBase n [MOD p] := by
      have pp := Nat.prime_of_mem_primeFactors pm
      obtain ⟨a,atT,pa⟩ := (pp.prime.dvd_finsetProd_iff id).mp ph
      exact good p (((Nat.prime_dvd_prime_iff_eq pp (pr a (sub atT))).mp pa) ▸ atT)
    have est := center n old ell target comp absent cell h q s r hpos qp (cop T sub) ok hq elig f g eq
    let Y := X.filter (fun a=>a ≡ s [MOD h])
    change |(q:ℝ)*(∑ a∈Y with a ≡ r [MOD q],f a)-∑ a∈Y,g a|≤_ at est
    have eqs : (X.filter (fun a=>a%(sieveProduct T)=s))=Y := by ext a; simp [Y,h,Nat.ModEq,Nat.mod_eq_of_lt ls]
    rw [eqs]; dsimp only [w]; rw [sum_sub_distrib,←sum_filter,←mul_sum]
    exact est.trans_eq (by dsimp only [c,V,e,z]; ring)
  have ml : (Fixed.B b)^4≤M := by change (2^(1000*Fixed.h b))^4≤2^(9997*Fixed.h b)
                                  rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  have np : (0:ℝ)<B := by dsimp only [B]; exact_mod_cast bp
  have qb : q*(Fixed.B b)≤M := (Nat.mul_le_mul_right _ cq).trans ((by ring : (Fixed.B b)^3*Fixed.B b=(Fixed.B b)^4) ▸ ml)
  have qs : (q:ℝ)≤M/B := (le_div_iff₀ np).mpr (by dsimp only [B]; exact_mod_cast qb)
  have unit : (1:ℝ)≤q := by exact_mod_cast qp
  have Mbig : (q:ℝ)≤M := qs.trans (div_le_self (Nat.cast_nonneg _) (by dsimp only [B]; exact_mod_cast (show 1≤Fixed.B b from bp)))
  let A := 4*D*(M/B)
  have posA : 0≤A := by dsimp [A];positivity
  have mid (T : Finset ℕ) (sub : T⊆P) (low : Fixed.B b<sieveProduct T) (_ : sieveProduct T≤(Fixed.B b)^2) (s : ℕ) :
      (∑ a∈X with a ≡ s [MOD sieveProduct T], |w a|) ≤ A := by
    have h := contrast_mass (L:=L) (M:=M) (s:=s) (r:=r) (bp.trans low) qp (cop T sub) X (filter_subset ..) f g D dp bound
    have frac := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) M) np (by dsimp only [B]; exact_mod_cast low.le : B≤(sieveProduct T:ℝ))
    dsimp only [A]; change _ ≤ D*(2*((M:ℝ)/(sieveProduct T:ℝ))+q+1) at h
    exact h.trans ((mul_le_mul_of_nonneg_left (by linarith only [frac,qs,unit] : 2*((M:ℝ)/(sieveProduct T:ℝ))+q+1≤4*(M/B)) dp).trans_eq (by ring))
  have mass : (∑ a∈X,|w a|)≤4*D*M := by
    have h := contrast_mass (L:=L) (M:=M) (h:=1) (s:=0) (r:=r) (by decide) qp (Nat.coprime_one_left _) X (filter_subset ..) f g D dp bound
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (by linarith only [Mbig,unit] : 2*(M:ℝ)+q+1≤4*M) dp).trans_eq (by ring))
  have sumPos : 0≤∑ T∈P.powerset,pairDivisorWeight T := sum_nonneg (fun T h=> prod_nonneg (fun p pm=>by
    have lb : (2:ℝ)≤p := by exact_mod_cast (pr p ((mem_powerset.mp h) pm)).two_le
    exact div_nonneg (by linarith) (sq_nonneg _)))
  have gamma := centered_pair_bound X P pr (Fixed.rootBase n) (Fixed.d b) (Fixed.B b) hp bp sizes w c A short mid posA
  have tail := mul_le_mul (mul_le_mul_of_nonneg_left mass posA) (weight b big P (fun p pm=>⟨pr p pm,sizes p pm⟩)) sumPos (by positivity)
  exact gamma.trans (add_le_add le_rfl (tail.trans_eq (by dsimp only [A,z]; ring)))

end Cogentic.Construction

#print axioms Cogentic.Construction.centered_residue_class_mean

#print axioms Cogentic.Construction.centered_residue_pair_model
namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- For all hit patterns, the physical two-field ratio to the unrestricted
marginal has the explicit product of the two full-band insertions. The two
saddles are independent of the prescribed ordinary rows. -/
theorem hit_smooth_marginal_ratio (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks →
    let O := PrescribedRows.unrestricted n ell
    ∃ α β : ℝ, α∈Set.Icc (199/200:ℝ) 1 ∧ β∈Set.Icc (199/200:ℝ) 1 ∧
      Window.saddleMean (primeBand b) α=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      Window.saddleMean (primeBand b) β=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      0<smoothMarkProbability O O a ∧ ∀ R T : PrescribedRows n ell,
      let F := fullBandInsertion b (R.hitProduct a) α*fullBandInsertion b (T.hitProduct a) β
      0<F ∧ |(smoothMarkProbability R T a/smoothMarkProbability O O a)/F-1|≤C*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨A,ap,b₀,ratio⟩ := full_band_marginal_ratio line K hk
  refine ⟨2*A+A^2,by positivity,b₀,?_⟩
  intro n ell a b large hn comp target absent mark O
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  let P (S : PrescribedRows n ell) (j : Bool) := prescribedProbability S j (smoothMarkEvent S j a)
  let raw (S : PrescribedRows n ell) (j : Bool) := prescribedProbability S j
    (fun k=>supportedValue (sieveBand n ell (S.prefactor a j)) (S.intercept a j k.1 k.2))
  have id (S : PrescribedRows n ell) (j : Bool) : raw S j=P S j := probability_congr S j _ (smoothMarkEvent S j a) rfl
  obtain ⟨α,ha,ma,pa,ra⟩ := ratio large hn comp target absent mark false
  obtain ⟨β,hb,mb,pb,rb⟩ := ratio large hn comp target absent mark true
  change 0<raw O false at pa
  change 0<raw O true at pb
  rw [id] at pa pb
  refine ⟨α,β,ha,hb,ma,mb,mul_pos pa pb,?_⟩
  intro R T F
  let f := fullBandInsertion b (R.hitProduct a) α; let g := fullBandInsertion b (T.hitProduct a) β
  obtain ⟨fp,ef⟩ := ra R
  obtain ⟨gp,eg⟩ := rb T
  change |(raw R false/raw O false)/f-1|≤A*e at ef
  change |(raw T true/raw O true)/g-1|≤A*e at eg
  rw [id,id] at ef eg
  refine ⟨mul_pos fp gp,?_⟩
  let x := (P R false/P O false)/f; let y := (P T true/P O true)/g
  change |x-1|≤A*e at ef
  change |y-1|≤A*e at eg
  have ident : (smoothMarkProbability R T a/smoothMarkProbability O O a)/F-1=(x-1)+(y-1)+(x-1)*(y-1) := by
    change (P R false*P T true/(P O false*P O true))/(f*g)-1=_
    dsimp only [x,y]; field_simp [pa.ne',pb.ne',fp.ne',gp.ne']; ring
  have eo : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have ee := mul_le_mul_of_nonneg_left eo (le_of_lt (show 0<e from exp_pos _))
  have cor := mul_le_mul ef eg (abs_nonneg _) (mul_nonneg ap.le (exp_pos _).le)
  rw [ident]
  apply (abs_add_le ..).trans
  apply (add_le_add (abs_add_le ..) (abs_mul ..).le).trans
  change _ ≤ (2*A+A^2)*e
  linarith only [ef,eg,cor,mul_le_mul_of_nonneg_left ee (sq_nonneg A)]

/-- Away from the prescribed root classes in both fields, the unrestricted
smoothness probability is the correct physical denominator up to an
arbitrarily small relative error, uniformly in the ordinary prescriptions. -/
theorem unhit_smooth_marginal_ratio (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ R T : PrescribedRows n ell,
    R.hitProduct a=1 → T.hitProduct a=1 →
    let O := PrescribedRows.unrestricted n ell
    0<smoothMarkProbability O O a ∧
    |smoothMarkProbability R T a/smoothMarkProbability O O a-1|≤C*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨C,cp,b₀,ratio⟩ := hit_smooth_marginal_ratio line K hk
  refine ⟨C,cp,b₀,?_⟩
  intro n ell a b large hn comp target absent mark R T rh th O
  obtain ⟨α,β,_,_,_,_,pos,all⟩ := ratio large hn comp target absent mark
  obtain ⟨fp,error⟩ := all R T
  refine ⟨pos,?_⟩
  let mass (x : ℝ) := Window.shiftedMass (primeBand b) (Window.primeProbability x) (fun p=>log p) (log (Fixed.B b)) 0
  have ident (x : ℝ) : fullBandInsertion b 1 x=mass x/mass x := by simp [fullBandInsertion,mass]
  rw [rh,th,ident,ident] at fp error
  by_cases ax : mass α=0
  · simp [ax] at fp
  by_cases bx : mass β=0
  · simp [bx] at fp
  simpa only [div_self ax,div_self bx,mul_one,div_one] using error

/-- A rank-one error at the scale sqrt(p^(-α) q^(-α))/u has squared
Frobenius norm at least one at the band saddle. A pointwise O(1/u)
estimate at this scale cannot alone give a vanishing band-wide norm. -/
theorem saddle_pointwise_error_frobenius_floor (J : Finset ℕ) (H u α : ℝ)
    (hp : 0<H) (up : 0<u) (band : ∀ p∈J, log p≤H)
    (saddle : Window.saddleMean J α=H*u) :
    1 ≤ ∑ p∈J, ∑ q∈J,(sqrt ((p:ℝ)^(-α))*sqrt ((q:ℝ)^(-α))/u)^2 := by
  let w (p : ℕ) := (p:ℝ)^(-α)
  have wn (p : ℕ) : 0≤w p := rpow_nonneg (Nat.cast_nonneg _) _
  have prob (p : ℕ) : Window.primeProbability α p ≤ w p := by
    change w p/(1+w p)≤w p
    exact div_le_self (wn p) (by linarith only [wn p])
  have terms := sum_le_sum (s:=J) (fun p pm=>
    (mul_le_mul_of_nonneg_left (band p pm) (show 0≤Window.primeProbability α p by dsimp [Window.primeProbability]; positivity)).trans
      (mul_le_mul_of_nonneg_right (prob p) hp.le))
  change (Window.saddleMean J α)≤_ at terms
  rw [saddle,←sum_mul,mul_comm] at terms
  have lower := (one_le_div up).mpr ((mul_le_mul_iff_left₀ hp).mp terms)
  have square := pow_le_pow_left₀ zero_le_one lower 2
  simp only [one_pow] at square
  apply square.trans_eq
  rw [div_pow,sq,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl; intro p _
  apply sum_congr rfl; intro q _
  rw [div_pow,mul_pow,sq_sqrt (wn p),sq_sqrt (wn q)]

private def contrastBilinear (X Y : Finset ℕ) (E : ℕ→ℕ→ℝ) (f g : ℕ→ℝ) :=
  ∑ a∈X, ∑ y∈Y,f a*g y*E a y

private theorem contrast_bilinear_sub (X : Finset ℕ) (E : ℕ→ℕ→ℝ) (f g : ℕ→ℝ) :
    contrastBilinear X X E (fun a=>f a-g a) (fun a=>f a-g a) =
    contrastBilinear X X E f f - contrastBilinear X X E f g -
    contrastBilinear X X E g f + contrastBilinear X X E g g := by
  unfold contrastBilinear
  simp only [←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro y _; ring

private def contrastMask (q r : ℕ) (f : ℕ→ℝ) (a : ℕ) :=
  if a ≡ r [MOD q] then (q:ℝ)*f a else 0

private theorem contrast_bilinear_mask (X : Finset ℕ) (E : ℕ→ℕ→ℝ) (f g : ℕ→ℝ) (q s r v : ℕ) :
    contrastBilinear X X E (contrastMask q r f) (contrastMask s v g) =
      ((q:ℝ)*s)*contrastBilinear (X.filter (fun a=>a ≡ r [MOD q])) (X.filter (fun y=>y ≡ v [MOD s])) E f g := by
  classical
  unfold contrastBilinear contrastMask
  rw [sum_filter,Finset.mul_sum]
  apply sum_congr rfl; intro a _
  by_cases ax : a ≡ r [MOD q]
  · rw [if_pos ax,if_pos ax,sum_filter,Finset.mul_sum]
    apply sum_congr rfl; intro y _
    by_cases yy : y ≡ v [MOD s]
    · simp [yy]; ring
    · simp [yy]
  · simp [ax]

private theorem contrast_score_identity {n ell : ℕ} (R T : PrescribedRows n ell) (X : Finset ℕ)
    (w : ℕ→ℝ) (pos : ∀ a∈X,0<smoothMarkProbability R T a) :
    twoFieldSecond R T X (fun a=>w a/smoothMarkProbability R T a) (smoothMarkEvent R false) (smoothMarkEvent T true) =
      ∑ a∈X, ∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y+1) := by
  unfold twoFieldSecond
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro y hy
  let p := smoothMarkProbability R T
  let j := prescribedProbability R false (fun k => smoothMarkEvent R false a k ∧ smoothMarkEvent R false y k)*
    prescribedProbability T true (fun k=>smoothMarkEvent T true a k ∧ smoothMarkEvent T true y k)
  change (w a/p a*(w y/p y))*j=w a*w y*((j-p a*p y)/(p a*p y)+1)
  field_simp [show p a≠0 from (pos a ha).ne',show p y≠0 from (pos y hy).ne']; ring

set_option maxHeartbeats 1200000 in
/-- A single ordinary congruence indicator with its smooth comparison weight
subtracted on the full coefficient probability space. The denominator is the
actual smoothness marginal on the prescribed coefficient space. -/
theorem centered_residue_score_second (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    ∀ R T : PrescribedRows n ell, let b := n.log2+1
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (q r : ℕ), 0<q → Squarefree q → q≤(Fixed.B b)^3 → q.Coprime (markModulus n ell) →
    let P := pairCorrectionPrimes b
    (∀ p∈P, p.Coprime q) → let L := firstCellMark b cell; let M := cellMarkCount b
    let X := constructorCellMarks n ell cell
    ∀ (f g : ℕ→ℝ) (D : ℝ), 0≤D → (∀ a∈X, |f a|≤D ∧ |g a|≤D) →
    (∑ j∈range M,f (L+j))=(∑ j∈range M,g (L+j)) →
    let V := fun w : ℕ→ℝ => |w (L+(M-1))|+∑ j∈range (M-1),|w (L+(j+1))-w (L+j)|
    let w := fun a=> (if a ≡ r [MOD q] then (q:ℝ)*f a else 0)-g a
    let z := (Fixed.z b:ℝ); let e := exp (-K*z^2); let B := (Fixed.B b:ℝ)
    let v := fun a=>w a/smoothMarkProbability R T a
    (∑' k : R.CoeffPoint false × T.CoeffPoint true,
      twoFieldWeight R T k*(twoFieldScore X v (smoothMarkEvent R false) (smoothMarkEvent T true) k.1.val k.2.val)^2) ≤
      4*(D*D)*(C*e)*(M:ℝ)^2 +
      ((V f+V g)*(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ)) + 16*D^2*(M:ℝ)^2/B*exp (48*z) := by
  obtain ⟨C,cp,b₁,pair⟩ := cell_pair_covariance_approximation line K hK
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_margin line
  obtain ⟨n₀,model⟩ := centered_residue_pair_model line K hK
  refine ⟨C,cp,max n₀ (max 2 (2^(max b₁ b₂))),?_⟩
  intro n large ell target comp absent R T b cell q r qp sf cq ok P pr L M X f g D dp bounds equal V w z e B v
  obtain ⟨old,more⟩ := max_le_iff.mp large
  obtain ⟨hn,limit⟩ := max_le_iff.mp more
  have huge : max b₁ b₂≤b := ((Nat.le_log2 (by omega : n≠0)).mpr limit).trans (Nat.le_succ _)
  let γ := fun a y=>pairGamma P (Fixed.rootBase n) a y
  let E := fun a y=>normalizedSmoothCovariance R T a y-(γ a y^2-1)
  let U := (D*D)*(C*e)*(M:ℝ)^2
  have raw (q' s' r' v' : ℕ) (qs : Squarefree q') (ss : Squarefree s')
      (qb : q'≤(Fixed.B b)^3) (sb : s'≤(Fixed.B b)^3) (F G : ℕ→ℝ)
      (fb : ∀ a∈X, |F a|≤D) (gb : ∀ a∈X, |G a|≤D) :
      |contrastBilinear X X E (contrastMask q' r' F) (contrastMask s' v' G)|≤U := by
    have est := pair R T (max_le_iff.mp huge).1 hn comp target absent cell cell q' s' r' v' qs ss qb sb F G D D dp dp
      (fun a ha=>fb a (mem_filter.mp ha).1) (fun a ha=>gb a (mem_filter.mp ha).1)
    have mp : 0<(M:ℝ)^2 := by dsimp [M,cellMarkCount]; positivity
    rw [contrast_bilinear_mask,abs_mul,abs_of_nonneg (show 0≤(q':ℝ)*s' by positivity)]
    exact (div_le_iff₀ mp).mp est
  have one : 1≤(Fixed.B b)^3 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
  have fb (a) (ha : a∈X) := (bounds a ha).1
  have gb (a) (ha : a∈X) := (bounds a ha).2
  have aa := raw q q r r sf sf cq cq f f fb fb
  have ab := raw q 1 r 0 sf squarefree_one cq one f g fb gb
  have ba := raw 1 q 0 r squarefree_one sf one cq g f gb fb
  have bb := raw 1 1 0 0 squarefree_one squarefree_one one one g g gb gb
  have plain : contrastMask 1 0 g=g := by funext a; simp [contrastMask,Nat.modEq_one]
  rw [plain] at ab ba bb
  have er : contrastBilinear X X E w w≤4*U := by
    change contrastBilinear X X E (fun a=>contrastMask q r f a-g a) (fun a=>contrastMask q r f a-g a) ≤_
    rw [contrast_bilinear_sub]
    linarith only [(abs_le.mp aa).2,(abs_le.mp ab).1,(abs_le.mp ba).1,(abs_le.mp bb).2]
  have pos (a) (ha : a∈X) : 0<smoothMarkProbability R T a := by
    have mark := (mem_filter.mp ha).2
    have lb : 0<8/(Fixed.B b:ℝ) := by dsimp [Fixed.B]; positivity
    have each (S : PrescribedRows n ell) (s : Bool) :
        0<prescribedProbability S s (smoothMarkEvent S s a) := by
      have raw := lb.trans_le (floor S (max_le_iff.mp huge).2 hn comp target absent mark s)
      exact raw.trans_eq (probability_congr S s _ (smoothMarkEvent S s a) rfl)
    exact mul_pos (each R false) (each T true)
  have dec : (∑ a∈X,∑ y∈X,w a*w y*(normalizedSmoothCovariance R T a y+1)) =
      contrastBilinear X X E w w+∑ a∈X,∑ y∈X,w a*w y*(γ a y)^2 := by
    unfold contrastBilinear
    rw [←sum_add_distrib];apply sum_congr rfl; intro a _
    rw [←sum_add_distrib];apply sum_congr rfl; intro y _; dsimp only [E]; ring
  rw [(twoField_score_second R T target X v (smoothMarkEvent R false) (smoothMarkEvent T true)).tsum_eq,contrast_score_identity R T X w pos,dec]
  have exactModel := model n old ell target comp absent cell q r qp cq ok pr f g D dp bounds equal
  change (∑ a∈X,∑ y∈X,w a*w y*(γ a y)^2)≤_ at exactModel
  exact (add_le_add er exactModel).trans_eq (by dsimp only [U,V,z,e,B]; ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.centered_residue_score_second

#print axioms Cogentic.Construction.pooled_residue_class_contrast

#print axioms Cogentic.Construction.unhit_smooth_marginal_ratio

#print axioms Cogentic.Construction.hit_smooth_marginal_ratio
#print axioms Cogentic.Construction.saddle_pointwise_error_frobenius_floor
