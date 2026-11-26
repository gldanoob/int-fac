import Cogentic.PooledResidueMoment
import Cogentic.CommonWeightTransfer

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- Moment bound for a signed sum of mesh profiles and for its absolute envelope.
The last two arguments are the sum of the raw mesh means and the total variation. -/
def profileMomentBound (b : ℕ) (K C A δ V : ℝ) : ℝ :=
  let M := (cellMarkCount b:ℝ)
  let z := (Fixed.z b:ℝ)
  let e := exp (-K*z^2)
  A^2*C*e*M^2+(|δ|+V*(1+2*exp 6)*M*e)^2*exp (8/(Fixed.d b:ℝ))+
    4*A^2*M^2/(Fixed.B b:ℝ)*exp (48*z)

/-- Cancellation of the signed raw mean yields a logarithmic-square saving
uniformly in the signed and unsigned component bounds. -/
theorem profileMomentBound_cancellation (K C H : ℝ) (hk : 1≤K) (cp : 0≤C) :
    ∃ D : ℝ, 0<D ∧ ∃ b₀ : ℕ, ∀ b≥b₀, 0<b → ∀ A T d v d' v' : ℝ,
    let M := (cellMarkCount b:ℝ); let e := exp (-K*(Fixed.z b:ℝ)^2)
    0≤T → |A|≤T → |v|≤T → |v'|≤T → |d|≤T*M*e → |d'|≤T*M →
    2*profileMomentBound b K C A d v+2*(H*e)^2*profileMomentBound b K C A d' v'≤D*(T*M)^2*e := by
  let h := 1+2*exp 6
  let L := C+(1+h)^2*exp 8+4
  have hn : 0≤h := by dsimp only [h];positivity
  have lp : 0<L := by dsimp only [L];positivity
  obtain ⟨b₀,save⟩ := fixed_band_power_savings (K+48) (by linarith only [hk])
  refine ⟨2*(1+H^2)*L,by positivity,b₀,?_⟩
  intro b big bp A T d v d' v' M e tn ba bv bv' ds da
  let z := (Fixed.z b:ℝ); let B := (Fixed.B b:ℝ)
  have zp : 1≤z := by dsimp only [z,Fixed.z];exact_mod_cast (Nat.le_add_left 1 b.log2)
  have bo : 1≤B := by dsimp only [B];exact_mod_cast (Nat.one_le_two_pow : 1≤Fixed.B b)
  have ep : 0≤e := (exp_pos _).le
  have eo : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have mp : 0≤M := Nat.cast_nonneg _
  have d1 : (1:ℝ)≤Fixed.d b := by exact_mod_cast Fixed.degree_pos bp
  have e8 : exp (8/(Fixed.d b:ℝ))≤exp 8 := exp_le_exp.mpr ((div_le_iff₀ (zero_lt_one.trans_le d1)).mpr (by linarith))
  have inv : 1/B≤exp (-(K+48)*z^2) := calc
    _ = B^(-(1:ℝ)) := by rw [rpow_neg (zero_le_one.trans bo),rpow_one,one_div]
    _ ≤ B^(-17/200:ℝ) := rpow_le_rpow_of_exponent_le bo (by norm_num)
    _ ≤ _ := save b big
  have tail : 1/B*exp (48*z)≤e := calc
    _ ≤ exp (-(K+48)*z^2)*exp (48*z) := mul_le_mul_of_nonneg_right inv (exp_pos _).le
    _ ≤ _ := by rw [←exp_add];apply exp_le_exp.mpr;nlinarith only [mul_nonneg (sub_nonneg.mpr zp) (zero_le_one.trans zp)]
  have unit (d₀ v₀ t : ℝ) (vt : |v₀|≤T) (dt : |d₀|≤T*M*t) (en : e≤t) (et : t≤1) :
      profileMomentBound b K C A d₀ v₀≤L*(T*M)^2*t := by
    have tp := ep.trans en
    have sqA := pow_le_pow_left₀ (abs_nonneg _) ba 2
    rw [sq_abs] at sqA
    have ga : A^2*M^2≤(T*M)^2 := by rw [mul_pow];exact mul_le_mul_of_nonneg_right sqA (sq_nonneg _)
    have arg : abs (|d₀|+v₀*h*M*e) ≤ (1+h)*(T*M)*t := by
      apply (abs_add_le ..).trans;rw [abs_abs,abs_mul,abs_mul,abs_mul,abs_of_nonneg hn,abs_of_nonneg mp,abs_of_nonneg ep]
      have step := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right vt hn) mp) en ep (by positivity : 0≤T*h*M)
      exact (add_le_add dt step).trans_eq (by ring)
    have m₀ := pow_le_pow_left₀ (abs_nonneg _) arg 2
    rw [sq_abs] at m₀
    have first := mul_le_mul ga (mul_le_mul_of_nonneg_left en cp) (mul_nonneg cp ep) (sq_nonneg _)
    have third := mul_le_mul ga (tail.trans en) (mul_nonneg (one_div_nonneg.mpr (zero_le_one.trans bo)) (exp_pos _).le) (sq_nonneg _)
    have second := mul_le_mul m₀ e8 (exp_pos _).le (sq_nonneg _)
    have st := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left et tp) (by positivity : 0≤(1+h)^2*(T*M)^2*exp 8)
    change A^2*C*e*M^2+(|d₀|+v₀*h*M*e)^2*exp (8/(Fixed.d b:ℝ))+4*A^2*M^2/B*exp (48*z)≤_
    dsimp only [L]
    linear_combination first+4*third+second+st
  have signed := unit d v e bv ds le_rfl eo
  have unsigned := unit d' v' 1 bv' (by simpa using da) eo le_rfl
  have scale := mul_le_mul_of_nonneg_left unsigned (by positivity : 0≤(H*e)^2)
  have diff := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left eo ep) (by positivity : 0≤H^2*L*(T*M)^2)
  nlinarith only [signed,scale,diff]

/-- The common physical denominator may be used in a two-sided signed CRT
comparison. The unsigned envelope is multiplied by the squared saddle error,
so only the signed profile requires cancellation of its mesh means. -/
theorem physical_profile_second (line : DirichletLZerosOnLine) (K : ℝ) (hk : 1≤K) :
    ∃ C H : ℝ, 0<C ∧ 0<H ∧ ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ {ι : Type*} (S : Finset ι), ∀ (cell : ι→Option (Bool×Fin (Fixed.d b))) (q r : ι→ℕ),
    (∀ i∈S, 0<q i ∧ Squarefree (q i) ∧ q i≤(Fixed.B b)^3 ∧ (q i).Coprime (markModulus n ell) ∧
      ∀ p∈pairCorrectionPrimes b,p.Coprime (q i)) →
    let Y := fun i=>(constructorCellMarks n ell (cell i)).filter (fun a=>a ≡ r i [MOD q i])
    let X := S.biUnion Y
    ∃ α β : ℕ→ℝ, (∀ a∈X, saddleMean (primeBand b) (α a)=log ((exactMean n ell a false:ℝ)/targetPart n ell a false) ∧
      saddleMean (primeBand b) (β a)=log ((exactMean n ell a true:ℝ)/targetPart n ell a true) ∧
      α a∈Set.Icc (199/200:ℝ) 1 ∧ β a∈Set.Icc (199/200:ℝ) 1) ∧
    ∀ (R T : PrescribedRows n ell) (w : ℕ→ℝ) (f : ι→ℕ→ℝ) (D : ι→ℝ),
    (∀ i∈S, 0≤D i ∧ ∀ a∈constructorCellMarks n ell (cell i), |f i a|≤D i) →
    let J := fun a=>fullBandInsertion b (R.hitProduct a) (α a)*fullBandInsertion b (T.hitProduct a) (β a)
    (∀ a∈X, w a*J a=pooledMarkWeight S Y (fun i t=>(q i:ℝ)*f i t) a) →
    let O := PrescribedRows.unrestricted n ell
    let L := fun i=>firstCellMark b (cell i); let M := cellMarkCount b
    let δ := fun (g : ι→ℕ→ℝ)=>∑ i∈S,∑ j∈range M,g i (L i+j)
    let V := fun (g : ι→ℕ→ℝ)=>∑ i∈S,meshVariation (L i) M (g i)
    let B := fun g=>profileMomentBound b K C (∑ i∈S,D i) (δ g) (V g)
    twoFieldSecond R T X (fun a=>w a/smoothMarkProbability O O a) (smoothMarkEvent R false) (smoothMarkEvent T true) ≤
      2*B f+2*(H*exp (-K*(Fixed.z b:ℝ)^2))^2*B (fun i a=>|f i a|) := by
  obtain ⟨H,hp,b₀,physical⟩ := common_weight_second_transfer line K hk
  obtain ⟨C,cp,n₁,mesh⟩ := pooled_residue_score_second_uniform line K hk
  refine ⟨C,H,cp,hp,max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target comp sieved b ι S cell q r props Y X
  obtain ⟨en,rest⟩ := max_le_iff.mp large
  obtain ⟨hn,lg⟩ := max_le_iff.mp rest
  have big := ((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _)
  have marks (a) (ha : a∈X) : a∈(construct n ell 0 0 0 0).marks := by
    obtain ⟨i,_,hy⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp (mem_filter.mp hy).1).2
  obtain ⟨α,β,law,transfer⟩ := physical big hn comp target sieved X marks
  refine ⟨α,β,law,?_⟩
  intro R T w f D bd J profile O L M δ V B
  let P := smoothMarkProbability R T
  let E := smoothMarkEvent R false; let F := smoothMarkEvent T true
  let raw := fun a=>w a/smoothMarkProbability O O a
  let model := fun a=>w a*(J a/P a)
  let absModel := fun a=>|w a| * (J a/P a)
  let W := fun (g : ι→ℕ→ℝ) a=>pooledMarkWeight S Y (fun i t=>(q i:ℝ)*g i t) a
  let g := fun i a=>|f i a|
  let η := H*exp (-K*(Fixed.z b:ℝ)^2)
  have Pn (a) : 0≤P a :=
    mul_nonneg (R.probability_unit target false _).1 (T.probability_unit target true _).1
  have pt (a) (ha : a∈X) : |W f a|≤W g a := by
    apply (abs_sum_le_sum_abs ..).trans_eq
    apply sum_congr rfl;intro i _
    by_cases hy : a∈Y i <;> simp [g,hy,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (q i))]
  have first (x y : ℤ×ℤ) : twoFieldScore X model E F x y=twoFieldScore X (fun a=>W f a/P a) E F x y := by
    apply sum_congr rfl;intro a ha
    dsimp only [model];rw [←mul_div_assoc,profile a ha]
  have second (x y : ℤ×ℤ) : |twoFieldScore X absModel E F x y|≤twoFieldScore X (fun a=>W g a/P a) E F x y := by
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum;intro a ha
    by_cases yes : E a x ∧ F a y
    · simp only [if_pos yes,mul_one]
      rw [show |absModel a|=|w a*J a|/P a by
        change |(|w a| * (J a/P a))|=|w a*J a|/P a; simp only [abs_mul,abs_abs,abs_div,abs_of_nonneg (Pn a),mul_div_assoc],profile a ha]
      exact div_le_div_of_nonneg_right (pt a ha) (Pn a)
    · simp [yes]
  let moment := fun z=>twoFieldSecond R T X z E F
  have momentEq : moment model=moment (fun a=>W f a/P a) := by
    apply (twoField_score_second R T target X model E F).unique
    simpa only [first] using twoField_score_second R T target X (fun a=>W f a/P a) E F
  have momentLe : moment absModel ≤ moment (fun a=>W g a/P a) := by
    apply hasSum_le _ (twoField_score_second R T target X absModel E F) (twoField_score_second R T target X (fun a=>W g a/P a) E F)
    intro k
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (R.pointMass_nonneg false k.1) (T.pointMass_nonneg true k.2))
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (second k.1.val k.2.val) 2
  have combined : moment raw≤2*moment model+2*moment (fun a=>raw a-model a) := by
    apply hasSum_le _ (twoField_score_second R T target X raw E F)
      (((twoField_score_second R T target X model E F).mul_left 2).add
        ((twoField_score_second R T target X (fun a=>raw a-model a) E F).mul_left 2))
    intro k
    have sub : twoFieldScore X (fun a=>raw a-model a) E F k.1.val k.2.val=
        twoFieldScore X raw E F k.1.val k.2.val-twoFieldScore X model E F k.1.val k.2.val := by
      simp only [twoFieldScore,sub_mul,sum_sub_distrib]
    rw [sub]
    have wp := mul_nonneg (R.pointMass_nonneg false k.1) (T.pointMass_nonneg true k.2)
    change 0≤twoFieldWeight R T k at wp
    nlinarith only [mul_nonneg wp (sq_nonneg (twoFieldScore X raw E F k.1.val k.2.val-2*twoFieldScore X model E F k.1.val k.2.val))]
  have modelBD : moment (fun a=>W f a/P a)≤B f :=
    mesh n en ell target comp sieved R T S cell q r f D props bd
  have absBD : moment (fun a=>W g a/P a)≤B g :=
    mesh n en ell target comp sieved R T S cell q r g D props (fun i hi=>⟨(bd i hi).1,fun a ha=>by
      simpa only [g,abs_abs] using (bd i hi).2 a ha⟩)
  have err := transfer R T w
  change moment (fun a=>raw a-model a)≤η^2*moment absModel at err
  have bound := err.trans (mul_le_mul_of_nonneg_left (momentLe.trans absBD) (sq_nonneg η))
  change moment raw≤2*B f+2*η^2*B g
  rw [momentEq] at combined
  linarith only [combined,modelBD,bound]

end
end Cogentic.Construction
#print axioms Cogentic.Construction.physical_profile_second
