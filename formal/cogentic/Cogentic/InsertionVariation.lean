import Cogentic.CellAtomVariation
import Cogentic.MarkIntervals
import Cogentic.ConstructionReduction

namespace Cogentic.Window
open Complex Finset Real MeasureTheory
noncomputable section

private def cis (x : ℝ) : ℂ := Complex.exp (Complex.I*x)

private theorem cis_one (x : ℝ) : ‖cis x‖=1 := Complex.norm_exp_I_mul_ofReal x

private theorem cis_change (x y : ℝ) : ‖cis x-cis y‖≤|x-y| := by
  have id : cis x-cis y=cis y*(cis (x-y)-1) := by
    unfold cis; rw [mul_sub,←Complex.exp_add,mul_one]
    congr 2; push_cast; ring
  rw [id,norm_mul,cis_one,one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

private def mix (r z : ℝ) : ℂ := ((1-r:ℝ):ℂ)+(r:ℂ)*cis z

private theorem mix_bound {r : ℝ} (z : ℝ) (r0 : 0≤r) (r1 : r≤1) : ‖mix r z‖≤1 := by
  apply (norm_add_le ..).trans
  rw [norm_mul,cis_one,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr r1),abs_of_nonneg r0]; ring_nf; rfl

private theorem factor_mix (r z : ℝ) : centeredFactor r z=cis (-r*z)*mix r z := by
  change ((1-r:ℝ):ℂ)*cis (-r*z)+(r:ℂ)*cis ((1-r)*z)=_
  have phase : cis ((1-r)*z)=cis (-r*z)*cis z := by
    unfold cis; rw [←Complex.exp_add]; congr 1; push_cast; ring
  rw [phase]; dsimp only [mix]; ring

private theorem factor_change (z r s : ℝ) (s0 : 0 ≤ s) (s1 : s ≤ 1) :
    ‖centeredFactor r z-centeredFactor s z‖≤2*|z| *|r-s| := by
  have part : ‖mix r z-mix s z‖≤|r-s| *|z| := by
    have id : mix r z-mix s z=((r-s:ℝ):ℂ)*(cis z-1) := by unfold mix; push_cast; ring
    rw [id,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (abs_nonneg _)
  have phase := cis_change (-r*z) (-s*z)
  rw [show -r*z- -s*z= -(r-s)*z by ring,abs_mul,abs_neg] at phase
  rw [factor_mix,factor_mix,show cis (-r*z)*mix r z-cis (-s*z)*mix s z =
    cis (-r*z)*(mix r z-mix s z)+(cis (-r*z)-cis (-s*z))*mix s z by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,cis_one,one_mul]
  have b := mul_le_mul phase (mix_bound z s0 s1) (norm_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  linarith only [b,part]

private theorem factor_bound (z r : ℝ) (r0 : 0≤r) (r1 : r≤1) : ‖centeredFactor r z‖≤1 := by
  rw [factor_mix,norm_mul,cis_one,one_mul]; exact mix_bound z r0 r1

private theorem characteristic_change {ι : Type*} (J : Finset ι) (r s ell : ι→ℝ) (t : ℝ)
    (r0 : ∀ p∈J,r p∈Set.Icc 0 1) (s0 : ∀ p∈J,s p∈Set.Icc 0 1) :
    ‖saddleCharacteristic J r ell t-saddleCharacteristic J s ell t‖≤2*|t| *(∑ p∈J,|ell p| *|r p-s p|) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [saddleCharacteristic]
  | insert p J jp ih =>
    have rp := r0 p (mem_insert_self ..)
    have sp := s0 p (mem_insert_self ..)
    have rt i (hm : i∈J) := r0 i (mem_insert_of_mem hm)
    have st i (hm : i∈J) := s0 i (mem_insert_of_mem hm)
    have tail := ih rt st
    let X := saddleCharacteristic J r ell t; let Y := saddleCharacteristic J s ell t
    let a := centeredFactor (r p) (t*ell p); let b := centeredFactor (s p) (t*ell p)
    have yn : ‖Y‖≤1 := by
      dsimp only [Y,saddleCharacteristic]; rw [norm_prod]; exact prod_le_one (fun _ _=>norm_nonneg _)
        (fun i h=>factor_bound _ _ (st i h).1 (st i h).2)
    have ab := factor_change (t*ell p) (r p) (s p) sp.1 sp.2
    rw [abs_mul] at ab
    rw [saddleCharacteristic,saddleCharacteristic,prod_insert jp,prod_insert jp,sum_insert jp]
    change ‖a*X-b*Y‖≤_
    rw [show a*X-b*Y=a*(X-Y)+(a-b)*Y by ring]
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul]
    have l := mul_le_mul_of_nonneg_right (factor_bound (t*ell p) (r p) rp.1 rp.2) (norm_nonneg (X-Y))
    have rr := mul_le_mul_of_nonneg_left yn (norm_nonneg (a-b))
    change ‖X-Y‖≤_ at tail
    change ‖a-b‖≤_ at ab
    linarith only [l,rr,tail,ab]

/-- The central Fourier mass is uniformly Lipschitz in the weighted total
change of the Bernoulli parameters, independently of the insertion shift. -/
theorem shiftedMass_parameter_change {ι : Type*} (J : Finset ι) (r s ell : ι→ℝ) (H a : ℝ)
    (hp : 0<H) (r0 : ∀ p∈J, r p∈Set.Icc 0 1) (s0 : ∀ p∈J, s p∈Set.Icc 0 1) :
    |shiftedMass J r ell H a-shiftedMass J s ell H a| ≤ (4/H^2)*(∑ p∈J, |ell p| *|r p-s p|) := by
  let F (v : ι→ℝ) (t : ℝ) := (cis (a*t)*saddleCharacteristic J v ell t).re
  have cont (v : ι→ℝ) : Continuous (F v) := by
    unfold F saddleCharacteristic
    apply Complex.continuous_re.comp
    apply Continuous.mul (by unfold cis; fun_prop)
    apply continuous_finsetProd; intro p _
    change Continuous (fun t : ℝ => ((1-v p:ℝ):ℂ)*cis (-v p*(t*ell p))+(v p:ℂ)*cis ((1-v p)*(t*ell p)))
    unfold cis; fun_prop
  let d := ∑ p∈J, |ell p| *|r p-s p|
  have dn : 0≤d := sum_nonneg (fun p _=>mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have ip := one_div_pos.mpr hp
  have bd (t : ℝ) (ht : t∈Set.uIoc (-(1/H)) (1/H)) : ‖F r t-F s t‖≤(2/H)*d := by
    rw [Set.uIoc_of_le (by linarith)] at ht
    have tcap := abs_le.mpr ⟨ht.1.le,ht.2⟩
    dsimp only [F]; rw [Real.norm_eq_abs,←Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    rw [←mul_sub,norm_mul,cis_one,one_mul]
    apply (characteristic_change J r s ell t r0 s0).trans
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left tcap (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)) dn
  change |(∫ t in -(1/H)..1/H,F r t)-(∫ t in -(1/H)..1/H,F s t)|≤_
  rw [←intervalIntegral.integral_sub ((cont r).intervalIntegrable ..) ((cont s).intervalIntegrable ..),←Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const bd).trans_eq
  rw [abs_of_nonneg (by linarith : 0≤1/H- -(1/H))]
  dsimp only [d]; ring

private theorem primeParameter_range (x : ℝ) (p : ℕ) : primeProbability x p∈Set.Icc 0 1 := by
  unfold primeProbability; constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by linarith)

private theorem primeParameter_order (p : ℕ) (hp : 1≤p) : Antitone (fun x=>primeProbability x p) := by
  have d (x : ℝ) := primeProbability_derivative x p hp
  apply antitone_of_deriv_nonpos (fun x=>(d x).differentiableAt)
  intro x
  rw [(d x).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (log_nonneg (by exact_mod_cast hp))) (primeParameter_range x p).1)
    (sub_nonneg.mpr (primeParameter_range x p).2)

/-- For two real saddles the weighted probability differences have one sign,
so the exact difference of saddle means bounds every insertion frequency. -/
theorem shiftedMass_saddle_change (J : Finset ℕ) (one : ∀ p∈J,1≤p) (α β H a : ℝ) (hp : 0<H) :
    let M := fun x=>shiftedMass J (primeProbability x) (fun p=>log p) H a
    |M α-M β|≤(4/H^2)*|saddleMean J α-saddleMean J β| := by
  intro M
  have ordered (x y : ℝ) (xy : x≤y) :
      (∑ p∈J, |Real.log (p:ℝ)| * |primeProbability x p-primeProbability y p|)=saddleMean J x-saddleMean J y := by
    unfold saddleMean; rw [←sum_sub_distrib]
    apply sum_congr rfl; intro p pm
    rw [abs_of_nonneg (log_nonneg (by exact_mod_cast one p pm)),
      abs_of_nonneg (sub_nonneg.mpr (primeParameter_order p (one p pm) xy))]; ring
  have step (x y : ℝ) (xy : x≤y) : |M x-M y|≤(4/H^2)*|saddleMean J x-saddleMean J y| := by
    have est := shiftedMass_parameter_change J (primeProbability x) (primeProbability y) (fun p=>log p) H a hp
      (fun p _=>primeParameter_range x p) (fun p _=>primeParameter_range y p)
    rw [ordered x y xy] at est
    exact est.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  rcases le_total α β with h|h
  · exact step α β h
  · rw [abs_sub_comm (M α),abs_sub_comm (saddleMean J α)]; exact step β α h

end
end Cogentic.Window
#print axioms Cogentic.Window.shiftedMass_parameter_change

#print axioms Cogentic.Window.shiftedMass_saddle_change

namespace Cogentic.Construction
open Real Window Finset
noncomputable section

private theorem power_step (q x y E : ℝ) (qp : 1≤q) (xe : q^x≤E) (ye : q^y≤E) :
    |q^x-q^y| ≤ E*log q*|x-y| := by
  have qpos := zero_lt_one.trans_le qp
  have h (a b : ℝ) (ab : a≤b) (be : q^b≤E) : |q^a-q^b|≤E*log q*|a-b| := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow_of_exponent_le qp ab)),
      abs_sub_comm a,abs_of_nonneg (sub_nonneg.mpr ab)]
    have id : q^a=q^b*exp (-(log q*(b-a))) := by
      rw [rpow_def_of_pos qpos,rpow_def_of_pos qpos,←exp_add]; congr 1; ring
    rw [id]
    have expo := add_one_le_exp (-(log q*(b-a)))
    have weighted := mul_le_mul_of_nonneg_left expo (rpow_nonneg qpos.le b)
    have enough := mul_le_mul_of_nonneg_right be (mul_nonneg (log_nonneg qp) (sub_nonneg.mpr ab))
    linarith only [weighted,enough]
  rcases le_total x y with xy|yx
  · exact h x y xy ye
  · rw [abs_sub_comm (q^x),abs_sub_comm x]; exact h y x yx xe

/-- Uniform variation of the complete normalized one- or two-hit insertion,
scaled by the larger of its two prime-power tilts. The coefficient depends
polynomially on the dimension, and is independent of the size of the cell. -/
theorem fullBandInsertion_saddle_control :
    ∃ b₀ : ℕ, ∀ b≥b₀, let H := log (Fixed.B b:ℝ); let J := primeBand b
    ∀ (Q : ℕ) (α β : ℝ), 0<Q → log Q≤2*H → 199/200≤α → 199/200≤β →
    let μ := saddleMean J
    let d := (Fixed.d b:ℝ)
    90*d≤μ α/H → μ α/H≤110*d → 90*d≤μ β/H → μ β/H≤110*d →
    let E := max ((Q:ℝ)^(1-α)) ((Q:ℝ)^(1-β))
    |fullBandInsertion b Q α|≤3*((Q:ℝ)^(1-α)) ∧
    |fullBandInsertion b Q α-fullBandInsertion b Q β| ≤
      E*((24+32*sqrt (110*d))/H)*|μ α-μ β| := by
  obtain ⟨b₁,low⟩ := fixed_central_mass_lower 0
  obtain ⟨_,_,b₂,ratio⟩ := fixed_central_insertions 0
  refine ⟨max 1 (max b₁ b₂),?_⟩
  intro b large H J Q α β qp qh aa bb μ d la ua lb ub E
  obtain ⟨bg,rest⟩ := max_le_iff.mp large
  obtain ⟨bl,br⟩ := max_le_iff.mp rest
  have dp : (1:ℝ)≤d := by dsimp only [d];exact_mod_cast (show 1≤Fixed.d b from Fixed.degree_pos bg)
  have bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos bg).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b))
  have natJ : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=J := by simp [J,primeBand]
  have pr (p : ℕ) (pm : p∈J) := (mem_primeBand.mp pm).1
  have one (p : ℕ) (pm : p∈J) : 1≤p := (pr p pm).one_le
  have band (p : ℕ) (pm : p∈J) : H/2≤log p ∧ log p≤H := by
    have ⟨_,top,bot⟩ := mem_primeBand.mp pm
    have ppos : (0:ℝ)<p := by exact_mod_cast (pr p pm).pos
    have lower := log_le_log (show 0<(Fixed.B b:ℝ) by exact_mod_cast bp) (by exact_mod_cast bot.le : (Fixed.B b:ℝ)≤(p:ℝ)^2)
    rw [log_pow] at lower
    norm_num only [Nat.cast_ofNat] at lower
    exact ⟨by dsimp only [H]; linarith,log_le_log ppos (by exact_mod_cast top)⟩
  have q1 : (1:ℝ)≤Q := by exact_mod_cast qp
  have shift : |log (Q:ℝ)|≤2*H := by rw [abs_of_nonneg (log_nonneg q1)];exact qh
  let M (x s : ℝ) := shiftedMass J (primeProbability x) (fun p=>log p) H s
  let G (x : ℝ) := M x (log Q)/M x 0
  let U := sqrt (110*d)
  have Upos : 0<U := sqrt_pos.mpr (by linarith)
  have center (x : ℝ) (ax : 199/200≤x) (lx : 90*d≤μ x/H) (ux : μ x/H≤110*d) :
      1/(2*H*U)≤M x 0 ∧ |G x|≤3 := by
    let u := μ x/H
    have up : 0<u := by dsimp only [u];linarith
    have eq : saddleMean J x=H*u := by dsimp only [u,μ]; field_simp
    have c := low b bl u x 0 ∅
    have r := ratio b br u x 0 0 (fun _=>∅)
    dsimp only at c r
    rw [natJ] at c r
    have nearby : |(0:ℝ)|≤H := by rw [abs_zero]; exact hp.le
    have size : (∅ : Finset ℕ).card≤b^0 := by simp
    have lower := c lx ux ax eq (by rw [abs_zero]; positivity) size (empty_subset _)
    have upper := (r lx ux ax eq nearby nearby (fun _ _=>size)).2.1 (log Q) shift
    have hz : 1/(2*H*U) ≤ 1/(2*H*sqrt u) := div_le_div_of_nonneg_left zero_le_one (by positivity)
      (mul_le_mul_of_nonneg_left (sqrt_le_sqrt ux) (by positivity))
    have om (s : ℝ) : omittedMass J ∅ (primeProbability x) (fun p=>log p) H s=M x s := by
      simp only [M,omittedMass,omittedCharacteristic,saddleCharacteristic,shiftedMass,notMem_empty,ite_false]
    rw [om] at lower
    rw [om,om] at upper
    exact ⟨hz.trans lower,upper.2⟩
  obtain ⟨αlo,gu⟩ := center α aa la ua
  obtain ⟨βlo,gv⟩ := center β bb lb ub
  have ma : 0<M α 0 := (by positivity : 0<1/(2*H*U)).trans_le αlo
  have mb : 0<M β 0 := (by positivity : 0<1/(2*H*U)).trans_le βlo
  let δ := |μ α-μ β|
  have dn : 0≤δ := abs_nonneg _
  have raw (s : ℝ) : |M α s-M β s|≤(4/H^2)*δ := shiftedMass_saddle_change J one α β H s hp
  have diff : |G α-G β|≤32*U/H*δ := by
    have ident : G α-G β=((M α (log Q)-M β (log Q))-G β*(M α 0-M β 0))/M α 0 := by
      dsimp only [G]; field_simp [ma.ne',mb.ne']; ring
    rw [ident,abs_div,abs_of_pos ma,div_le_iff₀ ma]
    apply (abs_sub ..).trans
    rw [abs_mul]
    have both := add_le_add (raw (log Q)) (mul_le_mul gv (raw 0) (abs_nonneg _) (by norm_num))
    have enough := mul_le_mul_of_nonneg_left αlo (show 0≤32*U/H*δ by positivity)
    apply both.trans
    exact (show (4/H^2)*δ+3*((4/H^2)*δ)=(32*U/H*δ)*(1/(2*H*U)) by field_simp; ring).le.trans enough
  have tilt (x y : ℝ) (xy : x≤y) (ax : 199/200≤x) (ly : 90*d≤μ y/H) : (y-x)*H≤4*(μ x-μ y)/H := by
    have lower := (saddle_displacement J x y H (by linarith) xy hp.le one band).1
    have uy : H≤μ y := (one_le_div hp).mp (by linarith)
    apply (le_div_iff₀ hp).mpr
    exact ((mul_le_mul_of_nonneg_left uy (mul_nonneg (sub_nonneg.mpr xy) hp.le))).trans (by linarith only [lower])
  have dist : |α-β| *H≤4*δ/H := by
    rcases le_total α β with ab|ba
    · rw [abs_sub_comm α,abs_of_nonneg (sub_nonneg.mpr ab)]
      exact (tilt α β ab aa lb).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) hp.le)
    · rw [abs_of_nonneg (sub_nonneg.mpr ba)]
      dsimp only [δ]; rw [abs_sub_comm (μ α)]
      exact (tilt β α ba bb la).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) hp.le)
  let A (x : ℝ) := (Q:ℝ)^(1-x)
  have dpow := power_step Q (1-α) (1-β) E q1 (le_max_left ..) (le_max_right ..)
  have add : |1-α-(1-β)|=|α-β| := by rw [show 1-α-(1-β)= -(α-β) by ring,abs_neg]
  rw [add] at dpow
  have en : 0≤E := (rpow_nonneg (Nat.cast_nonneg _) _).trans (le_max_left ..)
  have tbound : |A α-A β|≤E*(8/H*δ) := by
    apply dpow.trans
    have bq := mul_le_mul_of_nonneg_right qh (abs_nonneg (α-β))
    have inner : log (Q:ℝ)*|α-β|≤8/H*δ := calc
      _ ≤ 2*H*|α-β| := bq
      _ = 2*(|α-β| *H) := by ring
      _ ≤ 2*(4*δ/H) := mul_le_mul_of_nonneg_left dist (by norm_num)
      _ = _ := by ring
    exact (mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left inner en)
  refine ⟨?_,?_⟩
  · change |A α*G α|≤3*A α
    rw [abs_mul,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _ : 0≤A α)]
    exact (mul_le_mul_of_nonneg_left gu (rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq (mul_comm ..)
  change |A α*G α-A β*G β|≤_
  rw [show A α*G α-A β*G β=A α*(G α-G β)+(A α-A β)*G β by ring]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _ : 0≤A α)]
  have first := mul_le_mul (le_max_left (A α) (A β)) diff (abs_nonneg _) en
  have second := mul_le_mul tbound gv (abs_nonneg _) (by positivity)
  exact (add_le_add first second).trans_eq (by dsimp only [U,E,A,δ];ring)
/-- Uniform variation of the complete normalized one- or two-hit insertion,
scaled by the larger of its two prime-power tilts. The coefficient depends
polynomially on the dimension, and is independent of the size of the cell. -/
theorem fullBandInsertion_saddle_change :
    ∃ b₀ : ℕ, ∀ b≥b₀, let H := log (Fixed.B b:ℝ); let J := primeBand b
    ∀ (Q : ℕ) (α β : ℝ), 0<Q → log Q≤2*H → 199/200≤α → 199/200≤β →
    let μ := saddleMean J
    let d := (Fixed.d b:ℝ)
    90*d≤μ α/H → μ α/H≤110*d → 90*d≤μ β/H → μ β/H≤110*d →
    let E := max ((Q:ℝ)^(1-α)) ((Q:ℝ)^(1-β))
    |fullBandInsertion b Q α-fullBandInsertion b Q β| ≤
      E*((24+32*sqrt (110*d))/H)*|μ α-μ β| := by
  obtain ⟨b₀,h⟩ := fullBandInsertion_saddle_control
  refine ⟨b₀,?_⟩
  intro b hb H J Q α β qp cap aa bb μ d la ua lb ub E
  exact (h b hb Q α β qp cap aa bb la ua lb ub).2

end
end Cogentic.Construction
#print axioms Cogentic.Construction.fullBandInsertion_saddle_change

namespace Cogentic.Construction
open Real Window Finset
noncomputable section

private theorem fixed_insertion_tilt_bound (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b≥b₀, let H := log (Fixed.B b:ℝ); let d := (Fixed.d b:ℝ)
    ∀ (Q : ℕ) (x : ℝ), 0<Q → log Q≤2*H → x∈Set.Icc (199/200:ℝ) 1 →
    let u := saddleMean (primeBand b) x/H
    u≤110*d → (Q:ℝ)^(1-x)≤(1760*d+4)^4 := by
  obtain ⟨C,cp,tilt⟩ := fixed_saddle_euler_margin line
  obtain ⟨b₀,overhead⟩ := fixed_prime_overhead C cp 0
  refine ⟨max b₀ 1,?_⟩
  intro b big H d Q x qp qbound xwin u high
  obtain ⟨large,bp⟩ := max_le_iff.mp big
  have one : (1:ℝ)≤d := by dsimp only [d];exact_mod_cast (show 1≤Fixed.d b from Fixed.degree_pos bp)
  have bLarge : (16:ℝ)≤Fixed.B b := by
    have hz : 0<Fixed.h b := Nat.mul_pos (Fixed.degree_pos bp) (Nat.succ_pos _)
    exact_mod_cast (show 16≤2^(1000*Fixed.h b) from (by decide : 16≤2^4).trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hp : 0<H := log_pos (by linarith)
  have natJ : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=primeBand b := by simp [primeBand]
  have sm := overhead b large ∅ (by simp)
  simp only [card_empty,Nat.cast_zero,zero_mul,add_zero] at sm
  have base : 0<1760*d+4 := by linarith
  have lam : (1-x)*H≤2*log (1760*d+4) := by
    by_cases lt : 2≤(1-x)*H
    · have est := tilt (Fixed.B b) x u ∅ bLarge xwin.1 xwin.2 (sm.trans (by norm_num))
      dsimp only at est; rw [natJ] at est
      have eq : saddleMean (primeBand b) x=H*u := by dsimp only [u]; field_simp
      have lower := (est (empty_subset _) eq lt).2.1
      have un : 0≤u := by
        dsimp only [u,saddleMean];apply div_nonneg _ hp.le
        apply sum_nonneg;intro p pm
        exact mul_nonneg (by dsimp only [primeProbability];positivity) (log_nonneg (by exact_mod_cast (mem_primeBand.mp pm).1.one_le))
      exact lower.trans (mul_le_mul_of_nonneg_left (log_le_log (by linarith) (by linarith only [high] : 16*u+4≤1760*d+4)) (by norm_num))
    · have lg : 1≤log (1760*d+4) := (le_log_iff_exp_le base).mpr (by linarith only [one,exp_one_lt_d9])
      linarith
  have power : (Q:ℝ)^(1-x)≤exp (4*log (1760*d+4)) := by
    rw [rpow_def_of_pos (by exact_mod_cast qp : (0:ℝ)<Q)]
    exact exp_le_exp.mpr (by linarith only [lam,mul_le_mul_of_nonneg_right qbound (sub_nonneg.mpr xwin.2)])
  exact power.trans_eq (by rw [show 4*log (1760*d+4)=(4:ℕ)*log (1760*d+4) by norm_num,exp_nat_mul,exp_log base])

/-- On the actual integer mesh and any fixed target-part branch, a common
family of saddles has insertion variation controlled by the total variation
of the logarithms of the true oriented mean polynomial. The bound holds for
all one- or two-prime hit products simultaneously. -/
theorem actual_mark_insertion_variation (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (marks : ℕ→ℕ) (m : ℕ) (side : Bool) (D : ℝ), 1≤D → D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 →
    (∀ j ≤ m, marks j≤Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) (marks j)) →
    let d := (Fixed.d b:ℝ); let H := log (Fixed.B b:ℝ); let Y := fun j=>(exactMean n ell (marks j) side:ℝ)/D
    ∃ α : ℕ→ℝ, (∀ j ≤ m, α j∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) (α j)=log (Y j)) ∧
      ∀ Q : ℕ, 0<Q → log Q≤2*H →
      (∑ j∈range m, |fullBandInsertion b Q (α (j+1))-fullBandInsertion b Q (α j)|) ≤
        ((1760*d+4)^4*(24+32*sqrt (110*d))/H)*(∑ j∈range m,|log (Y (j+1))-log (Y j)|) := by
  classical
  obtain ⟨b₁,steps⟩ := fullBandInsertion_saddle_change
  obtain ⟨b₂,tilt⟩ := fixed_insertion_tilt_bound line
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  obtain ⟨b₄,wings⟩ := eventual_fixed_saddle_wings line 0 le_rfl 0
  refine ⟨max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell b large hn target marks m side D dl du mesh d H Y
  obtain ⟨one,two⟩ := max_le_iff.mp large
  obtain ⟨bst,bti⟩ := max_le_iff.mp one
  obtain ⟨bd,bw⟩ := max_le_iff.mp two
  have big := deg b bd
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b))
  have natJ : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=primeBand b := by simp [primeBand]
  have win j (ok : j ≤ m) := one_point_window hn big target (mesh j ok).1 (mesh j ok).2 side D ⟨dl,du⟩
  have point (j : ℕ) : ∃ x : ℝ, j ≤ m → x∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) x=log (Y j) := by
    by_cases ok : j ≤ m
    · have w := win j ok
      let u := log (Y j)/H
      have eq : log (Y j)=H*u := by dsimp only [u]; field_simp
      have lo : 90*d≤u := w.2.2.1
      have below : 80*d≤u := by have dn : 0≤d := Nat.cast_nonneg _;linarith
      have estimate := wings b bw u u (Y j) ∅ lo w.2.2.2.1 below (by simp) (zero_lt_one.trans_le w.2.1)
      dsimp only at estimate; rw [natJ] at estimate
      obtain ⟨x,xx,rate,_⟩ := estimate (empty_subset _) eq
      exact ⟨x,fun _=>⟨xx,rate.trans eq.symm⟩⟩
    · exact ⟨1,fun impossible=>(ok impossible).elim⟩
  choose α ha using point
  refine ⟨α,ha,?_⟩
  intro Q qp shift
  let A := (1760*d+4)^4
  have bounds j (ok : j ≤ m) : 90*d ≤ saddleMean (primeBand b) (α j)/H ∧ saddleMean (primeBand b) (α j)/H≤110*d := by
    rw [(ha j ok).2];exact ⟨(win j ok).2.2.1,(win j ok).2.2.2.1⟩
  have power j (ok : j ≤ m) : (Q:ℝ)^(1-α j)≤A := tilt b bti Q (α j) qp shift (ha j ok).1 (bounds j ok).2
  rw [mul_sum]
  apply sum_le_sum
  intro j jm
  have next := mem_range.mp jm
  have f := bounds j next.le
  have g := bounds (j+1) next
  have estimate := steps b bst Q (α (j+1)) (α j) qp shift (ha _ next).1.1 (ha _ next.le).1.1 g.1 g.2 f.1 f.2
  dsimp only at estimate
  rw [(ha _ next).2,(ha _ next.le).2] at estimate
  apply estimate.trans
  have maxBound := max_le (power (j+1) next) (power j next.le)
  have positive : 0≤(24+32*sqrt (110*d))/H := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right maxBound positive) (abs_nonneg _)).trans_eq (by dsimp only [A,d,H];ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.actual_mark_insertion_variation


namespace Cogentic.Construction
open Finset Real MeasureTheory Polynomial Set
noncomputable section

/-- The discrete variation of polynomial samples after any increasing change
of vertical scale. At each height, disjoint sample intervals crossing that
height give distinct roots of the shifted polynomial. -/
theorem polynomial_sample_variation (P : Polynomial ℝ) (x z : ℕ→ℝ) (F : ℝ→ℝ) (m : ℕ)
    (L U : ℝ) (xu : StrictMono x) (height : StrictMono F)
    (values : ∀ j ≤ m,P.eval (x j)=F (z j)) (bounded : ∀ j ≤ m,z j∈Icc L U) :
    (∑ j∈range m,|z (j+1)-z j|)≤P.natDegree*(U-L) := by
  classical
  let I (j : ℕ) := Ioo (min (z j) (z (j+1))) (max (z j) (z (j+1)))
  let w (j : ℕ) := (I j).indicator (fun _ : ℝ=>(1:ℝ))
  have lu := (bounded 0 (Nat.zero_le m)).1.trans (bounded 0 (Nat.zero_le m)).2
  have sets (j : ℕ) (jm : j < m) : I j⊆Set.Ioc L U := by
    intro t ht
    exact ⟨(le_min (bounded _ jm.le).1 (bounded _ jm).1).trans_lt ht.1,ht.2.le.trans
      (max_le (bounded _ jm.le).2 (bounded _ jm).2)⟩
  have usable (j : ℕ) : IntervalIntegrable (w j) volume L U := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le lu]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le lu).mp (intervalIntegrable_const (μ:=volume) (c:=(1:ℝ)))).indicator measurableSet_Ioo
  have mass (j : ℕ) (jm : j < m) : ∫ t in L..U,w j t=|z (j+1)-z j| := by
    change (∫ t in L..U,(I j).indicator (fun _ : ℝ=>(1:ℝ)) t)=_
    rw [intervalIntegral.integral_of_le lu,setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr (sets j jm),setIntegral_const,smul_eq_mul,mul_one]
    change volume.real (Ioo _ _)=_
    rw [Real.volume_real_Ioo_of_le (min_le_max ..),max_sub_min_eq_abs,abs_sub_comm]
  have crossed (t : ℝ) (j : ℕ) (jm : j < m) (cross : t∈I j) :
      ∃ a∈Ioo (x j) (x (j+1)),a∈(P-C (F t)).roots.toFinset := by
    have increasing := xu (Nat.lt_succ_self j)
    have c : ContinuousOn (fun a : ℝ=>P.eval a) (Icc (x j) (x (j+1))) := P.continuous.continuousOn
    have l := values j jm.le; have u := values (j+1) jm
    rcases le_total (z j) (z (j+1)) with up|down
    · change min _ _ < t ∧ t < max _ _ at cross
      rw [min_eq_left up,max_eq_right up] at cross
      obtain ⟨a,ax,e⟩ := intermediate_value_Ioo increasing.le c (show F t∈Ioo (P.eval (x j)) (P.eval (x (j+1))) by
        rw [l,u]; exact ⟨height cross.1,height cross.2⟩)
      refine ⟨a,ax,Multiset.mem_toFinset.mpr (mem_roots_sub_C'.mpr ⟨?_,e⟩)⟩
      intro pz;rw [pz,eval_C] at l; exact (height cross.1).ne l.symm
    · change min _ _ < t ∧ t < max _ _ at cross
      rw [min_eq_right down,max_eq_left down] at cross
      obtain ⟨a,ax,e⟩ := intermediate_value_Ioo' increasing.le c (show F t∈Ioo (P.eval (x (j+1))) (P.eval (x j)) by
        rw [l,u];exact ⟨height cross.1,height cross.2⟩)
      refine ⟨a,ax,Multiset.mem_toFinset.mpr (mem_roots_sub_C'.mpr ⟨?_,e⟩)⟩
      intro pz;rw [pz,eval_C] at u;exact (height cross.1).ne u.symm
  have count (t : ℝ) : (∑ j∈range m,w j t)≤(P.natDegree:ℝ) := by
    let S := (range m).filter (fun j=>t∈I j)
    have lift (j : ℕ) : ∃ a : ℝ, j∈S → a∈Ioo (x j) (x (j+1)) ∧ a∈(P-C (F t)).roots.toFinset := by
      by_cases h : j∈S
      · obtain ⟨a,ax,ep⟩ := crossed t j (mem_range.mp (mem_filter.mp h).1) (mem_filter.mp h).2
        exact ⟨a,fun _=>⟨ax,ep⟩⟩
      · exact ⟨0,fun k=>(h k).elim⟩
    choose a ha using lift
    have injective : (S : Set ℕ).InjOn a := by
      intro j hj k hk eq
      have neq (j k : ℕ) (hj : j∈S) (hk : k∈S) (lt : j<k) : a j<a k :=
        (ha j hj).1.2.trans_le (xu.monotone lt) |>.trans (ha k hk).1.1
      rcases lt_trichotomy j k with both|equal|both
      · exact ((neq j k hj hk both).ne eq).elim
      · exact equal
      · exact ((neq k j hk hj both).ne eq.symm).elim
    have size := card_le_card_of_injOn a (fun j h=>(ha j h).2) injective
    have card : S.card≤P.natDegree := size.trans (Multiset.toFinset_card_le _ |>.trans
      ((card_roots' _).trans ((natDegree_sub_le ..).trans (by simp))))
    change (∑ j∈range m,(I j).indicator (fun _ : ℝ=>(1:ℝ)) t)≤_
    simp only [Set.indicator_apply]
    change (∑ j∈range m, if t∈I j then (1:ℝ) else 0)≤_
    rw [Finset.sum_boole (fun j=>t∈I j) (range m)]
    exact_mod_cast card
  have sums (S : Finset ℕ) : IntervalIntegrable (fun t=>∑ j∈S,w j t) volume L U := by
    induction S using Finset.induction_on with
    | empty => simp only [sum_empty]; exact intervalIntegrable_const
    | insert j S jp ih => simp only [sum_insert jp];exact (usable j).add ih
  calc
    _ = ∑ j∈range m,∫ t in L..U,w j t := sum_congr rfl (fun j jm=>(mass j (mem_range.mp jm)).symm)
    _ = ∫ t in L..U,∑ j∈range m,w j t := (intervalIntegral.integral_finsetSum (fun j _=>usable j)).symm
    _ ≤ ∫ _ in L..U,(P.natDegree:ℝ) := intervalIntegral.integral_mono_on lu
      (sums _) intervalIntegrable_const (fun t _=>count t)
    _ = _ := by simp [mul_comm]

end
end Cogentic.Construction
#print axioms Cogentic.Construction.polynomial_sample_variation

namespace Cogentic.Construction
open Real Window Finset Polynomial
noncomputable section

private theorem mean_square_eval (n ell a : ℕ) (side : Bool) :
    let cs := meanPolynomial n ell side
    (((Marking.polynomial cs).map (Int.castRingHom ℝ))^2).eval (a:ℝ)=(exactMean n ell a side:ℝ)^2 := by
  intro cs
  have ev (l : List ℤ) : ((Marking.polynomial l).map (Int.castRingHom ℝ)).eval (a:ℝ)=
      ((Construction.eval (a:ℤ) l:ℤ):ℝ) := by
    induction l with
    | nil => simp [Marking.polynomial,Construction.eval]
    | cons x l ih => simp [Marking.polynomial,Construction.eval,ih]
  have norm := normalized_at_mark (A:=Fixed.A (n.log2+1)) (Nat.pow_pos (by decide)) a cs
  rw [eval_pow,ev]; unfold exactMean
  change _=(((orientation n a side*RootLogs.normalized (Fixed.A (n.log2+1)) cs ((a:ℚ)/Fixed.A (n.log2+1)):ℚ):ℝ))^2
  rw [norm]; push_cast
  unfold orientation
  split_ifs <;> push_cast <;> ring

/-- On every entire constructor cell, the actual one- or two-hit full-band
insertion has polynomially bounded endpoint size and total variation. This
holds at every integer mesh point for each fixed target-part value, before
eligibility and ordinary residue masks are imposed. -/
theorem constructor_cell_insertion_total_variation (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (side : Bool) (D : ℝ), 1≤D → D≤(Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 →
    let L := firstCellMark b cell; let M := cellMarkCount b
    let H := log (Fixed.B b:ℝ); let d := (Fixed.d b:ℝ); let Y := fun j=>(exactMean n ell (L+j) side:ℝ)/D
    ∃ α : ℕ→ℝ, (∀ j < M, α j∈Set.Icc (199/200:ℝ) 1 ∧ saddleMean (primeBand b) (α j)=log (Y j)) ∧
      ∀ Q : ℕ, 0<Q → log Q≤2*H →
      (∀ j < M, |fullBandInsertion b Q (α j)|≤3*(1760*d+4)^4) ∧
      (∑ j∈range (M-1), |fullBandInsertion b Q (α (j+1))-fullBandInsertion b Q (α j)|) ≤
        40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d)) := by
  obtain ⟨b₁,var⟩ := actual_mark_insertion_variation line
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 10004
  obtain ⟨b₃,control⟩ := fullBandInsertion_saddle_control
  obtain ⟨b₄,tilt⟩ := fixed_insertion_tilt_bound line
  refine ⟨max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell b big hn target cell side D dl du L M H d Y
  obtain ⟨two,more⟩ := max_le_iff.mp big
  obtain ⟨bv,bd⟩ := max_le_iff.mp two
  obtain ⟨bc,bt⟩ := max_le_iff.mp more
  have large := deg b bd
  let m := M-1
  have mp : 0<M := Nat.pow_pos (by decide)
  have d0 := Fixed.degree_pos (Nat.succ_pos n.log2)
  have hp : 0<H := log_pos (by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero d0.ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b))
  have mesh (j : ℕ) (jm : j ≤ m) : L+j≤Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) (L+j) := by
    apply (fixed_grid_interval d0 cell (L+j) ?_).2
    apply Finset.mem_Ico.mpr
    have ltM : j < M := by dsimp only [m] at jm;omega
    exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left ltM _⟩
  have w (j : ℕ) (jm : j ≤ m) := one_point_window hn large target (mesh j jm).1 (mesh j jm).2 side D ⟨dl,du⟩
  have rangeY (j : ℕ) (jm : j ≤ m) : log (Y j)∈Set.Icc (90*d*H) (110*d*H) :=
    ⟨(le_div_iff₀ hp).mp (w j jm).2.2.1,(div_le_iff₀ hp).mp (w j jm).2.2.2.1⟩
  have Dpos : 0<D := zero_lt_one.trans_le dl
  let cs := meanPolynomial n ell side
  let P : ℝ[X] := ((Marking.polynomial cs).map (Int.castRingHom ℝ))^2
  have degree : P.natDegree≤2*Fixed.d b := by
    have len : cs.length=Fixed.d b+1 :=
      (shape (ell:=ell) (by omega : 3≤Fixed.d b) side (b^2*Fixed.U b*Fixed.A b) (b^2*Fixed.U b)).1
    have cap : (Marking.polynomial cs).natDegree≤Fixed.d b := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      have eq := coefficient_rep (R:=ℤ) cs j
      simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : cs.length≤j)] using eq
    dsimp only [P]; rw [natDegree_pow]
    exact Nat.mul_le_mul_left _ (natDegree_map_le.trans cap)
  let F := fun t : ℝ=>D^2*exp (2*t)
  have inc : StrictMono F := by
    intro t v tv; apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos Dpos)
    exact exp_lt_exp.mpr (by linarith)
  let x := fun j : ℕ=>(↑(L+j):ℝ)
  have growing : StrictMono x := fun _ _ h=>by dsimp only [x];exact_mod_cast Nat.add_lt_add_left h L
  have identity (j : ℕ) (jm : j ≤ m) : P.eval (x j)=F (log (Y j)) := by
    rw [show P.eval (x j)=(exactMean n ell (L+j) side:ℝ)^2 from mean_square_eval ..]
    have yp := zero_lt_one.trans_le (w j jm).2.1
    dsimp only [F]
    rw [show 2*log (Y j)=log (Y j)+log (Y j) by ring,exp_add,exp_log (show 0<Y j from yp)]
    dsimp only [Y]; field_simp
  have logVar := polynomial_sample_variation P x (fun j=>log (Y j)) F m (90*d*H) (110*d*H) growing inc identity rangeY
  obtain ⟨α,ha,all⟩ := var bv hn target (fun j=>L+j) m side D dl du mesh
  have aj (j : ℕ) (jm : j < M) := ha j (show j ≤ m by dsimp only [m];omega)
  refine ⟨α,aj,?_⟩
  intro Q qp qh
  have point (j : ℕ) (jm : j < M) : |fullBandInsertion b Q (α j)|≤3*(1760*d+4)^4 := by
    have ok : j ≤ m := by dsimp only [m];omega
    have a := aj j jm
    have lo : 90*d ≤ saddleMean (primeBand b) (α j)/H := a.2 ▸ (w j ok).2.2.1
    have hi : saddleMean (primeBand b) (α j)/H≤110*d := a.2 ▸ (w j ok).2.2.2.1
    have small := (control b bc Q (α j) (α j) qp qh a.1.1 a.1.1 lo hi lo hi).1
    exact small.trans (mul_le_mul_of_nonneg_left (tilt b bt Q (α j) qp qh a.1 hi) (by norm_num))
  refine ⟨point,?_⟩
  have factor : 0≤(1760*d+4)^4*(24+32*sqrt (110*d))/H := by positivity
  have gap : 0 ≤ 110*d*H-90*d*H := by
    have dn : 0≤d := Nat.cast_nonneg _
    nlinarith only [mul_nonneg dn hp.le]
  have degreeR : (P.natDegree:ℝ)≤2*d := by dsimp only [d];exact_mod_cast degree
  have vis := all Q qp qh
  exact vis.trans ((mul_le_mul_of_nonneg_left (logVar.trans (mul_le_mul_of_nonneg_right degreeR gap)) factor).trans_eq (by field_simp;ring))

end
end Cogentic.Construction
#print axioms Cogentic.Construction.constructor_cell_insertion_total_variation
