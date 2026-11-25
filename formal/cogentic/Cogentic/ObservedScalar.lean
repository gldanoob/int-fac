import Cogentic.ConditionalTransfer
import Cogentic.PolynomialRelative

namespace Cogentic.Construction
open Real Cogentic.Window

private theorem relative_model_transfer (Z : ℂ) (A F G C e : ℝ) (ap : 0<A) (fp : 0<F)
    (cp : 0≤C) (ep : 0≤e) (small : e≤1) (changeModel : |G/F-1|≤e)
    (approximation : ‖Z-((A*G:ℝ):ℂ)‖≤ C*(A*G)*e) :
    ‖Z-((A*F:ℝ):ℂ)‖ ≤ (2*C+1)*(A*F)*e := by
  have err := changeModel
  rw [←div_self fp.ne' (a:=F),←sub_div,abs_div,abs_of_pos fp,div_le_iff₀ fp] at err
  have cap : G≤2*F := by linarith only [(abs_le.mp err).2,mul_le_mul_of_nonneg_right small fp.le]
  have diff : ‖((A*G:ℝ):ℂ)-((A*F:ℝ):ℂ)‖ ≤ A*(e*F) := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,←mul_sub,abs_mul,abs_of_pos ap]
    exact mul_le_mul_of_nonneg_left err ap.le
  have u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cap ap.le) cp) ep
  have tri := norm_add_le (Z-((A*G:ℝ):ℂ)) (((A*G:ℝ):ℂ)-((A*F:ℝ):ℂ))
  rw [sub_add_sub_cancel] at tri
  apply tri.trans
  linarith only [approximation,diff,u]

/-- The second-coordinate scalar probability is controlled by the true
    nominal mark center. On the reduced branch the main term is independent
    of the observed first coordinate. -/
theorem observed_second_scalar (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1≤K) :
    ∃ C : ℝ, 0<C ∧ ∃ n₀ : ℕ, ∀ {n ell a a' : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    n₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a≤Fixed.A b → a'∈(construct n ell 0 0 0 0).marks →
    (Fixed.A b:ℝ) ≤ |(a':ℝ)-a| * (dyadicUnit b:ℝ)^50 →
    ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let obs := (u:ℝ)+(a:ℝ)*(v:ℝ)
    |obs-lineCenter n a|≤(b:ℝ)^3*projectionScale n a →
    let c := R.intercept a' side u v
    let s := R.secondStep a a' side
    let g := commonDivisor c s
    let pre := R.prefactor a' side
    let J := sieveBand n ell pre
    let band := J.filter (fun p=>¬p∣s.natAbs)
    let H := log (Fixed.B b)
    let D := primeBand b\band
    let q := s.natAbs/g
    let Y := (exactMean n ell a' side:ℝ)/((pre:ℝ)*g)
    let Z := conditionalMean n ell a a' side obs
    let S := twoWidth n ell a a'
    let P := scalarMass J c s (Z/pre) (S/pre)
    (g∉squarefreeSupport J → P=0) ∧
    (g∈squarefreeSupport J → ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean (primeBand b) α=log Y ∧
      let model := ((q:ℝ)/q.totient)*Y^(α-1)*eulerMass band α*
        omittedMass (primeBand b) D (primeProbability α) (fun p=>log p) H 0
      0 < model ∧ ‖(2*π:ℝ) • P-(model:ℂ)‖ ≤ C*model*exp (-K*(Fixed.z b:ℝ)^2)) := by
  obtain ⟨C,cp,n₁,relative⟩ := scalar_progression_relative line K hK
  obtain ⟨n₂,transfer⟩ := observed_density_transfer 3 K hK
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 50000
  refine ⟨2*C+1,by positivity,max n₁ (max n₂ n₃),?_⟩
  intro n ell a a' R b huge hn comp target absent cap mark clean side u v ok obs bulk c s g pre J band H D q Y Z S P
  obtain ⟨one,t⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp t
  have db := deg b three
  have big : 10004≤Fixed.d b := by omega
  obtain ⟨_,cap',grid',_⟩ := (constructed_marks_iff n ell 0 0 0 0 a').mp mark
  obtain ⟨_,bound,_,ready⟩ := second_polynomial_data R hn big comp target absent cap mark clean side u v ok bulk
  change ScalarReady n pre c s Z S at ready
  have sp := Int.natAbs_pos.mpr ready.nonzero
  have gp : 0<g := Nat.gcd_pos_of_pos_right _ sp
  have fb := total_prefactor R side target gp bound (a:=a')
  let Q := (pre:ℝ)*g
  have qpos : 0<Q := mul_pos (by exact_mod_cast ready.prepos) (by exact_mod_cast gp)
  let U := log Y/H
  have win := one_point_window hn big target cap' grid' side Q fb
  have HH := (fixed_band_log_bounds b (Nat.succ_pos _) (by omega)).1
  change 1000*(Fixed.d b:ℝ)≤H at HH
  have dr : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast db
  have hH : 1≤H := by linarith only [HH,dr]
  have hp : 0<H := by linarith only [hH]
  have hu : H*U=log Y := by dsimp [U]; field_simp
  obtain ⟨_,_,drift⟩ := conditional_log_drift hn big target cap cap' grid' side obs Q qpos bulk
  have ⟨xx,_,_,_,_,_,_⟩ := dyadic_data (b:=b) (Nat.succ_pos _)
  have x2 : (2:ℝ)≤dyadicUnit b := by exact_mod_cast xx
  have xp : (0:ℝ)<dyadicUnit b := by linarith
  have little : (2:ℝ)/(dyadicUnit b:ℝ)^95 ≤ 1 := (div_le_one (by positivity)).mpr
    (x2.trans (le_self_pow₀ (by linarith) (by decide)))
  have off : |H*U-log (Z/Q)| ≤ 2*H := by
    rw [hu,abs_sub_comm]
    exact drift.trans (little.trans (by linarith))
  obtain ⟨zero,hit⟩ := relative c s Z S U one hn comp target absent ready.prepos ready.prebound
    ready.nonzero ready.cap ready.width ready.window win.2.2.1 win.2.2.2.1 off
  refine ⟨zero,?_⟩
  intro supported
  obtain ⟨α,ha,mean,mp,est⟩ := hit supported
  have ms : saddleMean (primeBand b) α=log Y := mean.trans hu
  have dc := omitted_card hn big comp target absent ready.prepos ready.prebound sp ready.cap
  have subBand : band⊆primeBand b := fun p z => (Finset.mem_filter.mp (Finset.mem_filter.mp z).1).1
  have bandEq : primeBand b\D=band := Finset.sdiff_sdiff_eq_self subBand
  have dsub : D⊆primeBand b := Finset.sdiff_subset
  obtain ⟨pos,changeModel⟩ := transfer two hn target cap cap' grid' side obs Q α D bulk fb ha.1 ha.2 ms dc dsub
  let A := (q:ℝ)/q.totient
  let F := centralDensity (primeBand b) D H U α Y
  let G := centralDensity (primeBand b) D H U α (Z/Q)
  let e := exp (-K*(Fixed.z b:ℝ)^2)
  have fp : 0<F := pos
  have divq : g∣s.natAbs := (gcd_dvd_intercept c s ready.nonzero).2
  have qp : 0<q := Nat.div_pos (Nat.le_of_dvd sp divq) gp
  have ap : 0<A := div_pos (by exact_mod_cast qp) (by exact_mod_cast Nat.totient_pos.mpr qp)
  have observed : ‖(2*π:ℝ) • P-(↑(A*G):ℂ)‖ ≤ C*(A*G)*e := by
    dsimp only [G,centralDensity]; rw [bandEq]
    simpa only [mul_assoc] using est
  have ep : e≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have final := relative_model_transfer ((2*π:ℝ) • P) A F G C e ap fp cp.le (exp_pos _).le ep changeModel observed
  refine ⟨α,ha,ms,?_⟩
  have fe : A*F = A*Y^(α-1)*eulerMass band α*
      omittedMass (primeBand b) D (primeProbability α) (fun p=>log p) H 0 := by
    dsimp only [F,centralDensity]
    rw [bandEq,hu,sub_self]; ring
  rw [←fe]
  exact ⟨mul_pos ap fp,final⟩

end Cogentic.Construction
