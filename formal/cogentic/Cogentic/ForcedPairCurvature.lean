import Cogentic.ForcedMarginalRatios
import Cogentic.FullPairCovariance

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

/-- One- and two-prime insertion atoms for the actual prescribed coefficient
laws. Removing the leading hit powers leaves the negative rank-one
curvature term at the same mark saddle as both individual insertions. -/
theorem forced_pair_curvature (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let J := primeBand b; let H := log (Fixed.B b)
    let y := (exactMean n ell a side:ℝ)/targetPart n ell a side; let u := log y/H
    let O := PrescribedRows.unrestricted n ell
    let P := fun R : PrescribedRows n ell => prescribedProbability R side
      (fun k=>supportedValue (sieveBand n ell (R.prefactor a side)) (R.intercept a side k.1 k.2))
    ∃ α∈Set.Icc (199/200:ℝ) 1, saddleMean J α=log y ∧ 0<P O ∧
      ∀ (p q : ℕ) (Rp Rq Rpq : PrescribedRows n ell), p∈J → q∈J → p≠q →
      Rp.hitProduct a=p → Rq.hitProduct a=q → Rpq.hitProduct a=p*q →
      let t := fun R : PrescribedRows n ell => (P R/P O)/(R.hitProduct a:ℝ)^(1-α)
      let V := saddleVariance J (primeProbability α) (fun r=> log r)
      |t Rp-1|≤60/u ∧ |t Rq-1|≤60/u ∧
        |t Rpq-t Rp*t Rq*(1-log p*log q/V)|≤C/u^2 := by
  classical
  obtain ⟨A,ap,b₁,ratios⟩ := forced_marginal_ratio line 400 (by norm_num)
  obtain ⟨C,cp,b₂,central⟩ := fixed_central_insertions 3
  obtain ⟨b₃,del⟩ := fixed_prime_deletions 3
  obtain ⟨b₄,deg⟩ := Fixed.degree_grows (max 10004 ⌈A⌉₊)
  refine ⟨C+600,by positivity,max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell a b huge hn comp target absent mark side J H y u O P
  obtain ⟨one,two⟩ := max_le_iff.mp (max_le_iff.mp huge).1
  obtain ⟨three,four⟩ := max_le_iff.mp (max_le_iff.mp huge).2
  obtain ⟨α,ha,mean,po,actual⟩ := ratios one hn comp target absent mark side
  refine ⟨α,ha,mean,po,?_⟩
  intro p q Rp Rq Rpq pm qm ne pp qq pq t V
  let B : ℝ := Fixed.B b
  let band := fun R : PrescribedRows n ell => (sieveBand n ell (R.prefactor a side)).filter
    (fun k=>¬k∣(firstStep n ell a side).natAbs)
  let omitted := fun R : PrescribedRows n ell=>J\band R
  let E := fun R : PrescribedRows n ell=>eulerMass (band R) α
  have big := (le_max_left (a:=10004) (b:=⌈A⌉₊)).trans (deg b four)
  have bigA : A≤(Fixed.d b:ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast (le_max_right (a:=10004) (b:=⌈A⌉₊)).trans (deg b four))
  have ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have op : O.hitProduct a=1 := by simp [O,PrescribedRows.unrestricted,PrescribedRows.hitProduct,PrescribedRows.hit,prodPrimes]
  have tp : O.prefactor a side=targetPart n ell a side := by simp [PrescribedRows.prefactor,op]
  have div := total_prefactor O side target (g:=1) (a:=a) (by decide)
    (show 1≤Fixed.A b*(Fixed.B b)^2 from Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide))))
  rw [tp,Nat.cast_one,mul_one] at div
  have win := one_point_window hn big target cap grid side _ div
  have lo : 90*(Fixed.d b:ℝ)≤u := win.2.2.1
  have hi : u≤110*(Fixed.d b:ℝ) := win.2.2.2.1
  have bg : (Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime=J := by simp [B,J,primeBand]
  have primeInfo := del b three u α lo hi ha.1
  change 0<H ∧ 2≤u ∧ _ at primeInfo
  obtain ⟨hp,ul,_,_,tiny,rb,_⟩ := primeInfo
  rw [bg] at rb
  have mag : H*u=log y := by dsimp only [u]; field_simp
  have dr : (10004:ℝ)≤Fixed.d b := by exact_mod_cast big
  have u10 : 100≤u := by linarith only [lo,dr]
  have up : 0<u := by linarith only [ul]
  have u4 : 4≤u := by linarith only [u10]
  have expBound := exponential_to_covariance b up (by linarith only [bigA,lo,dr] : A≤u) hi
  have onepow : 1/u^2≤1/u := div_le_div_of_nonneg_left zero_le_one up
    (by nlinarith only [mul_le_mul_of_nonneg_right (by linarith only [ul] : 1≤u) up.le])
  have five_two : 1/u^5≤1/u^2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_right₀ (by linarith only [ul]) (by decide))
  have omittedCard (R : PrescribedRows n ell) : (omitted R).card≤b^3 := by
    obtain ⟨s,v,ok,_⟩ := R.first_probability ((by decide : 3≤10004).trans big) target cap (mark_range hn big cap) side
    obtain ⟨_,_,ready⟩ := first_polynomial_data R hn big comp target absent mark side s v ok
    exact omitted_card hn big comp target absent ready.prepos ready.prebound (Int.natAbs_pos.mpr ready.nonzero) ready.cap
  have sub (R : PrescribedRows n ell) : band R⊆band O := by
    intro x hx
    obtain ⟨h,slope⟩ := mem_filter.mp hx
    obtain ⟨inJ,markMod,unforced⟩ := mem_filter.mp h
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨inJ,markMod,?_⟩,slope⟩
    rw [tp]
    exact fun bad=>unforced (dvd_mul_of_dvd_left bad _)
  have euler (R : PrescribedRows n ell) : 0≤E R/E O ∧ E R/E O≤1 ∧ 1-E R/E O≤1/u^2 := by
    obtain ⟨en,el,loss⟩ := euler_ratio_loss (band O) (band R) (sub R) α
    have diff : band O\band R ⊆ omitted R := fun x h => mem_sdiff.mpr
      ⟨(mem_filter.mp (mem_filter.mp (mem_sdiff.mp h).1).1).1,(mem_sdiff.mp h).2⟩
    have ct : ((band O\band R).card:ℝ)≤(b:ℝ)^3 := by exact_mod_cast (card_le_card diff).trans (omittedCard R)
    have bound := sum_le_sum (s:=band O\band R) (g:=fun _ =>B^(-199/400:ℝ)) (fun k hk => (rb k (mem_sdiff.mp (diff hk)).1).1)
    rw [sum_const,nsmul_eq_mul] at bound
    exact ⟨en,el,loss.trans (bound.trans ((mul_le_mul_of_nonneg_right ct (rpow_nonneg (Nat.cast_nonneg _) _)).trans (tiny.trans five_two)))⟩
  let h := log (p:ℝ); let j := log (q:ℝ)
  have pp' := (mem_primeBand.mp pm).1
  have qq' := (mem_primeBand.mp qm).1
  have hp' : 0<h := log_pos (by exact_mod_cast pp'.one_lt)
  have hq' : 0<j := log_pos (by exact_mod_cast qq'.one_lt)
  have hj : h≠j := by
    intro same; apply ne
    have pr : (0:ℝ)<p := by exact_mod_cast pp'.pos
    have qr : (0:ℝ)<q := by exact_mod_cast qq'.pos
    exact_mod_cast (log_injOn_pos pr qr same)
  let law := fun x : ℝ => if x=h+j then Rpq else if x=h then Rp else if x=j then Rq else O
  let f := fun x : ℝ => omittedMass J (omitted (law x)) (primeProbability α) (fun p=>log p) H x
  let g := fun x : ℝ => t (law x)*f 0
  have hh : |h|≤H := (abs_of_pos hp').symm ▸ (rb p pm).2.2
  have jj : |j|≤H := (abs_of_pos hq').symm ▸ (rb q qm).2.2
  have l0 : law 0=O := by simp [law,ne_of_lt hp',ne_of_lt hq',show 0≠h+j by linarith]
  have lh : law h=Rp := by simp [law,show h≠h+j by linarith]
  have lj : law j=Rq := by simp [law,show j≠h+j by linarith,hj.symm]
  have ls : law (h+j)=Rpq := by simp [law]
  let U : Finset ℝ := {0,h,j,h+j}
  have shift (x : ℝ) (inU : x∈U) : log ((law x).hitProduct a:ℝ)=x := by
    simp only [U,mem_insert,mem_singleton] at inU
    rcases inU with rfl|rfl|rfl|rfl
    · simp [l0,op]
    · simp [lh,pp,h]
    · simp [lj,qq,j]
    · rw [ls,pq,Nat.cast_mul,log_mul (by exact_mod_cast pp'.ne_zero) (by exact_mod_cast qq'.ne_zero)]
  have maxShift (x : ℝ) (hx : x∈U) : |x|≤2*H := by
    simp only [U,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · rw [abs_zero]; positivity
    · linarith
    · linarith
    · exact (abs_add_le ..).trans (by linarith)
  change (Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime=J at bg
  have integr := central b two u α h j (fun x=>omitted (law x)) lo hi ha.1 (by rw [bg]; exact mean.trans mag.symm) hh jj
    (fun x _ =>omittedCard (law x))
  rw [bg] at integr
  change 0<f 0 ∧ (∀ x : ℝ, |x|≤2*H → |f x/f 0-1|≤36/u ∧ |f x/f 0|≤3) ∧
    |f (h+j)/f 0-(f h/f 0)*(f j/f 0)*(1-h*j/V)| ≤ C/u^2 at integr
  have fpos (x) (inU : x∈U) : 0<f x := by
    have low := (abs_le.mp (integr.2.1 x (maxShift x inU)).1).1
    have ls : 36/u<1 := (div_lt_one up).mpr (by linarith only [u10])
    exact (div_pos_iff_of_pos_right integr.1).mp (by linarith only [ls,low])
  have cent (x) (inU : x∈U) : (law x).forcedCentralFactor a side α=E (law x)*f x := by
    dsimp only [PrescribedRows.forcedCentralFactor]
    rw [shift x inU]
  have base : O.forcedCentralFactor a side α=E O*f 0 := by simpa only [l0] using cent 0 (by simp [U])
  have near (x : ℝ) (inU : x∈U) : |g x/f x-1|≤2/u^2 := by
    let R := law x; let Q := (R.hitProduct a:ℝ)^(1-α)
    let Φ := Q*(R.forcedCentralFactor a side α/O.forcedCentralFactor a side α)
    let v := (P R/P O)/Φ; let er := E R/E O
    have Rpos : 0<Q := rpow_pos_of_pos (by exact_mod_cast (R.subprod_bounds (s:=R.hit a) (filter_subset ..)).1) _
    have fR := fpos x inU
    have eO := eulerMass_pos (band O) α; have eR := eulerMass_pos (band R) α
    have z := actual R
    change 0<Φ ∧ |v-1|≤A*exp (-400*(Fixed.z b:ℝ)^2) at z
    have id : g x/f x=v*er := by
      dsimp only [g,t,v,Φ,er]
      change ((P R/P O)/Q*f 0)/f x=((P R/P O)/(Q*(R.forcedCentralFactor a side α/O.forcedCentralFactor a side α)))*(E R/E O)
      rw [cent x inU,base]
      change 0<E O at eO; change 0<E R at eR
      change ((P R/P O)/Q*f 0)/f x=((P R/P O)/(Q*((E R*f x)/(E O*f 0))))*(E R/E O)
      field_simp [eO.ne',eR.ne',fR.ne',integr.1.ne',po.ne',Rpos.ne']
    have e := euler R
    have ez : |er-1|≤1/u^2 := by rw [abs_of_nonpos (sub_nonpos.mpr e.2.1)]; linarith only [e.2.2]
    rw [id,show v*er-1=(v-1)*er+(er-1) by ring]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul,abs_of_nonneg e.1]
    have me := mul_le_mul (z.2.trans expBound) e.2.1 e.1 (by positivity : 0≤1/u^2)
    change |v-1| *er+|er-1|≤2/u^2
    exact (add_le_add (me.trans_eq (mul_one _)) ez).trans_eq (by ring)
  have variance := (prime_saddle_variance_bounds J α H (by linarith only [ha.1]) hp.le
    (fun k hx => (mem_primeBand.mp hx).1.one_le) (fun k hx => (rb k hx).2)).1
  rw [mean,←mag] at variance
  change H*(H*u)/4≤V at variance
  have vp : 0<V := (by positivity : 0<H*(H*u)/4).trans_le variance
  have hv : |h*j/V|≤1 := by
    rw [abs_div,abs_mul,abs_of_pos vp,div_le_one vp]
    exact (mul_le_mul hh jj (abs_nonneg _) hp.le).trans (by
      nlinarith only [variance,mul_le_mul_of_nonneg_left u4 (sq_nonneg H)])
  have curve : |1-h*j/V|≤2 := abs_le.mpr ⟨by linarith only [(abs_le.mp hv).2],by linarith only [(abs_le.mp hv).1]⟩
  have short : 2/u^2≤1/2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith only [u4,sq_nonneg (u-2)])
  obtain ⟨_,dh,dj,dx⟩ := transfer_four_ratios f g h j (1-h*j/V) (2/u^2) (C/u^2) short (by positivity) curve
    fpos near (fun x hx=>(integr.2.1 x (maxShift x (mem_insert_of_mem hx))).2) integr.2.2
  have unit : t O=1 := by dsimp only [t]; rw [op,Nat.cast_one,one_rpow,div_self po.ne',div_one]
  have lawT (x) : g x/g 0=t (law x) := by dsimp only [g]; rw [l0,unit,one_mul,mul_div_cancel_right₀ _ integr.1.ne']
  rw [lawT,lh] at dh
  rw [lawT,lj] at dj
  rw [lawT,lawT,lawT,ls,lh,lj] at dx
  have single (x z : ℝ) (hx : |x|≤2*H) (err : |z-f x/f 0|≤12*(2/u^2)) : |z-1|≤60/u := by
    apply (abs_sub_le _ (f x/f 0) _).trans
    have m : 12*(2/u^2)≤24*(1/u) := (show 12*(2/u^2)=24*(1/u^2) by ring).trans_le
      (mul_le_mul_of_nonneg_left onepow (by norm_num))
    exact (add_le_add (err.trans m) (integr.2.1 x hx).1).trans_eq (by ring)
  exact ⟨single h _ (by linarith) dh,single j _ (by linarith) dj,dx.trans_eq (by ring)⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.forced_pair_curvature
