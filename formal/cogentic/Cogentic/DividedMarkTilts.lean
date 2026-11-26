import Cogentic.MarkTilts
import Cogentic.CellAtomVariation
import Cogentic.FixedPairCovariance
import Cogentic.Rank

namespace Cogentic.Construction

open Real Window
noncomputable section

private theorem band_one_lt {b : ℕ} (bp : 0<b) : 1<(Fixed.B b:ℝ) := by
  exact_mod_cast (Nat.one_lt_pow (Nat.mul_ne_zero (by decide)
    (Nat.mul_ne_zero (Fixed.degree_pos bp).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)

private theorem band_log_interval {p b : ℕ} (bp : 0<b) (pm : p∈primeBand b) :
    log (Fixed.B b)/2≤log p ∧ log p≤log (Fixed.B b) := by
  obtain ⟨pp,cap,low⟩ := mem_primeBand.mp pm
  have l := log_le_log (zero_lt_one.trans (band_one_lt bp)) (show (Fixed.B b:ℝ)≤(p:ℝ)^2 by exact_mod_cast low.le)
  rw [log_pow] at l
  exact ⟨by norm_num at l; linarith,log_le_log (by exact_mod_cast pp.pos) (by exact_mod_cast cap)⟩

/-- The saddle used for a prescribed marginal, after removing the target
factor when this mark is in a target class. -/
def dividedLogCenter (n ell a : ℕ) (side : Bool) : ℝ :=
  log ((exactMean n ell a side : ℝ) / targetPart n ell a side)

/-- Uniform range of the logarithmic center after fixing a target branch. -/
def InMarkSaddleRange (n : ℕ) (Y : ℝ) : Prop :=
  let b := n.log2+1; let H := log (Fixed.B b)
  H*(90*(Fixed.d b:ℝ)) ≤ Y ∧ Y ≤ H*(110*(Fixed.d b:ℝ)) ∧
    log (amplitude n)-201*H/200 ≤ Y ∧ Y ≤ log (amplitude n)+H/200

/-- The full integer mesh on either target branch has the same range, including
positions removed by the constructor's sieve or belonging to the other branch. -/
theorem grid_center_range {n ell a : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (t : ℝ) (tr : 1≤t) (lim : t≤Fixed.B (n.log2+1)) :
    InMarkSaddleRange n (log ((exactMean n ell a side:ℝ)/t)) := by
  let b := n.log2+1
  let H := log (Fixed.B b)
  have tp : (0:ℝ)<t := zero_lt_one.trans_le tr
  have bd : 1 < (Fixed.B b:ℝ) := band_one_lt (Nat.succ_pos n.log2)
  have hp : 0<H := log_pos bd
  have tw : (t:ℝ) ≤ (Fixed.A b:ℝ)*(Fixed.B b:ℝ)^40 := calc
    _ ≤ (Fixed.B b:ℝ) := by exact_mod_cast lim
    _ ≤ (Fixed.B b:ℝ)^40 := le_self_pow₀ bd.le (by decide)
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast (Nat.one_le_two_pow : 1≤Fixed.A b))
  have win := one_point_window hn big target cap grid side (t:ℝ) ⟨tr,tw⟩
  have lo := (le_div_iff₀ hp).mp win.2.2.1
  have yp : 0 < (exactMean n ell a side:ℝ) := (div_pos_iff_of_pos_right tp).mp (zero_lt_one.trans_le win.2.1)
  have shift := mark_log_displacement hn big target cap grid side (exactMean n ell a side) (by simp; positivity)
  have tl : log (t:ℝ) ≤ H := log_le_log tp (by exact_mod_cast lim)
  have tn : 0 ≤ log (t:ℝ) := log_nonneg tr
  have hi := (div_le_iff₀ hp).mp win.2.2.2.1
  refine ⟨(mul_comm ..).trans_le lo,hi.trans_eq (mul_comm ..),?_⟩
  change _ ≤ log ((exactMean n ell a side:ℝ)/t) ∧ log ((exactMean n ell a side:ℝ)/t) ≤ _
  rw [log_div yp.ne' tp.ne']
  change |log (exactMean n ell a side:ℝ)-log (amplitude n)| ≤ H/200 at shift
  obtain ⟨l,r⟩ := abs_le.mp shift
  constructor <;> linarith

theorem divided_center_range {n ell a : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) :
    InMarkSaddleRange n (dividedLogCenter n ell a side) := by
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  apply grid_center_range hn big target side cap grid
  · have one : 1 ≤ targetPart n ell a side := by
      dsimp [targetPart]; split <;> first | exact (mem_dyadicTargets.mp target).1.one_le | decide
    exact_mod_cast one
  · have cap : targetPart n ell a side ≤ Fixed.B (n.log2+1) := by
      dsimp [targetPart]; split <;> first | exact (mem_dyadicTargets.mp target).2.2 | exact Nat.one_le_two_pow
    exact_mod_cast cap

/-- Compare any two saddles on the two full integer meshes. -/
theorem grid_saddle_prime_weight {n : ℕ}
    (big : 10004 ≤ Fixed.d (n.log2+1)) {α β : ℝ} (ap : 0≤α) (bp : 0≤β)
    (ma : InMarkSaddleRange n (saddleMean (primeBand (n.log2+1)) α))
    (mb : InMarkSaddleRange n (saddleMean (primeBand (n.log2+1)) β))
    {q : ℕ} (qm : q ∈ primeBand (n.log2+1)) :
    |(q:ℝ)^(-α)/(q:ℝ)^(-β)-1| ≤ 16/(90*(Fixed.d (n.log2+1):ℝ)) := by
  let b := n.log2+1
  let H := log (Fixed.B b)
  let u := 90*(Fixed.d b:ℝ)
  have ⟨l,_,x,y⟩ := ma
  have ⟨r,_,z,w⟩ := mb
  have bd : 1 < (Fixed.B b:ℝ) := band_one_lt (Nat.succ_pos n.log2)
  have hp : 0<H := log_pos bd
  have ur : (10004:ℝ) ≤ Fixed.d b := by exact_mod_cast big
  rw [show (16:ℝ)=8*2 by norm_num]
  apply prime_weight_of_saddle_gap (primeBand b) α β H u 2 ap bp hp (by dsimp [u]; positivity)
    (by dsimp [u]; linarith only [ur]) (fun p pm=>(mem_primeBand.mp pm).1.one_le) (fun _=>band_log_interval (Nat.succ_pos n.log2))
    l r _ q qm
  change log (amplitude n)-201*H/200 ≤ _ at x z
  change _ ≤ log (amplitude n)+H/200 at y w
  exact abs_le.mpr ⟨by linarith only [x,w,hp],by linarith only [z,y,hp]⟩

/-- One reference saddle can be used for all mark and field coordinates,
including comparisons across distinct target-hit branches. -/
theorem divided_mark_prime_weight {n ell a a₀ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1))
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (mark : a ∈ (construct n ell 0 0 0 0).marks)
    (refMark : a₀ ∈ (construct n ell 0 0 0 0).marks)
    (side side₀ : Bool) {α β : ℝ} (ap : 0≤α) (bp : 0≤β)
    (ma : saddleMean (primeBand (n.log2+1)) α = dividedLogCenter n ell a side)
    (mb : saddleMean (primeBand (n.log2+1)) β = dividedLogCenter n ell a₀ side₀)
    {q : ℕ} (qm : q ∈ primeBand (n.log2+1)) :
    |(q:ℝ)^(-α)/(q:ℝ)^(-β)-1| ≤ 16/(90*(Fixed.d (n.log2+1):ℝ)) :=
  grid_saddle_prime_weight big ap bp (ma ▸ divided_center_range hn big target mark side)
    (mb ▸ divided_center_range hn big target refMark side₀) qm

/-- Insertion atoms on the common prime scale. The two-prime remainder
after subtracting the curvature is second order even on target-hit marks. -/
theorem grid_scale_insertions :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ α β : ℝ, 199/200≤α → 0≤β →
    InMarkSaddleRange n (saddleMean (primeBand b) α) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    let u₀ := 90*(Fixed.d b:ℝ)
    let I := fun Q : ℕ => fullBandInsertion b Q α / ((Q:ℝ)*(Q:ℝ)^(-β))
    let V := saddleVariance (primeBand b) (primeProbability α) (fun p=>log p)
    ∀ p∈primeBand b, ∀ q∈primeBand b,
      |I p-1|≤88/u₀ ∧
      |I (p*q)-I p*I q*(1-log p*log q/V)|≤C/u₀^2 := by
  obtain ⟨C,cp,b₁,central⟩ := fixed_central_insertions 0
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨4*C,by positivity,max b₁ b₂,?_⟩
  intro n b huge α β aa bp ma mb u₀ I V p pm q qm
  have big := degree b (max_le_iff.mp huge).2
  have dr : (10004:ℝ)≤Fixed.d b := by exact_mod_cast big
  have u₀large : 16≤u₀ := by dsimp only [u₀]; linarith only [dr]
  have u₀p : 0<u₀ := by linarith
  let H := log (Fixed.B b:ℝ)
  let J := primeBand b
  let u := saddleMean J α/H
  let M := shiftedMass J (primeProbability α) (fun p=>log p) H
  let G (s : ℝ) := M s/M 0
  let r (k : ℕ) := (k:ℝ)^(-α)/(k:ℝ)^(-β)
  have hp : 0<H := log_pos (band_one_lt (Nat.succ_pos n.log2))
  obtain ⟨lo,hi,_,_⟩ := ma
  have low : u₀≤u := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using lo)
  have high : u≤110*(Fixed.d b:ℝ) := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hi)
  have eqm : saddleMean J α=H*u := by dsimp only [u]; field_simp
  have logBound (k) (km : k∈J) : |log k| ≤ H := by
    rw [abs_of_nonneg (log_nonneg (by exact_mod_cast (mem_primeBand.mp km).1.one_le))]
    exact (band_log_interval (Nat.succ_pos n.log2) km).2
  have raw := central b (max_le_iff.mp huge).1 u α (log p) (log q) (fun _=>∅)
  dsimp only at raw
  rw [show (Finset.Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime=J by simp [J,primeBand]] at raw
  have ⟨_,single,pair⟩ := raw low high aa eqm (logBound p pm) (logBound q qm) (by simp)
  have om (s : ℝ) : omittedMass J ∅ (primeProbability α) (fun p=>log p) H s=M s := by
    simp only [M,omittedMass,omittedCharacteristic,saddleCharacteristic,shiftedMass,Finset.notMem_empty,ite_false]
  change ∀ s : ℝ, |s|≤2*H → |omittedMass J ∅ _ _ H s/omittedMass J ∅ _ _ H 0-1|≤36/u ∧ _ at single
  change |omittedMass J ∅ _ _ H _ / _ - _| ≤ _ at pair
  simp only [om] at single pair
  change |G (log p+log q)-G (log p)*G (log q)*(1-log p*log q/V)|≤C/u^2 at pair
  have drift (k) (km : k∈J) : |r k-1|≤16/u₀ :=
    grid_saddle_prime_weight big (by linarith only [aa]) bp ma mb km
  have mag (k) (km : k∈J) : |r k|≤2 := by
    have rp : 0≤r k := by dsimp only [r]; positivity
    rw [abs_of_nonneg rp]
    have cap := (abs_le.mp (drift k km)).2
    have frac : 16/u₀≤1 := (div_le_one u₀p).mpr u₀large
    linarith only [cap,frac]
  have fi (k : ℕ) (kp : 0<(k:ℝ)) : I k=r k*G (log k) := by
    dsimp only [I,fullBandInsertion,G,r,M,J,H]
    rw [show (1:ℝ)-α=1+(-α) by ring, Real.rpow_add kp, Real.rpow_one]
    field_simp
  have pp : 0<(p:ℝ) := by exact_mod_cast (mem_primeBand.mp pm).1.pos
  have qp : 0<(q:ℝ) := by exact_mod_cast (mem_primeBand.mp qm).1.pos
  rw [fi p pp,fi q qp,fi (p*q) (by exact_mod_cast Nat.mul_pos (mem_primeBand.mp pm).1.pos (mem_primeBand.mp qm).1.pos)]
  constructor
  · have h := (single (log p) ((logBound p pm).trans (by linarith only [hp]))).1
    change |G (log p)-1| ≤ 36/u at h
    rw [show r p*G (log p)-1 = r p*(G (log p)-1)+(r p-1) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have rs := mul_le_mul (mag p pm) (h.trans (div_le_div_of_nonneg_left (by norm_num) u₀p low))
      (abs_nonneg _) (by norm_num)
    exact (add_le_add rs (drift p pm)).trans_eq (by ring)
  · have prod : r (p*q)=r p*r q := by
      simp only [r,Nat.cast_mul,mul_rpow pp.le qp.le]; ring
    rw [prod,Nat.cast_mul,log_mul pp.ne' qp.ne']
    rw [show r p*r q*G (log p+log q)-r p*G (log p)*(r q*G (log q))*(1-log p*log q/V) =
        (r p*r q)*(G (log p+log q)-G (log p)*G (log q)*(1-log p*log q/V)) by ring]
    rw [abs_mul,abs_mul]
    have bound := mul_le_mul (mag p pm) (mag q qm) (abs_nonneg _) (by norm_num)
    calc _ ≤ (2*2)*(C/u₀^2) := mul_le_mul bound (pair.trans (div_le_div_of_nonneg_left cp.le
             (sq_pos_of_pos u₀p) (pow_le_pow_left₀ u₀p.le low _))) (abs_nonneg _) (by norm_num)
         _ = _ := by ring

theorem common_scale_insertions :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell a a₀ : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ell∈dyadicTargets (Fixed.beta b) →
    a∈(construct n ell 0 0 0 0).marks → a₀∈(construct n ell 0 0 0 0).marks →
    ∀ (side side₀ : Bool) (α β : ℝ), 199/200≤α → 0≤β →
    saddleMean (primeBand b) α=dividedLogCenter n ell a side →
    saddleMean (primeBand b) β=dividedLogCenter n ell a₀ side₀ →
    let u₀ := 90*(Fixed.d b:ℝ)
    let I := fun Q : ℕ => fullBandInsertion b Q α / ((Q:ℝ)*(Q:ℝ)^(-β))
    let V := saddleVariance (primeBand b) (primeProbability α) (fun p=>log p)
    ∀ p∈primeBand b, ∀ q∈primeBand b,
      |I p-1|≤88/u₀ ∧
      |I (p*q)-I p*I q*(1-log p*log q/V)|≤C/u₀^2 := by
  obtain ⟨C,cp,b₁,raw⟩ := grid_scale_insertions
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max b₁ b₂,?_⟩
  intro n ell a a₀ b large hn target mark refMark side side₀ α β aa bp ma mb
  have big := deg b (max_le_iff.mp large).2
  exact raw (max_le_iff.mp large).1 α β aa bp (ma ▸ divided_center_range hn big target mark side)
    (mb ▸ divided_center_range hn big target refMark side₀)

/-- The local curvature denominator has the same lower bound at every
position on both target meshes. -/
theorem grid_variance_floor {n : ℕ} {α : ℝ} (ap : 0≤α)
    (ma : InMarkSaddleRange n (saddleMean (primeBand (n.log2+1)) α)) :
    let b := n.log2+1
    let H := log (Fixed.B b:ℝ)
    let u₀ := 90*(Fixed.d b:ℝ)
    let V := saddleVariance (primeBand b) (primeProbability α) (fun q=>log q)
    H^2*u₀≤4*V ∧ 0<V := by
  intro b H u₀ V
  have up : 0<u₀ := by dsimp only [u₀];exact_mod_cast Nat.mul_pos (by decide : 0<90) (Fixed.degree_pos (Nat.succ_pos n.log2))
  have hp : 0<H := log_pos (band_one_lt (Nat.succ_pos n.log2))
  have var := (prime_saddle_variance_bounds (primeBand b) α H ap hp.le
    (fun q qm=>(mem_primeBand.mp qm).1.one_le) (fun q qm=>band_log_interval (Nat.succ_pos n.log2) qm)).1
  have low := ma.1
  change H*u₀≤_ at low
  change H*_/4≤V at var
  have floor : H^2*u₀≤4*V := by nlinarith only [var,mul_le_mul_of_nonneg_left low hp.le]
  exact ⟨floor,by nlinarith only [floor,mul_pos (sq_pos_of_pos hp) up]⟩

/-- Displacement of the physical curvature direction from its reference norm
direction. The estimate allows repeated primes on different rows. -/
theorem common_scale_curvature_displacement :
    ∃ b₀ : ℕ, ∀ {ι : Type*} [Fintype ι] {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ α β : ℝ, 199/200≤α → 0≤β →
    InMarkSaddleRange n (saddleMean (primeBand b) α) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    ∀ (p : ι→ℕ), (∀ i, p i ∈ primeBand b) →
    let u₀ := 90*(Fixed.d b:ℝ)
    let m := fun i => (p i:ℝ)^(-β)
    let w := fun i => sqrt (m i)*log (p i)
    let z := fun i => fullBandInsertion b (p i) α/((p i:ℝ)*m i)
    let V := saddleVariance (primeBand b) (primeProbability α) (fun q=>log q)
    ∀ v : ι→ℝ,
      (∑ i, (z i-1)*w i*v i)^2/V ≤
        (4*88^2/u₀^3)*(∑ i,m i)*(∑ i,(v i)^2) := by
  obtain ⟨_,_,b₁,insertions⟩ := grid_scale_insertions
  obtain ⟨b₂,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro ι _ n b huge α β aa bp ma mb p pm u₀ m w z V v
  let H := log (Fixed.B b:ℝ)
  have big := degree b (max_le_iff.mp huge).2
  have up : 0<u₀ := by dsimp only [u₀]; exact_mod_cast Nat.mul_pos (by decide : 0<90) (Fixed.degree_pos (Nat.succ_pos n.log2))
  have hp : 0<H := log_pos (band_one_lt (Nat.succ_pos n.log2))
  have band (q : ℕ) (qm : q∈primeBand b) : H/2 ≤ log q ∧ log q ≤ H :=
    band_log_interval (Nat.succ_pos n.log2) qm
  obtain ⟨floor,vp⟩ := grid_variance_floor (by linarith only [aa] : 0≤α) ma
  change H^2*u₀≤4*V at floor
  have single := insertions (max_le_iff.mp huge).1 α β aa bp ma mb
  have nn (i : ι) : 0≤m i := rpow_nonneg (Nat.cast_nonneg _) _
  have d (i) : |z i-1|≤88/u₀ := (single (p i) (pm i) (p i) (pm i)).1
  have pt (i) : ((z i-1)*w i)^2 ≤ ((88/u₀)^2*H^2)*m i := by
    rw [mul_pow,show (w i)^2 = m i*(log (p i))^2 by rw [show w i=sqrt (m i)*log (p i) from rfl,mul_pow,sq_sqrt (nn i)]]
    have a := sq_le_sq' (abs_le.mp (d i)).1 (abs_le.mp (d i)).2
    have l := (band (p i) (pm i))
    have c := sq_le_sq' (by linarith only [l.1,hp] : -H≤log (p i)) l.2
    exact (mul_le_mul a (mul_le_mul_of_nonneg_left c (nn i)) (by positivity) (by positivity)).trans_eq (by ring)
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pt i)
  rw [← Finset.mul_sum] at total
  have bound := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>(z i-1)*w i) v
  rw [div_le_iff₀ vp]
  apply (bound.trans (mul_le_mul_of_nonneg_right total (Finset.sum_nonneg (fun i _=>sq_nonneg (v i))))).trans
  have cmp : (88/u₀)^2*H^2 ≤ (4*88^2/u₀^3)*V := by
    field_simp [up.ne']
    nlinarith only [floor]
  have positive := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right cmp (Finset.sum_nonneg (s:=Finset.univ) (fun i _=>nn i)))
    (Finset.sum_nonneg (s:=Finset.univ) (fun i _=>sq_nonneg (v i)))
  exact positive.trans_eq (by ring)

/-- A perpendicular ordinary vector loses only the second-order displacement
energy. -/
theorem common_scale_curvature_energy {ι : Type*} [Fintype ι] :
    ∃ b₀ : ℕ, ∀ {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ α β : ℝ, 199/200≤α → 0≤β →
    InMarkSaddleRange n (saddleMean (primeBand b) α) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    ∀ (p : ι→ℕ), (∀ i, p i ∈ primeBand b) →
    let u₀ := 90*(Fixed.d b:ℝ)
    let m := fun i => (p i:ℝ)^(-β)
    let w := fun i => sqrt (m i)*log (p i)
    let z := fun i => fullBandInsertion b (p i) α/((p i:ℝ)*m i)
    let V := saddleVariance (primeBand b) (primeProbability α) (fun q=>log q)
    ∀ v : ι→ℝ, (∑ i, w i*v i)=0 →
      (∑ i, z i*w i*v i)^2/V ≤
        (4*88^2/u₀^3)*(∑ i,m i)*(∑ i,(v i)^2) := by
  obtain ⟨b₀,displace⟩ := common_scale_curvature_displacement
  refine ⟨b₀,?_⟩
  intro n b big α β aa bp ma mb p pm u₀ m w z V v perp
  have h := displace big α β aa bp ma mb p pm v
  change (∑ i,(z i-1)*w i*v i)^2/V≤_ at h
  simpa only [sub_mul,one_mul,Finset.sum_sub_distrib,perp,sub_zero] using h

/-- When the target rows participate in the norm equation, their missing
curvature coefficient costs only their raw residue density times `8/u₀`.
Here `x` is the reciprocal row scale, in particular `1 / sqrt ell`. -/
theorem joint_target_curvature_uniform :
    ∃ b₀ : ℕ, ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}, let b := n.log2+1
    b₀≤b → ∀ α β : ℝ, 199/200≤α → 0≤β →
    InMarkSaddleRange n (saddleMean (primeBand b) α) →
    InMarkSaddleRange n (saddleMean (primeBand b) β) →
    ∀ (p : ι→ℕ), (∀ i, p i∈primeBand b) → ∀ ell∈primeBand b, ∀ x : ℝ,
    let u₀ := 90*(Fixed.d b:ℝ)
    let m := fun i => (p i:ℝ)^(-β)
    let w := fun i => sqrt (m i)*log (p i)
    let z := fun i => fullBandInsertion b (p i) α/((p i:ℝ)*m i)
    let V := saddleVariance (primeBand b) (primeProbability α) (fun q=>log q)
    ∀ (v : ι→ℝ) (t : κ→ℝ),
    (∑ i,w i*v i)+x*log ell*(∑ r,t r)=0 →
    (∑ i,z i*w i*v i)^2/V ≤
      (8*88^2/u₀^3)*(∑ i,m i)*(∑ i,(v i)^2)+
      (8/u₀)*((Fintype.card κ:ℝ)*x^2)*(∑ r,(t r)^2) := by
  obtain ⟨b₀,displace⟩ := common_scale_curvature_displacement
  refine ⟨b₀,?_⟩
  intro ι κ _ _ n b big α β aa bp ma mb p pm ell em x u₀ m w z V v t perp
  let H := log (Fixed.B b:ℝ)
  let D := ∑ i,(z i-1)*w i*v i
  let S := x*log ell*(∑ r,t r)
  have eq : (∑ i,z i*w i*v i)=D-S := by
    dsimp only [D,S]
    simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
    linarith only [perp]
  have ub : D^2/V≤(4*88^2/u₀^3)*(∑ i,m i)*(∑ i,(v i)^2) := displace big α β aa bp ma mb p pm v
  obtain ⟨floor,vp⟩ := grid_variance_floor (by linarith only [aa] : 0≤α) ma
  change H^2*u₀≤4*V at floor
  change 0<V at vp
  have up : 0<u₀ := by dsimp only [u₀];exact_mod_cast Nat.mul_pos (by decide : 0<90) (Fixed.degree_pos (Nat.succ_pos n.log2))
  obtain ⟨l,h⟩ := band_log_interval (Nat.succ_pos n.log2) em
  have hp : 0<H := log_pos (band_one_lt (Nat.succ_pos n.log2))
  have logSq : (log ell)^2≤H^2 := sq_le_sq' (by change H/2≤_ at l; linarith only [l,hp]) h
  have ratio : (log ell)^2/V≤4/u₀ :=
    (div_le_div_iff₀ vp up).mpr ((mul_le_mul_of_nonneg_right logSq up.le).trans floor)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ=>(1:ℝ)) t
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at cs
  have xs := mul_le_mul_of_nonneg_left cs (sq_nonneg x)
  have sbound := mul_le_mul ratio xs (mul_nonneg (sq_nonneg x) (sq_nonneg _)) (by positivity)
  have sb : S^2/V≤(4/u₀)*((Fintype.card κ:ℝ)*x^2)*(∑ r,(t r)^2) := by
    calc S^2/V = (log ell)^2/V*(x^2*(∑ r,t r)^2) := by dsimp only [S];ring
         _ ≤ _ := sbound
         _ = _ := by ring
  rw [eq]
  have joint := div_le_div_of_nonneg_right
    (show (D-S)^2≤2*D^2+2*S^2 by nlinarith only [sq_nonneg (D+S)]) vp.le
  apply joint.trans
  rw [show (2*D^2+2*S^2)/V=2*(D^2/V)+2*(S^2/V) by ring]
  exact (add_le_add (mul_le_mul_of_nonneg_left ub (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left sb (by norm_num : (0:ℝ)≤2))).trans_eq (by ring)

end
end Cogentic.Construction

#print axioms Cogentic.Construction.divided_mark_prime_weight

#print axioms Cogentic.Construction.common_scale_insertions

#print axioms Cogentic.Construction.common_scale_curvature_energy

#print axioms Cogentic.Construction.joint_target_curvature_uniform
