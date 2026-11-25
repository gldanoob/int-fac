import Cogentic.GaussianMarginal
import Cogentic.Window
import TwoThirdsWindow

open scoped BigOperators

namespace Cogentic.Window

noncomputable section

/-- The scalar index of a signed arithmetic progression enumerates each
    supported natural number in its class exactly once. -/
theorem affine_support_sum (A : Finset ℕ) (c s : ℤ) (hs : s ≠ 0) (w : ℤ → ℝ) :
    (∑' j : ℤ, if c+s*j ∈ A.image (fun n : ℕ => (n:ℤ)) then w (c+s*j) else 0) =
      ∑ n ∈ A, if (c:ZMod s.natAbs) = (n:ZMod s.natAbs) then w n else 0 := by
  classical
  let T := A.filter (fun n : ℕ => (c : ZMod s.natAbs) = (n : ZMod s.natAbs))
  let g := fun n : ℕ => ((n:ℤ)-c)/s
  let f := fun j : ℤ => c+s*j
  have class_iff (n : ℕ) : (c:ZMod s.natAbs)=(n:ZMod s.natAbs) ↔ s ∣ (n:ℤ)-c := by
    rw [← Int.natAbs_dvd]
    simpa only [Int.cast_natCast] using ZMod.intCast_eq_intCast_iff_dvd_sub c (n:ℤ) s.natAbs
  have fg (n : ℕ) (hn : n ∈ T) : f (g n) = n := by
    have dv := (class_iff n).mp (Finset.mem_filter.mp hn).2
    dsimp [f,g]
    rw [mul_comm s,Int.ediv_mul_cancel dv]
    ring
  have fi : Function.Injective f := by
    intro i j eq
    exact mul_left_cancel₀ hs (add_left_cancel eq : s*i=s*j)
  have gi : Set.InjOn g T := by
    intro n hn m hm eq
    have zz := congrArg f eq
    rw [fg n hn,fg m hm] at zz
    exact_mod_cast zz
  let v := fun j : ℤ => if f j ∈ A.image (fun n : ℕ => (n:ℤ)) then w (f j) else 0
  change (∑' j, v j) = _
  rw [tsum_eq_sum (s := T.image g) (fun j hj => ?_),Finset.sum_image gi,← Finset.sum_filter (s := A) (fun n : ℕ => (c:ZMod s.natAbs)=(n:ZMod s.natAbs)) (fun n : ℕ => w n)]
  · apply Finset.sum_congr rfl
    intro n hn
    dsimp only [v]
    rw [fg n hn,if_pos (Finset.mem_image.mpr ⟨n,(Finset.mem_filter.mp hn).1,rfl⟩)]
  · dsimp only [v]
    apply if_neg
    intro mem
    obtain ⟨n,hn,eq⟩ := Finset.mem_image.mp mem
    have cl : s ∣ (n:ℤ)-c := by
      refine ⟨j,?_⟩
      rw [eq]
      dsimp [f]; ring
    have hm : n ∈ T := Finset.mem_filter.mpr ⟨hn,(class_iff n).mpr cl⟩
    exact hj (Finset.mem_image.mpr ⟨n,hm,fi ((fg n hm).trans eq)⟩)

/-- Equality of the normalized scalar progression in the polynomial
    law and the finite reduced residue in the character theorem. -/
theorem gaussian_affine_classMass (J : Finset ℕ) (c s : ℤ) (hs : s ≠ 0)
    (r : (ZMod s.natAbs)ˣ) (hr : (r : ZMod s.natAbs)=c) (Y S : ℝ) :
    (((s.natAbs:ℝ)/S * ∑' j : ℤ, if c+s*j ∈ (squarefreeSupport J).image (fun n : ℕ => (n:ℤ)) then
      coeffGaussian (c+s*j : ℤ) Y S else 0 : ℝ):ℂ) =
    (s.natAbs:ℂ)*classMass (squarefreeSupport J) (fun n => (gaussian Y S n:ℂ)) r := by
  rw [affine_support_sum (squarefreeSupport J) c s hs (fun n => coeffGaussian n Y S)]
  rw [classMass]
  simp only [hr,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sum,← Complex.ofReal_zero,
    ← apply_ite Complex.ofReal]
  apply congrArg Complex.ofReal
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split <;> simp [coeffGaussian,gaussian]
  ring

/-- The constructive all-input squarefree predicate agrees with the
    actual Euler support of the analytic window theorem. -/
theorem supported_iff_euler (J : Finset ℕ) (hp : ∀ p ∈ J, p.Prime) (n : ℕ) :
    TwoThirdsWindow.Supported (fun p => p ∈ J) n ↔ n ∈ squarefreeSupport J := by
  have prime (p : ℕ) : TwoThirdsWindow.Prime p ↔ p.Prime := Nat.prime_def.symm
  rw [mem_squarefreeSupport J hp]
  constructor
  · rintro ⟨positive,supported⟩
    refine ⟨Nat.squarefree_iff_prime_squarefree.mpr (fun p pp sq =>
      (supported p ((prime p).mpr pp) ((dvd_mul_right p p).trans sq)).2 sq),?_⟩
    intro p mem
    exact (supported p ((prime p).mpr (Nat.prime_of_mem_primeFactors mem))
      (Nat.dvd_of_mem_primeFactors mem)).1
  · rintro ⟨square,sub⟩
    refine ⟨Nat.pos_of_ne_zero square.ne_zero,fun p pp dv => ?_⟩
    exact ⟨sub (Nat.mem_primeFactors.mpr ⟨(prime p).mp pp,dv,square.ne_zero⟩),
      (Nat.squarefree_iff_prime_squarefree.mp square) p ((prime p).mp pp)⟩

/-- Natural residue representatives of squarefree smooth integers, including
    nonunits, with the original modulus retained in the support. -/
def residueSupport (J : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (squarefreeSupport J).filter (fun n => n%q=r%q)

theorem divide_residue_support (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime) (r q : ℕ) (hq : 0 < q) :
    let g := r.gcd q
    let K := J.filter (fun p => ¬p ∣ q)
    residueSupport J q r = if g ∈ squarefreeSupport J then
      (residueSupport K (q/g) (r/g)).image (fun m => g*m) else ∅ := by
  classical
  let g := r.gcd q
  let K := J.filter (fun p => ¬p ∣ q)
  have kg (p : ℕ) (hp : p ∈ K) : p.Prime := pj p (Finset.mem_filter.mp hp).1
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  have supp : (fun p => p ∈ J ∧ ¬p ∣ q) = (fun p => p ∈ K) := by
    funext p; simp [K]
  have law (n : ℕ) := TwoThirdsWindow.divide_squarefree_class (fun p => p ∈ J) n r q hq
  simp only [supported_iff_euler J pj,supp,supported_iff_euler K kg] at law
  ext n
  change n ∈ residueSupport J q r ↔ n ∈ (if g ∈ squarefreeSupport J then
    (residueSupport K (q/g) (r/g)).image (fun m => g*m) else ∅)
  rw [residueSupport,Finset.mem_filter,and_comm,law]
  by_cases hg : g ∈ squarefreeSupport J
  · rw [if_pos hg,Finset.mem_image]
    constructor
    · rintro ⟨dvd,cl,_,mem⟩
      exact ⟨n/g,Finset.mem_filter.mpr ⟨mem,cl⟩,Nat.mul_div_cancel' dvd⟩
    · rintro ⟨m,hm,rfl⟩
      have hh := Finset.mem_filter.mp hm
      change g ∣ g*m ∧ ((g*m)/g)%(q/g)=(r/g)%(q/g) ∧
        g ∈ squarefreeSupport J ∧ (g*m)/g ∈ squarefreeSupport K
      rw [Nat.mul_div_cancel_left _ gp]
      exact ⟨dvd_mul_right ..,hh.2,hg,hh.1⟩
  · rw [if_neg hg]
    constructor
    · exact fun h => (hg h.2.2.1).elim
    · exact fun h => (Finset.notMem_empty n h).elim

/-- Exact Gaussian mass in any nonunit progression as a reduced mass,
    with the correct scaling of center, width, and normalization. -/
theorem divide_gaussian_class (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime)
    (r q : ℕ) (hq : 0 < q) (Y S : ℝ) (hS : 0 < S) :
    let g := r.gcd q
    let K := J.filter (fun p => ¬p ∣ q)
    let u := ZMod.unitOfCoprime (r/g) (TwoThirdsWindow.reduced_class_coprime r q hq)
    (q:ℂ)*(∑ n ∈ residueSupport J q r, (gaussian Y S n:ℂ)) =
      if g ∈ squarefreeSupport J then ((q/g:ℕ):ℂ) *
        classMass (squarefreeSupport K) (fun n => (gaussian (Y/g) (S/g) n:ℂ)) u else 0 := by
  classical
  let g := r.gcd q
  let K := J.filter (fun p => ¬p ∣ q)
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  let u := ZMod.unitOfCoprime (r/g) (TwoThirdsWindow.reduced_class_coprime r q hq)
  have eq := divide_residue_support J pj r q hq
  change residueSupport J q r = if g ∈ squarefreeSupport J then
    (residueSupport K (q/g) (r/g)).image (fun m => g*m) else ∅ at eq
  dsimp only
  change (q:ℂ)*(∑ n ∈ residueSupport J q r, (gaussian Y S n:ℂ)) =
    if g ∈ squarefreeSupport J then ((q/g:ℕ):ℂ) * classMass (squarefreeSupport K)
      (fun n => (gaussian (Y/g) (S/g) n:ℂ)) u else 0
  rw [eq]
  by_cases hg : g ∈ squarefreeSupport J
  · rw [if_pos hg,if_pos hg,Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left gp h)]
    have clas : classMass (squarefreeSupport K) (fun n => (gaussian (Y/g) (S/g) n:ℂ)) u =
        ∑ n ∈ residueSupport K (q/g) (r/g), (gaussian (Y/g) (S/g) n:ℂ) := by
      rw [classMass,residueSupport,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      rw [show (u:ZMod (q/g))=(r/g:ℕ) from ZMod.coe_unitOfCoprime ..]
      have mod : ((r/g:ℕ):ZMod (q/g))=(n:ZMod (q/g)) ↔ n%(q/g)=(r/g)%(q/g) :=
        (ZMod.natCast_eq_natCast_iff ..).trans eq_comm
      simp only [mod]
    rw [clas,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have scale := gaussian_rescale q g Y S ((g:ℝ)*(m:ℝ)) (by exact_mod_cast gp.ne') hS.ne'
    rw [mul_div_cancel_left₀ _ (by exact_mod_cast gp.ne' : (g:ℝ) ≠ 0)] at scale
    have qd : ((q/g:ℕ):ℝ)=(q:ℝ)/(g:ℝ) := Nat.cast_div (Nat.gcd_dvd_right r q) (by exact_mod_cast gp.ne')
    simpa only [Nat.cast_mul,Complex.ofReal_mul,Complex.ofReal_natCast,← qd] using
      congrArg Complex.ofReal scale.symm
  · simp [hg]

/-- The signed scalar Gaussian over an arbitrary residue, as it appears
    inside the two-point polynomial law, reduces exactly to a character
    window or vanishes when the forced common divisor is ineligible. -/
theorem affine_gaussian_reduced (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime)
    (c s : ℤ) (hs : s ≠ 0) (r : ℕ) (hc : (r:ZMod s.natAbs)=c)
    (Y S : ℝ) (hS : 0 < S) :
    let q := s.natAbs
    let g := r.gcd q
    let K := J.filter (fun p => ¬p ∣ q)
    let u := ZMod.unitOfCoprime (r/g) (TwoThirdsWindow.reduced_class_coprime r q (Int.natAbs_pos.mpr hs))
    (((q:ℝ)/S * ∑' j : ℤ, if c+s*j ∈ (squarefreeSupport J).image (fun n : ℕ => (n:ℤ)) then
      coeffGaussian (c+s*j : ℤ) Y S else 0 : ℝ):ℂ) =
      if g ∈ squarefreeSupport J then ((q/g:ℕ):ℂ) *
        classMass (squarefreeSupport K) (fun n => (gaussian (Y/g) (S/g) n:ℂ)) u else 0 := by
  dsimp only
  rw [← divide_gaussian_class J pj r s.natAbs (Int.natAbs_pos.mpr hs) Y S hS,
    affine_support_sum (squarefreeSupport J) c s hs (fun n => coeffGaussian n Y S)]
  rw [residueSupport,Finset.sum_filter,← hc]
  have mod (n : ℕ) : ((r:ZMod s.natAbs)=(n:ZMod s.natAbs)) ↔ n%s.natAbs=r%s.natAbs :=
    (ZMod.natCast_eq_natCast_iff ..).trans eq_comm
  simp only [mod,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_sum,
    ← Complex.ofReal_zero,← apply_ite Complex.ofReal]
  apply congrArg Complex.ofReal
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split <;> simp [coeffGaussian,gaussian]
  ring

/-- In a signed evaluation progression with positive center, every
    nonpositive value lies in a uniform Gaussian tail. -/
theorem negative_affine_gaussian_tail (c s : ℤ) (hs : s ≠ 0) (Y S : ℝ) (hY : 0 < Y)
    (hS : 0 < S) (hτ : 2 ≤ S/|(s:ℝ)|) :
    |(s:ℝ)| / S*(∑' j : ℤ, if c+s*j ≤ 0 then coeffGaussian (c+s*j : ℤ) Y S else 0) ≤
      8*Real.exp (-Real.pi*(Y/S)^2/2) := by
  let d := (s:ℝ)
  let τ := S/|d|
  let θ := (Y-(c:ℝ))/d
  let T := Y/S
  have nz : d ≠ 0 := by dsimp [d]; exact_mod_cast hs
  have dp : 0 < |d| := abs_pos.mpr nz
  have tp : 0 < τ := div_pos hS dp
  have θid : (c:ℝ)+d*θ=Y := by dsimp only [θ]; field_simp; ring
  have w' (j : ℤ) : coeffGaussian (c+s*j : ℤ) Y S = coeffGaussian j θ τ := by
    have w := conditional_second_weight nz (c:ℝ) (j:ℝ) θ τ
    rw [θid,show |d| *τ=S by dsimp [τ]; field_simp] at w
    push_cast
    exact w
  let F := fun j : ℤ => coeffGaussian j θ τ
  let A := fun j : ℤ => if c+s*j ≤ 0 then F j else 0
  let B := fun j : ℤ => if T*τ ≤ |(j:ℝ)-θ| then F j else 0
  have qp : 1 ≤ τ := by change 2 ≤ τ at hτ; linarith
  have sf : Summable F := by
    have hz := (conditional_progression_probability 0 1 θ τ zero_lt_one
      (by simpa only [div_one] using hτ) (fun _ => True)).1
    simp only [one_mul,zero_add] at hz
    by_contra h
    exact hz.ne' (tsum_eq_zero_of_not_summable h)
  have p (j : ℤ) : 0 ≤ F j := (Real.exp_pos _).le
  have sb : Summable B := by
    apply Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) sf
    · dsimp [B]; split <;> first | exact p j | rfl
    · dsimp [B]; split <;> first | exact p j | rfl
  have le (j : ℤ) : A j ≤ B j := by
    dsimp only [A,B]
    split_ifs with hn size size
    · rfl
    · exfalso
      apply size
      have x : (c:ℝ)+d*j ≤ 0 := by dsimp [d]; exact_mod_cast hn
      have y : Y ≤ |d| * |(j:ℝ)-θ| := by
        rw [← abs_mul,show d*((j:ℝ)-θ) = (c:ℝ)+d*j-Y by linarith only [θid]]
        rw [abs_of_nonpos (by linarith)]
        linarith
      have eq : T*τ=Y/|d| := by dsimp only [T,τ]; field_simp
      rw [eq,div_le_iff₀ dp,mul_comm]
      exact y
    · exact p j
    · rfl
  have sa : Summable A := Summable.of_nonneg_of_le (fun j => by
    dsimp [A]; split <;> first | exact p j | rfl) le sb
  have z := (sa.tsum_le_tsum le sb).trans (lattice_gaussian_tail θ τ T qp (div_pos hY hS).le)
  simp_rw [w']
  change |d| / S*(∑' j, A j) ≤ 8*Real.exp (-Real.pi*T^2/2)
  have cf : |d| / S = 1/τ := by dsimp [τ]; field_simp
  rw [cf]
  apply (mul_le_mul_of_nonneg_left z (one_div_pos.mpr tp).le).trans_eq
  field_simp

end

end Cogentic.Window
