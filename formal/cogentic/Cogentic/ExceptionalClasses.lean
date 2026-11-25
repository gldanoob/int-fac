import Cogentic.ClassBalance

namespace Cogentic.Window
open Real

theorem gaussianMass_pos (J : Finset ℕ) (Y S : ℝ) (sp : 0<S) : 0<gaussianMass J Y S := by
  have one : 1∈squarefreeSupport J := Finset.mem_image.mpr
    ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _),by simp⟩
  exact (div_pos (exp_pos _) sp).trans_le (Finset.single_le_sum
    (f:=fun n : ℕ => gaussian Y S n) (fun n _ => (div_pos (exp_pos _) sp).le) one)

private theorem retained_neighbor (J D : Finset ℕ) (r ell : ℕ → ℝ) (p : ℕ) (H u : ℝ)
    (hp : p∈J) (hH : 0<H) (hu : 2<u) (r0 : ∀ t∈J, 0 ≤ r t) (r1 : ∀ t∈J, r t ≤ 1)
    (band : ∀ t∈J, ell t ≤ H) (mean : ∑ t∈J, r t*ell t=H*u)
    (del : (∑ t∈J, if t∈D then r t else 0) ≤ 1) :
    ∃ t∈J\D, p≠t := by
  classical
  by_contra! miss
  have ub : (∑ t∈J, r t) ≤ (∑ t∈J, if t∈D then r t else 0)+1 := by
    have eq : (∑ t∈J, if t=p then (1:ℝ) else 0)=1 := by simp [hp]
    rw [←eq,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    by_cases d : t∈D
    · simp only [d,if_pos]; split <;> linarith
    · have h := miss t (Finset.mem_sdiff.mpr ⟨ht,d⟩)
      rw [if_neg d,if_pos h.symm,zero_add]; exact r1 t ht
  have m := Finset.sum_le_sum (s:=J) (fun t ht => mul_le_mul_of_nonneg_left (band t ht) (r0 t ht))
  rw [←Finset.sum_mul,mean] at m
  have sz : (∑t∈J,r t) ≤ 2 := by linarith only [ub,del]
  linarith only [m,mul_le_mul_of_nonneg_right sz hH.le,mul_lt_mul_of_pos_left hu hH]

/-- Every retained prime has true smooth Gaussian divisibility
    probability at most twice its own Bernoulli weight. -/
theorem fixed_divisibility_upper (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α Y S : ℝ) (D : Finset ℕ) (p : ℕ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    let K := J\D
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    saddleMean J α=H*u → log Y=H*u → 0<Y → 0<S →
    B^(17/200:ℝ) ≤ Y/S → Y/S ≤ B^(17/100:ℝ) → D.card+2 ≤ b^k →
    D⊆J → p∈K → divisorGaussian K p Y S ≤ 2*primeProbability α p*gaussianMass K Y S := by
  obtain ⟨_,_,n₁,pr⟩ := fixed_divisibility_covariance line k
  obtain ⟨n₂,del⟩ := fixed_prime_deletions k
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ (max n₂ n₃),?_⟩
  intro b huge u α Y S D p B H J K lo hi ha mean logY yp sp wl wh card sub mem
  obtain ⟨one,a⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp a
  have hd : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast deg b three
  have u48 : 48≤u := by linarith only [lo,hd]
  have up : 0<u := by linarith only [u48]
  obtain ⟨hH,large,_,mw,sm,band,om⟩ := del b two u α lo hi ha
  have cap : (1:ℝ)/u^5 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by linarith only [large]))
  have r0 (t : ℕ) (_ : t∈J) : 0≤primeProbability α t := by unfold primeProbability; positivity
  have r1 (t : ℕ) (ht : t∈J) : primeProbability α t ≤ 1 := (band t ht).1.trans (mw.trans (sm.trans cap))
  obtain ⟨q,qm,ne⟩ := retained_neighbor J D _ (fun t=>log t) p H u (Finset.mem_sdiff.mp mem).1 hH
    (by linarith only [u48]) r0 r1 (fun t h=>(band t h).2.2) mean ((om D (by omega)).trans (sm.trans cap))
  have h := (pr b one u α Y S D p q lo hi ha mean logY yp sp wl wh card sub mem qm ne).1
  have pp := (Finset.mem_filter.mp (Finset.mem_sdiff.mp mem).1).2
  have w : 0<primeProbability α p := by
    have pos : 0<(p:ℝ) := by exact_mod_cast pp.pos
    unfold primeProbability
    positivity
  have gp := gaussianMass_pos K Y S sp
  have near := (abs_le.mp h).2
  have ur : 48/u≤1 := (div_le_one up).mpr u48
  have rate : (divisorGaussian K p Y S/gaussianMass K Y S)/primeProbability α p≤2 := by linarith only [near,ur]
  exact (div_le_iff₀ gp).mp ((div_le_iff₀ w).mp rate)

end Cogentic.Window

namespace Cogentic.Construction
open Cogentic.Window Real

/-- At an actual first-coordinate clean window, rejecting any prescribed
    extra residue costs O(1/p) in a unit class and O(r_p) in the zero
    class, relative to that actual smooth reduced class. -/
theorem constructed_exceptional_residues (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ {n ell forced q₀ q p : ℕ} {Y S α : ℝ},
    let b := n.log2+1
    let J := (sieveBand n ell forced).filter (fun x => ¬x∣q₀)
    n₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    0<forced → forced≤(Fixed.B b)^3 → 0<q → q∣q₀ → 0<q₀ → q₀*p≤conductorCap n →
    p.Prime → q.Coprime p → InWindow b Y S → InWindow b (Y/p) (S/p) →
    199/200≤α → saddleMean (primeBand b) α=log Y →
    ∀ r : (ZMod q)ˣ,
    (∀ s : (ZMod p)ˣ, classPart J Y S r (fun n => (s:ZMod p)=(n:ZMod p)) ≤
      (9/((p:ℝ)-1))*classWeight J Y S r) ∧
    classPart J Y S r (p∣·) ≤ (18*primeProbability α p)*classWeight J Y S r := by
  classical
  obtain ⟨n₁,bal⟩ := constructed_classes_balanced line
  obtain ⟨n₂,rate⟩ := fixed_divisibility_upper line 4
  obtain ⟨n₃,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ (max n₂ n₃),?_⟩
  intro n ell forced q₀ q p Y S α b J huge hn comp target absent pf fc qp qd q₀p cap pp cop win winp ha mean r
  let H := log (Fixed.B b)
  let : NeZero q := ⟨qp.ne'⟩
  obtain ⟨one,h⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp h
  have db := deg b three
  have big : 10004 ≤ Fixed.d b := by omega
  have bpos : 0<b := Nat.succ_pos _
  have bcap : q₀≤conductorCap n := (Nat.le_mul_of_pos_right _ pp.pos).trans cap
  have ppR : (0:ℝ)<p := by exact_mod_cast pp.pos
  have qp0 : 0<q₀*p := Nat.mul_pos q₀p pp.pos
  have base := bal one hn comp target absent pf fc qp qd q₀p bcap win
  let sieve := sieveBand n ell forced
  have prS (x : ℕ) (mem : x∈sieve) : x.Prime := (mem_primeBand.mp (Finset.mem_filter.mp mem).1).1
  have prJ (x : ℕ) (mem : x∈J) : x.Prime := prS x (Finset.mem_filter.mp mem).1
  have er : sieve.filter (fun x => ¬x∣q₀*p) = J.erase p := by
    ext x
    by_cases hx : x∈sieve
    · have xprime := prS x hx
      have divp : x∣p ↔ x=p := by
        rw [Nat.dvd_prime pp]
        simp [xprime.ne_one]
      simp [J,sieve] at hx ⊢
      rw [xprime.dvd_mul,divp]; tauto
    · change x∈sieve.filter _ ↔ x∈(sieve.filter _).erase p
      simp [hx]
  have extra : J\(q*p).primeFactors=J.erase p := by
    ext x
    by_cases hx : x∈J
    · have xp := prJ x hx
      have no : ¬x∣q := fun d => (Finset.mem_filter.mp hx).2 (d.trans qd)
      have divp : x∣p ↔ x=p := by rw [Nat.dvd_prime pp]; simp [xp.ne_one]
      simp [hx,Nat.mem_primeFactors,xp,Nat.ne_of_gt (Nat.mul_pos qp pp.pos),xp.dvd_mul,no,divp]
    · simp [hx]
  have joint := bal one hn comp target absent pf fc (Nat.mul_pos qp pp.pos) (Nat.mul_dvd_mul_right qd p) qp0 cap win
  change classBalanced (sieve.filter (fun x=>¬x∣q₀*p)) (q*p) Y S at joint
  rw [er,←extra] at joint
  refine ⟨fun s => nonzero_extra_class_cost J prJ pp cop Y S win.1 r s base joint,?_⟩
  by_cases eligible : p∈J
  · have split := bal one hn comp target absent pf fc qp (qd.trans (dvd_mul_right ..)) qp0 cap winp
    change classBalanced (sieve.filter (fun x=>¬x∣q₀*p)) q (Y/p) (S/p) at split
    rw [er] at split
    let D := primeBand b\J
    have subJ : J⊆primeBand b := fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have eqJ : primeBand b\D=J := Finset.sdiff_sdiff_eq_self subJ
    have card := omitted_card hn big comp target absent pf fc q₀p bcap
    change D.card ≤ b^3 at card
    have bits := Fixed.degree_le_bits b
    have bc : 2≤b := by omega
    have plus : D.card+2≤b^4 := by
      have bu : 2≤b^3 := bc.trans (Nat.le_self_pow (by decide) b)
      have fg := Nat.mul_le_mul_left (b^3) bc
      rw [pow_succ]
      omega
    have HH := (fixed_band_log_bounds b bpos (by omega)).1
    have dr : 50000≤(Fixed.d b:ℝ) := by exact_mod_cast db
    change 1000*(Fixed.d b:ℝ)≤H at HH
    have hp : 0<H := by linarith
    let u := log Y/H
    have eq : H*u=log Y := by dsimp [u]; field_simp
    specialize rate b two u α Y S D p
    simp only [Nat.floor_natCast] at rate
    change _ → _ → _ → saddleMean (primeBand b) α=H*u → _ → _ → _ → _ → _ → _ → _ → p∈primeBand b\D →
       divisorGaussian (primeBand b\D) p Y S ≤ 2*primeProbability α p*gaussianMass (primeBand b\D) Y S at rate
    rw [eqJ,eq] at rate
    have hit := rate win.2.2.1 win.2.2.2.1 ha mean rfl (zero_lt_one.trans_le win.2.1) win.1
      win.2.2.2.2.1 win.2.2.2.2.2.1 plus Finset.sdiff_subset eligible
    have cost := zero_extra_class_cost J prJ p eligible cop.symm Y S win.1 r base split
      (2*primeProbability α p) (by dsimp [primeProbability]; positivity) hit
    linarith only [cost]
  · have miss : (squarefreeSupport J).filter (p∣·)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨mem,dvd⟩ := Finset.mem_filter.mp hx
      obtain ⟨sf,fac⟩ := (mem_squarefreeSupport J prJ x).mp mem
      exact eligible (fac (Nat.mem_primeFactors.mpr ⟨pp,dvd,sf.ne_zero⟩))
    rw [classPart,miss,Finset.sum_empty]
    have base0 : 0≤classWeight J Y S r := by
      apply Finset.sum_nonneg; intro x _; split
      · exact (div_pos (exp_pos _) win.1).le
      · exact le_rfl
    exact mul_nonneg (by unfold primeProbability; positivity) base0

end Cogentic.Construction
