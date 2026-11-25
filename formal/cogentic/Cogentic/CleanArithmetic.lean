import Cogentic.GaussianClass
import Cogentic.Construction
import Cogentic.ProgressionCorrection
import Cogentic.WindowCentral

namespace Cogentic.Window

noncomputable section

/-- A prescribed root distinct from both marks excludes at most one
    first-coordinate residue when the second value is required to be a unit. -/
theorem one_bad_mark_residue (p : ℕ) (pp : p.Prime) (a b r L f K : ZMod p)
    (ar : r ≠ a) (br : r ≠ b) (unit : K ≠ 0) :
    ∃ c : ZMod p, ∀ x w : ZMod p, x+(r-a)*w=L →
      (f+K*(x+(b-a)*w)=0 ↔ x=c) := by
  let : Fact p.Prime := ⟨pp⟩
  let c := (-(r-a)*f/K-(b-a)*L)/(r-b)
  refine ⟨c,fun x w row => ?_⟩
  have eq : (r-a)*(f+K*(x+(b-a)*w)) = K*(r-b)*x+(r-a)*f+K*(b-a)*L := by
    linear_combination (norm := ring) (K*(b-a))*row
  have nza := sub_ne_zero.mpr ar
  have nzb := sub_ne_zero.mpr br
  constructor
  · intro h
    rw [h,mul_zero] at eq
    dsimp only [c]
    rw [eq_div_iff nzb]
    field_simp [unit]
    linear_combination (norm := ring) -eq
  · intro h
    dsimp only [c] at h
    rw [eq_div_iff nzb] at h
    field_simp [unit] at h
    apply mul_left_cancel₀ nza
    rw [mul_zero,eq]
    linear_combination (norm := ring) h

/-- Congruent marks have congruent values for the actual Horner
    coefficient arrays used by the deterministic constructor. -/
theorem diagonal_evaluation_dvd (f : List ℤ) (p : ℕ) (a b : ℤ) (coincide : (p:ℤ) ∣ b-a) :
    (p:ℤ) ∣ Cogentic.Construction.eval b f ↔ (p:ℤ) ∣ Cogentic.Construction.eval a f := by
  have hab := (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mpr coincide
  have eq : ((Cogentic.Construction.eval b f : ℤ):ZMod p)=
      ((Cogentic.Construction.eval a f : ℤ):ZMod p) := by
    induction f with
    | nil => rfl
    | cons c l ih => simp only [Construction.eval,Int.cast_add,Int.cast_mul,hab,ih]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd,eq]

/-- On the squarefree smooth event at one mark, any prime dividing both
    evaluations at a diagonal coincidence belongs to the prime support. -/
theorem diagonal_smooth_prime (f : List ℤ) (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime)
    (p : ℕ) (prime : p.Prime) (a b : ℤ) (coincide : (p:ℤ) ∣ b-a)
    (smooth : (Construction.eval a f).natAbs ∈ squarefreeSupport J)
    (bad : (p:ℤ) ∣ Construction.eval b f) : p ∈ J := by
  have d := (diagonal_evaluation_dvd f p a b coincide).mp bad
  obtain ⟨sf,sub⟩ := (mem_squarefreeSupport J pj _).mp smooth
  exact sub (prime.mem_primeFactors (Int.natCast_dvd.mp d) sf.ne_zero)

/-- An inserted prime determines a bijection with products of the other
    eligible primes, independent of the congruence to be applied later. -/
theorem marked_prime_support (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime) (p : ℕ) (hp : p ∈ J) :
    (squarefreeSupport J).filter (fun n => p ∣ n) =
      (squarefreeSupport (J.erase p)).image (fun m => p*m) := by
  classical
  have pp := pj p hp
  have res := divide_residue_support J pj 0 p pp.pos
  simp only [Nat.gcd_zero_left,Nat.div_self pp.pos,Nat.zero_div,residueSupport,Nat.mod_one,
    Nat.zero_mod,← Nat.dvd_iff_mod_eq_zero] at res
  have single : p ∈ squarefreeSupport J := (mem_squarefreeSupport J pj _).mpr
    ⟨pp.squarefree,by simpa [pp.primeFactors] using hp⟩
  have er : J.filter (fun q => ¬q ∣ p) = J.erase p := by
    ext q
    rw [Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨mem,nd⟩
      exact ⟨fun eq => nd (eq ▸ dvd_rfl),mem⟩
    · rintro ⟨ne,mem⟩
      exact ⟨mem,fun dvd => ((Nat.dvd_prime pp).mp dvd).elim (pj q mem).ne_one ne⟩
  simpa [single,er] using res

/-- Exact one-prime marked probability inside a reduced smooth window.
    The change of center and width produces the full factor 1/p. -/
theorem marked_prime_classMass {q : ℕ} (J : Finset ℕ) (pj : ∀ p ∈ J, p.Prime)
    (p : ℕ) (hp : p ∈ J) (cop : p.Coprime q) (r : (ZMod q)ˣ) (Y S : ℝ) (hS : 0 < S) :
    classMass ((squarefreeSupport J).filter (fun n => p ∣ n))
      (fun n => (gaussian Y S n:ℂ)) r =
      (1/(p:ℂ))*classMass (squarefreeSupport (J.erase p))
        (fun n => (gaussian (Y/p) (S/p) n:ℂ)) (r/(ZMod.unitOfCoprime p cop)) := by
  classical
  let u := ZMod.unitOfCoprime p cop
  have pp := pj p hp
  have pr : (0:ℝ) < p := by exact_mod_cast pp.pos
  rw [marked_prime_support J pj p hp,classMass,classMass,
    Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left pp.pos h),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have crt : ((r:ZMod q)=(p*m:ℕ)) ↔ ((r/u : (ZMod q)ˣ):ZMod q)=m := by
    rw [Nat.cast_mul,← ZMod.coe_unitOfCoprime p cop]
    change (r:ZMod q)=(u:ZMod q)*m ↔ _
    constructor
    · intro h
      change (r:ZMod q)*(↑(u⁻¹):ZMod q)=m
      rw [h]
      simp [mul_assoc,mul_comm]
    · intro h
      have hh := congrArg (fun z : ZMod q => z*(u:ZMod q)) h
      change (r:ZMod q)*(↑(u⁻¹):ZMod q)*(u:ZMod q)=(m:ZMod q)*(u:ZMod q) at hh
      simpa [mul_assoc,mul_comm,mul_left_comm] using hh
  change (if (r:ZMod q)=(p*m:ℕ) then _ else 0) =
    (1/(p:ℂ))*(if ((r/u:(ZMod q)ˣ):ZMod q)=m then _ else 0)
  simp only [crt]
  split
  · have eq := gaussian_rescale 1 (p:ℝ) Y S ((p:ℝ)*m) pr.ne' hS.ne'
    rw [mul_div_cancel_left₀ _ pr.ne',one_mul] at eq
    simpa only [Nat.cast_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_natCast] using congrArg Complex.ofReal eq.symm
  · simp

/-- A nonzero extra residue restriction combines with the original
    reduced class into one reduced class at the multiplied modulus. -/
theorem extra_reduced_class {q p : ℕ} (cop : q.Coprime p)
    (r : (ZMod q)ˣ) (s : (ZMod p)ˣ) :
    ∃ c : (ZMod (q*p))ˣ, ∀ (A : Finset ℕ) (w : ℕ → ℂ),
      classMass (A.filter (fun n : ℕ => (s:ZMod p)=(n:ZMod p))) w r = classMass A w c := by
  classical
  let e := ZMod.chineseRemainder cop
  let x : ZMod q × ZMod p := (r,s)
  have ux : IsUnit x := Prod.isUnit_iff.mpr ⟨r.isUnit,s.isUnit⟩
  let uc := ux.map e.symm
  refine ⟨uc.unit,fun A w => ?_⟩
  have proj (n : ℕ) : (uc.unit:ZMod (q*p))=n ↔ (r:ZMod q)=n ∧ (s:ZMod p)=n := by
    rw [uc.unit_spec,← e.injective.eq_iff,e.apply_symm_apply,map_natCast]
    exact Prod.ext_iff
  rw [classMass,classMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [proj n]
  by_cases a : (r:ZMod q)=n <;> by_cases b : (s:ZMod p)=n <;> simp [a,b]

/-- The tilted Euler mass at the divided center has exactly the
    Bernoulli insertion weight from the shared saddle. -/
theorem inserted_tilted_mass (J : Finset ℕ) (p : ℕ) (hp : p ∈ J) (prime : 0 < p)
    (Y α : ℝ) (hy : 0 < Y) :
    1/(p:ℝ)*((Y/(p:ℝ))^(α-1)*eulerMass (J.erase p) α) =
      primeProbability α p*(Y^(α-1)*eulerMass J α) := by
  have pp : (0:ℝ)<p := by exact_mod_cast prime
  have prod : eulerMass J α=(1+(p:ℝ)^(-α))*eulerMass (J.erase p) α :=
    (Finset.mul_prod_erase _ _ hp).symm
  have pw : (p:ℝ)^(α-1)*(p:ℝ)^(-α)=(p:ℝ)⁻¹ := by
    rw [← Real.rpow_add pp,show α-1+-α=(-1:ℝ) by ring,Real.rpow_neg_one]
  have nzp := (Real.rpow_pos_of_pos pp (α-1)).ne'
  have c : 0 < 1+(p:ℝ)^(-α) := by positivity
  rw [prod,primeProbability,Real.div_rpow hy.le pp.le]
  have inv : (p:ℝ)^(-α)*p*(p:ℝ)^(α-1)=1 := by
    calc _ = (p:ℝ)*((p:ℝ)^(α-1)*(p:ℝ)^(-α)) := by ring
         _ = 1 := by rw [pw,mul_inv_cancel₀ pp.ne']
  calc _ = Y^(α-1)*eulerMass (J.erase p) α / ((p:ℝ)*(p:ℝ)^(α-1)) := by ring
       _ = (p:ℝ)^(-α)*(Y^(α-1)*eulerMass (J.erase p) α) := by
           rw [div_eq_iff (mul_ne_zero pp.ne' nzp)]
           calc _ = (Y^(α-1)*eulerMass (J.erase p) α)*1 := by ring
                _ = (Y^(α-1)*eulerMass (J.erase p) α)*((p:ℝ)^(-α)*p*(p:ℝ)^(α-1)) := by rw [inv]
                _ = _ := by ring
       _ = _ := by field_simp


end

end Cogentic.Window
