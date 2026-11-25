import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

open scoped BigOperators

namespace Cogentic.Window

/-- Given a compatible value of the first coordinate, all affine root
    constraints select exactly one class for the remaining integer coefficient. -/
theorem coefficient_fiber_crt (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (r L : ℕ → ℤ) (a x : ℤ)
    (hit : ∀ q ∈ Q, (r q : ZMod q) = a → (x : ZMod q) = L q) :
    let miss := Q.filter (fun q => (r q : ZMod q) ≠ a)
    ∃ c : ℤ, ∀ w : ℤ,
      (∀ q ∈ Q, (x:ZMod q) + ((r q : ZMod q) - a)*w = L q) ↔
      ∃ j : ℤ, w = c+(∏ q ∈ miss, (q:ℤ))*j := by
  classical
  let miss := Q.filter (fun q => (r q : ZMod q) ≠ a)
  have hmem {q : ℕ} (hq : q ∈ miss) : q ∈ Q ∧ (r q:ZMod q) ≠ a := Finset.mem_filter.mp hq
  have cop {p q : ℕ} (h : p ∈ miss) (k : q ∈ miss) (neq : p ≠ q) : p.Coprime q :=
    (Nat.coprime_primes (hp p (hmem h).1) (hp q (hmem k).1)).mpr neq
  let res := fun (q : ℕ) => ((L q : ZMod q)-x)*((r q : ZMod q)-a)⁻¹
  have sol (q : ℕ) (hq : q ∈ miss) (w : ℤ) :
      (x:ZMod q) + ((r q:ZMod q)-a)*w=L q ↔ (w:ZMod q)=res q := by
    let : Fact q.Prime := ⟨hp q (hmem hq).1⟩
    have nz : (r q:ZMod q)-(a:ZMod q) ≠ 0 := sub_ne_zero.mpr (hmem hq).2
    dsimp [res]
    rw [← div_eq_mul_inv,eq_div_iff nz]
    constructor <;> intro h <;> linear_combination (norm := ring) h
  let c := Nat.chineseRemainderOfFinset (fun q => (res q).val) id miss
    (fun i hi => (hp i (hmem hi).1).ne_zero) (fun _ h _ k ne => cop h k ne)
  have castc (q : ℕ) (hq : q ∈ miss) : ((c.val:ℕ):ZMod q)=res q := by
    have : NeZero q := ⟨(hp q (hmem hq).1).ne_zero⟩
    exact ((ZMod.natCast_eq_natCast_iff ..).mpr (c.prop q hq)).trans (ZMod.natCast_zmod_val _)
  refine ⟨(c.val:ℤ),fun w => ⟨?_,?_⟩⟩
  · intro hw
    have dvd (q : ℕ) (hq : q ∈ miss) : (q:ℤ) ∣ w - c.val := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      push_cast
      exact (castc q hq).trans ((sol q hq w).mp (hw q (hmem hq).1)).symm
    obtain ⟨j,eq⟩ := Finset.prod_dvd_of_coprime (t := miss) (s := fun q : ℕ => (q:ℤ))
      (fun _ h _ k ne => (cop h k ne).isCoprime) dvd
    exact ⟨j,by linarith only [eq]⟩
  · rintro ⟨j,hj⟩ q hq
    by_cases m : (r q : ZMod q) = a
    · simpa [m] using hit q hq m
    · have hmiss : q ∈ miss := Finset.mem_filter.mpr ⟨hq,m⟩
      apply (sol q hmiss w).mpr
      rw [← castc q hmiss]
      have hd : (q:ℤ) ∣ w - ↑(c.val) := by
        rw [hj]
        ring_nf
        have hpdiv : (q:ℤ) ∣ ∏ p ∈ miss, (p:ℤ) := Finset.dvd_prod_of_mem _ hmiss
        simpa [mul_comm] using dvd_mul_of_dvd_right hpdiv j
      simpa using ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd).symm

/-- The original polynomial root condition is one affine constraint in the
    shared coefficients whenever the perturbation is a unit at that root. -/
theorem linear_root_constraint (q : ℕ) (prime : q.Prime) (F K r : ℤ)
    (unit : (K:ZMod q) ≠ 0) :
    ∃ c : ℤ, ∀ u v : ℤ, (F+K*(u+r*v) : ℤ) ≡ 0 [ZMOD q] ↔
      (u:ZMod q)+(r:ZMod q)*v = (c:ZMod q) := by
  let : Fact q.Prime := ⟨prime⟩
  obtain ⟨c,hc⟩ := ZMod.intCast_surjective (-((F:ZMod q))/(K:ZMod q))
  refine ⟨c,fun u v => ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff,hc,eq_div_iff unit]
  push_cast
  constructor <;> intro h <;> linear_combination (norm := ring) h

/-- The compatible values of the first coordinate form one congruence class
    modulo precisely the primes whose assigned evaluation coincides with it. -/
theorem first_coordinate_crt (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (r L : ℕ → ℤ) (a : ℤ) :
    let hit := Q.filter (fun q => (r q : ZMod q) = a)
    ∃ c : ℤ, ∀ x : ℤ,
      (∃ w : ℤ, ∀ q ∈ Q, (x:ZMod q) + ((r q : ZMod q) - a)*w = L q) ↔
      ∃ i : ℤ, x=c+(∏ q ∈ hit, (q:ℤ))*i := by
  classical
  let hit := Q.filter (fun q => (r q : ZMod q) = a)
  have ph (q : ℕ) (hq : q ∈ hit) : q.Prime := hp q (Finset.mem_filter.mp hq).1
  have dz (q : ℕ) (hq : q ∈ hit) : (1:ZMod q) ≠ 0 := by
    let : Fact q.Prime := ⟨ph q hq⟩
    exact one_ne_zero
  obtain ⟨c,hc⟩ := coefficient_fiber_crt hit ph (fun _ => 1) L 0 0 (by
    intro q hq neq
    exact (dz q hq (by simpa using neq)).elim)
  have hf : hit.filter (fun q => (1:ZMod q) ≠ 0) = hit :=
    Finset.filter_true_of_mem (fun q hq => by simpa using dz q hq)
  simp only [Int.cast_zero,Int.cast_one,sub_zero,one_mul,zero_add] at hc
  rw [hf] at hc
  refine ⟨c,fun x => ⟨?_,?_⟩⟩
  · rintro ⟨w,h⟩
    apply (hc x).mp
    intro q hq
    simpa [(Finset.mem_filter.mp hq).2] using h q (Finset.mem_filter.mp hq).1
  · intro hx
    have cells := (hc x).mpr hx
    obtain ⟨w,hw⟩ := coefficient_fiber_crt Q hp r L a x
      (fun q hq eq => cells q (Finset.mem_filter.mpr ⟨hq,eq⟩))
    exact ⟨w,(hw w).mpr ⟨0,by simp⟩⟩

/-- Every compatible coefficient pair occurs exactly once in the two
    integer coordinates used in the scalar Gaussian formulas. -/
theorem polynomial_root_lattice (Q : Finset ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (r L : ℕ → ℤ) (a : ℤ) :
    let H := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) = a), (q:ℤ)
    let M := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) ≠ a), (q:ℤ)
    let C := {v : ℤ × ℤ // ∀ q ∈ Q, (v.1:ZMod q)+(r q : ZMod q)*v.2 = L q}
    ∃ (c : ℤ) (d : ℤ → ℤ) (e : (ℤ × ℤ) ≃ C), ∀ i j : ℤ,
      (e (i,j)).val = (c+H*i-a*(d i+M*j), d i+M*j) := by
  classical
  let H := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) = a), (q:ℤ)
  let M := ∏ q ∈ Q.filter (fun q => (r q : ZMod q) ≠ a), (q:ℤ)
  let C := {v : ℤ × ℤ // ∀ q ∈ Q, (v.1:ZMod q)+(r q : ZMod q)*v.2 = L q}
  have hH : H ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => by
    exact_mod_cast (hp q (Finset.mem_filter.mp hq).1).ne_zero
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => by
    exact_mod_cast (hp q (Finset.mem_filter.mp hq).1).ne_zero
  obtain ⟨c,hc⟩ := first_coordinate_crt Q hp r L a
  have existd (i : ℤ) := (hc (c+H*i)).mpr ⟨i,rfl⟩
  have hit (i : ℤ) (q : ℕ) (hq : q ∈ Q) (eq : (r q:ZMod q) = a) : ((c+H*i:ℤ):ZMod q) = L q := by
    obtain ⟨w,hw⟩ := existd i
    simpa only [eq,sub_self,zero_mul,add_zero] using hw q hq
  choose d hd using (fun i : ℤ => coefficient_fiber_crt Q hp r L a (c+H*i) (hit i))
  let f : ℤ × ℤ → C := fun ij => ⟨(c+H*ij.1-a*(d ij.1+M*ij.2),d ij.1+M*ij.2),by
    intro q hq
    have hw := ((hd ij.1 _).mpr ⟨ij.2,rfl⟩) q hq
    change ((c+H*ij.1:ℤ):ZMod q) + ((r q:ZMod q)-a)*((d ij.1+M*ij.2:ℤ):ZMod q)= L q at hw
    push_cast at hw ⊢
    linear_combination (norm := ring) hw⟩
  have fi : Function.Injective f := by
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have x := congrArg (fun u : C => u.val.1) eq
    have y := congrArg (fun u : C => u.val.2) eq
    change c+H*i-a*(d i+M*j)=c+H*k-a*(d k+M*l) at x
    change d i+M*j=d k+M*l at y
    rw [y] at x
    have ik : i=k := mul_left_cancel₀ hH (by linarith only [x] : H*i=H*k)
    subst k
    have jl : j=l := mul_left_cancel₀ hM (by linarith only [y] : M*j=M*l)
    subst l
    rfl
  have fs : Function.Surjective f := by
    rintro ⟨⟨u,w⟩,hw⟩
    have transformed (q : ℕ) (hq : q ∈ Q) :
        ((u+a*w:ℤ):ZMod q)+((r q:ZMod q)-a)*w=L q := by
      push_cast
      linear_combination (norm := ring) hw q hq
    obtain ⟨i,hi⟩ := (hc (u+a*w)).mp ⟨w,transformed⟩
    change u+a*w=c+H*i at hi
    have eq := transformed
    rw [hi] at eq
    obtain ⟨j,hj⟩ := (hd i w).mp eq
    refine ⟨(i,j),Subtype.ext ?_⟩
    change (c+H*i-a*(d i+M*j),d i+M*j)=(u,w)
    change w=d i+M*j at hj
    rw [← hj,← hi]
    simp
  exact ⟨c,d,Equiv.ofBijective f ⟨fi,fs⟩,fun _ _ => rfl⟩

end Cogentic.Window
