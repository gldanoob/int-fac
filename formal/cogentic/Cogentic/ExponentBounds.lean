import Cogentic.ArchPrecision
import Cogentic.ConstructionReduction

/-! Finite-base row and final exponent bounds for the executable pair attempt. -/

open Polynomial
open scoped BigOperators Matrix
namespace Cogentic
open Marking

private theorem guarded_roots {s : Input} {cs : List ℤ} (guard : s.polynomialGuard cs)
    {q : ℕ} (listed : q ∈ s.base) :
    letI : Fact q.Prime := ⟨(mem_base.mp listed).2.1⟩
    let F := (polynomial cs).map (Int.castRingHom (ZMod q))
    F ≠ 0 ∧ F.roots.toFinset.card ≤ s.degree := by
  classical
  let : Fact q.Prime := ⟨(mem_base.mp listed).2.1⟩
  intro F
  have cp := (mem_base.mp listed).2.2.2.of_dvd_right (dvd_mul_right s.leading s.n)
  have cop : ¬q ∣ s.leading := (mem_base.mp listed).2.1.coprime_iff_not_dvd.mp cp
  have last : cs[s.degree]? = some (s.leading:ℤ) := by
    simpa [List.getLast?_eq_getElem?,guard.1] using guard.2.1
  have cf : F.coeff s.degree = (s.leading : ZMod q) := by
    simpa [F,List.getD_eq_getElem?_getD,last] using Construction.coefficient_rep (R:=ZMod q) cs s.degree
  have fd : F.natDegree ≤ s.degree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simpa [F,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by have := guard.1; omega : cs.length ≤ j)] using
      Construction.coefficient_rep (R:=ZMod q) cs j
  refine ⟨?_,(Multiset.toFinset_card_le _).trans (F.card_roots'.trans fd)⟩
  intro zero
  apply cop
  apply (ZMod.natCast_eq_zero_iff ..).mp
  simpa [zero] using cf.symm

/-- At most d residues per side and base prime are retained. This sharp
count makes the fixed global precision at least every successfully used local precision. -/
theorem retained_root_row_cap {s : Input} {rel : Relations} (ok : stageOne s = some rel) :
    rel.rows.length ≤ 2*s.degree*s.B := by
  classical
  obtain ⟨guards,_,_,same,_⟩ := rows_and_guards ok
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,ga,gb⟩ := guards
  have member {r : Row} (h : r ∈ rel.rows.toFinset) : r ∈ s.rows := by
    have k : r ∈ s.clean := by simpa [← same] using h
    exact (mem_clean.mp k).1
  have nodup : rel.rows.Nodup := by rw [same]; exact (List.nodup_dedup _).filter _
  let key := fun r : Row => (r.second,r.q)
  let base := Finset.Icc 1 s.B
  let choices := Finset.univ (α:=Bool) ×ˢ base
  have maps (r : Row) (h : r ∈ rel.rows.toFinset) : key r ∈ choices := by
    have q := mem_base.mp (mem_rows.mp (member h)).1
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_Icc.mpr ⟨q.2.1.pos,q.2.2.1⟩⟩
  have fibers (t : Bool × ℕ) (_ht : t ∈ choices) :
      (rel.rows.toFinset.filter (fun r => key r=t)).card ≤ s.degree := by
    rcases t with ⟨side,q⟩
    let fiber := rel.rows.toFinset.filter (fun r => key r = (side,q))
    change fiber.card ≤ s.degree
    rcases fiber.eq_empty_or_nonempty with empty|⟨r,belongs⟩
    · simp [empty]
    have rinfo {a : Row} (h : a ∈ fiber) :
        a.second=side ∧ a.q=q ∧ a.r<q ∧
        (polynomial (s.coeffs side)).eval₂ (Int.castRingHom (ZMod q)) (a.r : ZMod q) = 0 := by
      obtain ⟨inside,eq⟩ := Finset.mem_filter.mp h
      have sides : a.second = side := congrArg Prod.fst eq
      have primes : a.q = q := congrArg Prod.snd eq
      have aroot := mem_rows.mp (member inside)
      exact ⟨sides,primes,primes ▸ aroot.2.1,by subst q; simpa only [sides] using aroot.2.2⟩
    have inBase := (mem_rows.mp (member (Finset.mem_filter.mp belongs).1)).1
    rw [(rinfo belongs).2.1] at inBase
    let : Fact q.Prime := ⟨(mem_base.mp inBase).2.1⟩
    let F := (polynomial (s.coeffs side)).map (Int.castRingHom (ZMod q))
    have guard : s.polynomialGuard (s.coeffs side) := by cases side; exact ga; exact gb
    obtain ⟨nonzero,count⟩ := guarded_roots guard inBase
    have send (a : Row) (h : a ∈ fiber) : (a.r : ZMod q) ∈ F.roots.toFinset := by
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots nonzero).mpr
      exact (Polynomial.eval_map ..).trans (rinfo h).2.2.2
    have inj : Set.InjOn (fun a : Row => (a.r : ZMod q)) (fiber : Set Row) := by
      intro a ha c hc eq
      have ⟨sideA,primeA,rA,_⟩ := rinfo ha
      have ⟨sideC,primeC,rC,_⟩ := rinfo hc
      have res : a.r = c.r := by simpa only [ZMod.val_natCast_of_lt rA,ZMod.val_natCast_of_lt rC] using congrArg ZMod.val eq
      cases a; cases c
      exact (Row.mk.injEq ..).mpr ⟨sideA.trans sideC.symm,primeA.trans primeC.symm,res⟩
    exact (Finset.card_le_card_of_injOn _ send inj).trans count
  have size := Finset.card_le_mul_card_image_of_maps_to maps s.degree fibers
  rw [List.toFinset_card_of_nodup nodup] at size
  simpa [choices,base,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using size

/-- Any reconstructed denominator inside the proven Q cap passes the final
exponent comparison against the minimum of global and local bit caps. -/
theorem fixed_exponent_fits {N target : ℕ} {pair : TryPair.PairData} {rel : Relations}
    {out : Elimination.IntegerFamily rel.marks.length}
    (marked : Marking.stageOne (TryPair.fixedInput N target pair) = some rel)
    (solved : Elimination.stageTwo rel = some out) (big : 300 ≤ Fixed.d (N.log2+1)) (m : ℕ) :
    let s := TryPair.fixedInput N target pair
    m ≤ TryPair.denominatorCap s rel →
      2*(out.scale*m) ≤ 2^(min (TryPair.localBits s rel) (Fixed.precision (N.log2+1))) := by
  intro s cap
  let b := N.log2+1
  let d := Fixed.d b
  let R := rel.rows.length+1
  let k := 10010*Fixed.h b
  have env := ArchPrecision.fixed_envelope marked big
  have dp : 1 ≤ d := env.degree
  have rp : 1 ≤ R := env.rowCount
  have bp : 1 ≤ b := env.bits
  have row := retained_root_row_cap marked
  change rel.rows.length ≤ 2*d*Fixed.B b at row
  have local_le : TryPair.localBits s rel ≤ Fixed.precision b := by
    change 64*d^3*R*b ≤ 64*d^3*(2*d*Fixed.B b+1)*b
    gcongr; exact Nat.add_le_add_right row 1
  rw [min_eq_left local_le]
  have coeff := (stageTwo_height solved).1.1
  have Rsmall : R ≤ 2^k := env.rows_le
  have ksmall : k ≤ b := by have := env.budget; change 8*k ≤ b at this; omega
  have cb : out.scale ≤ 2^(R*b) := by
    calc
      _ ≤ R.factorial := coeff
      _ ≤ R^R := Nat.factorial_le_pow R
      _ ≤ (2^k)^R := Nat.pow_le_pow_left Rsmall R
      _ = 2^(k*R) := (Nat.pow_mul 2 k R).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simpa [Nat.mul_comm R] using Nat.mul_le_mul_right R ksmall)
  change m ≤ 2^(3*d*R*b) at cap
  calc
    _ ≤ 2*(2^(R*b)*2^(3*d*R*b)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul cb cap)
    _ = 2^(1+R*b+3*d*R*b) := by rw [Nat.pow_add,Nat.pow_add]; ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      change 1+R*b+3*d*R*b ≤ 64*d^3*R*b
      have a := Nat.mul_le_mul_right (R*b) (Nat.le_self_pow (by decide : 3≠0) d)
      have c := Nat.mul_pos rp bp
      have e := Nat.le_mul_of_pos_left (R*b) dp
      nlinarith only [a,c,e]

end Cogentic
