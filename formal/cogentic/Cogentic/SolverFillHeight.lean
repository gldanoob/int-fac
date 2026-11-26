import Cogentic.BackSubstitutionWork

namespace Cogentic.SolverStage
open Elimination Finset

def fillWidth (N m H : ℕ) := 2*fillExponent (N+1) m H+3

private def qWidth (x : ℚ) := max x.num.natAbs.size x.den.size

private theorem of_height {x : ℚ} {a t : ℕ} (hn : |x.num|≤(a:ℤ)) (hd : (x.den:ℤ)≤a) (up : a≤2^t) :
    qWidth x≤t+1 := by
  rw [Int.abs_eq_natAbs] at hn
  have h : ∀ i≤a,i.size≤t+1 := fun i hi=>(Nat.size_le_size (hi.trans up)).trans_eq Nat.size_pow
  exact max_le (h _ (by exact_mod_cast hn)) (h _ (by exact_mod_cast hd))

/-- The operands of each binary operation in a pivot's dot product, then
its final numerator and divisor, fit one bound for the original system.
The estimate covers every subset of the dot product, including single terms. -/
theorem recover_operand_widths {N n H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base,∀ j,(r.aug j).natAbs≤H) {rows : List (Row (n+1))}
    (reach : SolveStep base rows) (dim : n≤N) (p : Row (n+1)) (pm : p∈rows)
    {f : Family n} (tail : solve n (rows.map p.reduce)=some f)
    (found : rows.find? (fun r=>r.head != 0)=some p) (y : Fin f.free→ℤ) (hy : ∀ j, |y j|≤1) :
    let x := f.values (fun i=>(y i:ℚ));let a := p.drop.coeffs.get
    let w := fun z : ℚ=>max z.num.natAbs.size z.den.size
    let W := fillWidth N base.length H
    (∀ i,w (x i)≤W) ∧ (∀ j,w (p.aug j:ℚ)≤W) ∧
    (∀ s : Finset (Fin n),w (∑ i∈s,(a i:ℚ)*x i)≤W) ∧
    w ((p.rhs:ℚ)-(∑ i,(a i:ℚ)*x i))≤W := by
  intro x a w W
  let C := (base.length+1).factorial*H^(base.length+1)
  let B := (n+1).factorial*C^n
  let G := (N+2).factorial*C^(N+1)
  let t := fillExponent (N+1) base.length H
  have cp : 0<C := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hp)
  have gp : 0<G := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos cp)
  have leSquare : (G:ℤ) ≤ (G:ℤ)^2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left (show (1:ℤ)≤G by exact_mod_cast gp) (Int.natCast_nonneg G)
  have boundG : G≤2^t := fill_height_exp (N+1) base.length H
  have cG : C≤G := (Nat.le_self_pow (Nat.succ_ne_zero N) C).trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _))
  have new : (n+2).factorial*C^(n+1)≤G := Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right cp (by omega))
  have bG : B≤G := Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right cp (by omega))
  have wide : t+1≤W := by change _≤2*t+3;omega
  have coeff (j) : (p.aug j).natAbs≤C := solve_intermediate_height base hp input reach p pm j
  have aux (i) : |a i|≤(C:ℤ) := by
    rw [Int.abs_eq_natAbs]
    have h := coeff (some i.succ)
    simpa only [a,Row.aug,Option.elim_some,Row.drop,Vector.get_eq_getElem,Vector.getElem_ofFn,
      Int.ofNat_le] using (Int.ofNat_le.mpr h)
  have frac : BoundedFraction x (B:ℤ) := solve_back_substitution_height base hp input (.pivot reach found) tail y hy
  have partialWidth (s : Finset (Fin n)) :
      let z := ∑ i∈s,(a i:ℚ)*x i
      |z.num|≤(G:ℤ) ∧ (z.den:ℤ)≤G := by
    have rc := frac.partial_sum a aux (Int.natCast_nonneg _) s
    have sz : s.card≤n := (card_le_univ s).trans_eq (Fintype.card_fin n)
    have sz' : s.card*C+1≤(n+2)*C := by nlinarith only [Nat.mul_le_mul_right C sz,cp]
    have scale : (s.card*C+1)*B≤G :=
      ((Nat.mul_le_mul_right B sz').trans_eq (by dsimp only [B];rw [Nat.factorial_succ (n+1),pow_succ];ring)).trans new
    have scale' : ((s.card:ℤ)*(C:ℤ)+1)*(B:ℤ)≤(G:ℤ) := by exact_mod_cast scale
    exact ⟨rc.1.trans scale',rc.2.trans scale'⟩
  refine ⟨fun i=>?_,fun j=>?_,fun s=>(of_height (partialWidth s).1 (partialWidth s).2 boundG).trans wide,?_⟩
  · obtain ⟨u,v⟩ := frac.reduced i
    exact (of_height u v (bG.trans boundG)).trans wide
  · have upper := (coeff j).trans (cG.trans boundG)
    exact (of_height (x:=(p.aug j:ℚ)) (by simpa only [Rat.num_intCast,Int.abs_eq_natAbs] using (Int.ofNat_le.mpr upper))
      (by simpa only [Rat.den_intCast,Nat.cast_one] using (show (1:ℤ)≤((2^t:ℕ):ℤ) by exact_mod_cast Nat.two_pow_pos t)) le_rfl).trans wide
  · let d := ∑ i,(a i:ℚ)*x i
    let num := p.rhs*(d.den:ℤ)-d.num
    have dh := partialWidth univ
    change |d.num|≤(G:ℤ) ∧ (d.den:ℤ)≤G at dh
    have rhs : |p.rhs|≤(G:ℤ) := by rw [Int.abs_eq_natAbs];exact_mod_cast (coeff none).trans cG
    have ng : |num|≤(2*G^2:ℕ) := by
      have bound : |p.rhs*(d.den:ℤ)| ≤ (G:ℤ)*(G:ℤ) := by
        rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
        exact mul_le_mul rhs dh.2 (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      dsimp only [num]
      push_cast
      exact (abs_sub (p.rhs*(d.den:ℤ)) d.num).trans (by nlinarith only [bound,dh.1,leSquare])
    have full : BoundedFraction (fun _ : Fin 1=>(p.rhs:ℚ)-d) ((2*G^2:ℕ):ℤ) := by
      refine ⟨d.den,by exact_mod_cast d.pos.ne',?_,fun _=>num,fun _=>ng,fun _=>?_⟩
      · rw [abs_of_nonneg (Int.natCast_nonneg _)]
        apply dh.2.trans;push_cast
        nlinarith only [leSquare,sq_nonneg (G:ℤ)]
      · dsimp only [num]; push_cast
        rw [sub_mul,Rat.mul_den_eq_num]
    have last := full.reduced 0
    have up : 2*G^2≤2^(2*t+1) := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left boundG 2)).trans_eq (by
      rw [←pow_mul,pow_succ]; ring_nf)
    exact (of_height last.1 last.2 up).trans (by change 2*t+1+1≤2*t+3;omega)

end Cogentic.SolverStage
