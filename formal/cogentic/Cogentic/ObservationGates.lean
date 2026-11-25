import Cogentic.CompiledColumns
import Cogentic.MinorVerificationWork

namespace Cogentic.BinaryProjection
open BinaryDivision BinaryPivot Finset

/-- Form an integer weighted dot product on the shared column denominator.
The final quotient is rounded once at the precision of the minor system. -/
def observe {m d : ℕ} (z : Vector (Vector ℤ d) m) (c : Vector ℤ m) (k : Fin d) (src dst : ℕ) : ℤ × ℕ :=
  let term (i : Fin m) := cross (encode (c.get i)) (encode ((z.get i).get k)) (encode 0) (encode 0)
  let y := fun i=>if h : i<m then (term ⟨i,h⟩).1 else encode 0
  let dot := sumPrefix y m
  let out := roundWord dot.1 src dst
  (out.1,(∑ i : Fin m,(term i).2)+dot.2+out.2+1)

private def readCols {m d : ℕ} (z : Vector (Vector ℤ d) m) (src : ℕ) :=
  z.map (fun v=>v.map (fun (t:ℤ)=>(t:ℚ)/2^src))

theorem observe_spec {m d : ℕ} (z : Vector (Vector ℤ d) m) (c : Vector ℤ m) (k : Fin d)
    (src dst W : ℕ) (cw : ∀ i,(c.get i).natAbs.size≤W) (zw : ∀ i,((z.get i).get k).natAbs.size≤W)
    (mw : m≤W) (sw : src+1≤W) (dw : dst≤W) :
    let out := observe z c k src dst
    out.1=(Concrete.observation (readCols z src) c dst).get k ∧ out.2≤1000000*(W+1)^3 := by
  let term (i : Fin m) := cross (encode (c.get i)) (encode ((z.get i).get k)) (encode 0) (encode 0)
  let y := fun i=>if h : i<m then (term ⟨i,h⟩).1 else encode 0
  let dot := sumPrefix y m
  have widths (i : Fin m) : (encode (c.get i)).digits.length≤W ∧
      (encode ((z.get i).get k)).digits.length≤W := by simpa only [encode,Nat.size_eq_bits_len] using And.intro (cw i) (zw i)
  have zero : (encode 0).digits.length≤W := by simp [encode]
  have termSpec (i : Fin m) : (term i).1.decode=c.get i*(z.get i).get k ∧
      (term i).1.digits.length≤3*W+1 ∧ (term i).2≤32*W^2+75*W+10 := by
    obtain ⟨eq,cost⟩ := cross_spec _ _ _ _ W (widths i).1 (widths i).2 zero zero
    exact ⟨by simpa [term] using eq,BinaryReconstruction.cross_length _ _ _ _ (widths i).1 (widths i).2 zero zero,cost⟩
  obtain ⟨ev,len,cost⟩ := sumPrefix_spec y m (3*W+1) (fun i hi=>by simpa only [y,dif_pos hi] using (termSpec ⟨i,hi⟩).2.1)
  change dot.1.decode=_ at ev; change dot.1.digits.length≤_ at len; change dot.2≤_ at cost
  have valt : dot.1.decode=∑ i : Fin m,c.get i*(z.get i).get k := by
    rw [ev,←Fin.sum_univ_eq_sum_range (fun i=>(y i).decode) m]
    exact sum_congr rfl (fun i _=>by simpa only [y,dif_pos i.isLt] using (termSpec i).1)
  have ⟨floor,roundCost⟩ := roundWord_spec dot.1 src dst (4*W+1) (by omega) (by omega) (by omega)
  have dotEq : (dot.1.decode:ℚ)/2^src=∑ i : Fin m,(c.get i:ℚ)*((readCols z src).get i).get k := by
    rw [valt]; push_cast; rw [sum_div]
    exact sum_congr rfl (fun i _=>by simp [readCols,Vector.get_eq_getElem,mul_div_assoc])
  rw [dotEq] at floor
  unfold ArchNumerics.roundDyadic at floor
  have f := (div_left_inj' (by positivity : (2:ℚ)^dst≠0)).mp floor
  refine ⟨by exact_mod_cast f,?_⟩
  have total := sum_le_sum (s:=univ) (fun i _=>(termSpec i).2.2)
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at total
  have prod := total.trans (Nat.mul_le_mul_right _ mw)
  have adds := cost.trans (show m*(25*(3*W+1+m)+9)≤W*(25*(3*W+1+W)+9) by gcongr)
  change (∑ i,(term i).2)+dot.2+(roundWord dot.1 src dst).2+1≤_
  nlinarith only [prod,adds,roundCost]

/-- Every right-hand-side and direction observation, before the list of minors
is examined. Inputs are the binary column numerators already computed. -/
def observationWork (s : Marking.Input) (rel : Marking.Relations) (lat : Elimination.IntegerFamily rel.marks.length)
    (cols : Vector (Vector ℤ (2*s.degree-2)) rel.marks.length) : ℕ :=
  let P := TryPair.localBits s rel
  let run := fun c=>∑ k : Fin (2*s.degree-2),(observe cols c k (3*P/2) P).2
  run lat.particular+∑ j,run (lat.directions.get j)

end Cogentic.BinaryProjection
