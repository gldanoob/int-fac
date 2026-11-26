import Cogentic.CompiledColumns
import Cogentic.SolverStageParameters

namespace Cogentic.BinaryProjection
open BinaryDivision BinaryPivot Finset

/-- Form an integer weighted dot product on the shared column denominator.
The final quotient is rounded once at the precision of the minor system. -/
def observe {m d : ℕ} (z : Vector (Vector ℤ d) m) (c : Vector ℤ m) (k : Fin d) (src dst : ℕ) : ℤ × ℕ :=
  let productAt (i : Fin m) := cross (encode (c.get i)) (encode ((z.get i).get k)) (encode 0) (encode 0)
  let y := fun (i : ℕ) =>if h : i < m then (productAt ⟨i,h⟩).1 else encode 0
  let dot := sumPrefix y m
  let out := roundWord dot.1 src dst
  (out.1,(∑ i : Fin m,(productAt i).2)+dot.2+out.2+1)

def readCols {m d : ℕ} (z : Vector (Vector ℤ d) m) (src : ℕ) :=
  z.map (fun v=>v.map (fun (t:ℤ)=>(t:ℚ)/2^src))

theorem observe_spec {m d : ℕ} (z : Vector (Vector ℤ d) m) (c : Vector ℤ m) (k : Fin d)
    (src dst W : ℕ) (cw : ∀ i,(c.get i).natAbs.size≤W) (zw : ∀ i,((z.get i).get k).natAbs.size≤W)
    (mw : m≤W) (sw : src+1≤W) (dw : dst≤W) :
    let out := observe z c k src dst
    out.1=(Concrete.observation (readCols z src) c dst).get k ∧ out.2≤1000000*(W+1)^3 := by
  let productAt (i : Fin m) := cross (encode (c.get i)) (encode ((z.get i).get k)) (encode 0) (encode 0)
  let y := fun (i : ℕ) =>if h : i < m then (productAt ⟨i,h⟩).1 else encode 0
  let dot := sumPrefix y m
  have widths (i : Fin m) : (encode (c.get i)).digits.length≤W ∧
      (encode ((z.get i).get k)).digits.length≤W := by simpa only [encode,Nat.size_eq_bits_len] using And.intro (cw i) (zw i)
  have zero : (encode 0).digits.length≤W := by simp [encode]
  have termSpec (i : Fin m) : (productAt i).1.decode=c.get i*(z.get i).get k ∧
      (productAt i).1.digits.length≤3*W+1 ∧ (productAt i).2≤32*W^2+75*W+10 := by
    obtain ⟨eq,cost⟩ := cross_spec _ _ _ _ W (widths i).1 (widths i).2 zero zero
    exact ⟨by simpa [productAt] using eq,BinaryReconstruction.cross_length _ _ _ _ (widths i).1 (widths i).2 zero zero,cost⟩
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
  constructor
  · change (roundWord dot.1 src dst).1 = (Concrete.observation (readCols z src) c dst).get k
    simp only [Concrete.observation,Vector.get_eq_getElem,Vector.getElem_ofFn,Concrete.numerator]
    simp only [Vector.get_eq_getElem] at f
    exact_mod_cast f
  have total := sum_le_sum (s:=univ) (fun i _=>(termSpec i).2.2)
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at total
  have prod := total.trans (Nat.mul_le_mul_right _ mw)
  have adds := cost.trans (show m*(25*(3*W+1+m)+9)≤W*(25*(3*W+1+W)+9) by gcongr)
  change (∑ i,(productAt i).2)+dot.2+(roundWord dot.1 src dst).2+1≤_
  nlinarith only [prod,adds,roundCost]

private theorem numerator_size {m d : ℕ} (cols : Vector (Vector ℤ d) m) (P C H L : ℕ)
    (ch : C*2^P ≤ H) (ph : 2^P ≤ H) (hWidth : H.size ≤ L)
    (raw : ∀ i k, |((readCols cols (3*P/2)).get i).get k| ≤ (C:ℚ))
    (i : Fin m) (k : Fin d) : ((cols.get i).get k).natAbs.size ≤ 4*L+1 := by
  have e := raw i k
  simp only [readCols,Vector.get_eq_getElem,Vector.getElem_map,abs_div,abs_of_pos (show (0:ℚ)<2^(3*P/2) by positivity)] at e
  have f := (div_le_iff₀ (show (0:ℚ)<2^(3*P/2) by positivity)).mp e
  have zi : |(cols.get i).get k| ≤ ((C*2^(3*P/2):ℕ):ℤ) := by exact_mod_cast f
  rw [Int.abs_eq_natAbs] at zi
  have bound : ((cols.get i).get k).natAbs ≤ C*2^(3*P/2) := by exact_mod_cast zi
  have sq : C*2^(3*P/2) ≤ H*H := calc
    _ ≤ C*2^(P+P) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    _ = (C*2^P)*2^P := by rw [pow_add,mul_assoc]
    _ ≤ _ := Nat.mul_le_mul ch ph
  apply Nat.size_le.mpr
  have tight := Nat.size_le.mp hWidth
  have hh : H*H < 2^L*2^L := Nat.mul_lt_mul_of_lt_of_le tight tight.le (Nat.two_pow_pos _)
  exact (bound.trans sq).trans_lt (hh.trans_le (by rw [←pow_add]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

/-- Every right-hand-side and direction observation, before the list of minors
is examined. Inputs are the binary column numerators already computed. -/
def observationWork (s : Marking.Input) (rel : Marking.Relations) (lat : Elimination.IntegerFamily rel.marks.length)
    (cols : Vector (Vector ℤ (2*s.degree-2)) rel.marks.length) : ℕ :=
  let P := TryPair.localBits s rel
  let run := fun (c : Vector ℤ rel.marks.length) => ∑ k : Fin (2*s.degree-2),(observe cols c k (3*P/2) P).2
  run lat.particular+∑ j,run (lat.directions.get j)

/-- On every candidate reaching the minor scan, all observations decode to
the actual rounded system and their combined gate count fits the search scale. -/
theorem constructed_observations {n ell u v w z : ℕ} (hn : 2 ≤ n)
    (large : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
        w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (Construction.construct n ell u v w z)
    ∀ {rel}, Marking.stageOne s = some rel → ∀ {lat}, Elimination.stageTwo rel = some lat →
    lat.free < rel.marks.length →
    ∃ cols, columnWords s rel = some cols ∧
      let P := TryPair.localBits s rel
      Concrete.markColumns s rel = some (readCols cols (3*P/2)) ∧
      (∀ c, (c = lat.particular ∨ ∃ j, c = lat.directions.get j) →
        ∀ k, (observe cols c k (3*P/2) P).1 = (Concrete.observation (readCols cols (3*P/2)) c P).get k) ∧
      observationWork s rel lat cols ≤ 2^(150050*TwoThirdsCost.scale (n.log2+1)) := by
  intro s rel stage lat solved free
  obtain ⟨cols,words,readout⟩ := constructed_column_words hn large target box stage
  refine ⟨cols,words,readout,?_⟩
  let P := TryPair.localBits s rel
  let C := 2*s.degree*(s.L₀+1)+1
  let T := (rel.rows.length+1).factorial
  let H := rel.marks.length*T*C*2^P+1
  let S := TwoThirdsCost.scale (n.log2+1)
  let L := 2^(30000*S)
  let W := 4*L+1
  obtain ⟨sp,marks,_,dim,hWidth⟩ := SolverStage.fixed_parameters stage
  change 0<S at sp
  change rel.marks.length≤L at marks
  change 2*s.degree-2≤L at dim
  change H.size≤L at hWidth
  have lp : 0<L := Nat.two_pow_pos _
  have tp : 0<T := Nat.factorial_pos _
  have cp : 0<C := Nat.succ_pos _
  have mp : 0<rel.marks.length := (Nat.zero_le _).trans_lt free
  have mc : 1 ≤ rel.marks.length*T := Nat.mul_pos mp tp
  have ch : C*2^P ≤ H := (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left C mc)).trans (Nat.le_succ _)
  have th : T ≤ H := by
    calc T ≤ rel.marks.length*T := Nat.le_mul_of_pos_left _ mp
         _ ≤ rel.marks.length*T*C := Nat.le_mul_of_pos_right _ cp
         _ ≤ rel.marks.length*T*C*2^P := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
         _ ≤ _ := Nat.le_succ _
  have ph : 2^P ≤ H := (Nat.le_mul_of_pos_left _ cp).trans ch
  have prec := (Nat.size_le_size ph).trans hWidth
  rw [Nat.size_pow] at prec
  have rawBound := Concrete.constructed_entry_bound hn large target box stage readout
  have colwidth := numerator_size cols P C H L ch ph hWidth rawBound
  have height := stageTwo_height solved
  have spec (c : Vector ℤ rel.marks.length) (bound : ∀ i, |c.get i| ≤ (T:ℤ)) (k) :=
    observe_spec cols c k (3*P/2) P W (fun i => by
      have ci := bound i
      rw [Int.abs_eq_natAbs] at ci
      have hi : (c.get i).natAbs ≤ T := by exact_mod_cast ci
      exact ((Nat.size_le_size (hi.trans th)).trans hWidth).trans (by dsimp [W]; omega))
      (fun i => colwidth i k) (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega)
  constructor
  · intro c hc k
    rcases hc with rfl | mem
    · exact (spec _ height.1.2 k).1
    · obtain ⟨j,rfl⟩ := mem
      exact (spec _ (height.2 j).2 k).1
  · let N := (2*s.degree-2)*(1000000*(W+1)^3)
    have one (c : Vector ℤ rel.marks.length) (bd : ∀ i, |c.get i| ≤ (T:ℤ)) :
        (∑ k, (observe cols c k (3*P/2) P).2) ≤ N := by
      simpa only [N,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] using
        (sum_le_sum (s := univ) (fun k _ => (spec c bd k).2))
    have dirs := sum_le_sum (s := univ) (fun j _ => one _ (height.2 j).2)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at dirs
    change _ + _ ≤ _
    apply (Nat.add_le_add (one _ height.1.2) dirs).trans
    calc
      _ = (lat.free+1)*N := by rw [Nat.succ_mul]; omega
      _ ≤ L*(L*(2^20*(2^3*L)^3)) := by
        have f : lat.free+1≤L := (Nat.succ_le_of_lt free).trans marks
        have ws : W+1≤2^3*L := by dsimp [W]; omega
        dsimp only [N]; gcongr; decide
      _ = 2^(30000*S+(30000*S+(20+(3+30000*S)*3))) := by dsimp only [L]; rw [←pow_add 2 3 _,←pow_mul,←pow_add,←pow_add,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryProjection

#print axioms Cogentic.BinaryProjection.constructed_observations
