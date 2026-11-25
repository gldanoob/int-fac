import Cogentic.Marking

namespace Cogentic.Marking

private theorem zero_at_mark (cs : List ℤ) (a q : ℕ) :
    ((horner ((a%q:ℕ):ZMod q) cs).1=0 ↔ q∣value cs a) ∧
    ((horner ((a%q:ℕ):ZMod q) cs).2=0 ↔ q∣(horner (a:ℤ) cs).2.natAbs) := by
  have cast (f : Polynomial ℤ) :
      f.eval₂ (Int.castRingHom (ZMod q)) ((a%q:ℕ):ZMod q) = ((f.eval (a:ℤ):ℤ):ZMod q) := by
    rw [ZMod.natCast_mod]
    simpa only [Int.coe_castRingHom,Int.cast_natCast] using
      (Polynomial.eval₂_at_apply (p:=f) (Int.castRingHom (ZMod q)) (a:ℤ))
  have vanishes (v : ℤ) : (v:ZMod q)=0 ↔ q∣v.natAbs :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).trans (Int.dvd_natAbs.symm.trans Int.natCast_dvd_natCast)
  simp only [value,horner_correct,cast,vanishes]
  exact ⟨Iff.rfl,Iff.rfl⟩

/-- After both smoothness tests, the bad-row filter is exactly three gcd
tests on the two integer values and their derivatives at the mark. -/
theorem avoids_badRows_iff_coprime (s : Input) (a : ℕ)
    (smooth : ∀ i : Bool, SquarefreeSmooth s.base (value (s.coeffs i) a)) :
    (∀ row ∈ s.badRows, a%row.q ≠ row.r) ↔
      (value s.first a).Coprime (value s.second a) ∧
      ∀ i : Bool, (value (s.coeffs i) a).Coprime (horner (a:ℤ) (s.coeffs i)).2.natAbs := by
  let val := fun i => value (s.coeffs i) a
  let der := fun i => (horner (a:ℤ) (s.coeffs i)).2.natAbs
  let row := fun i p => Row.mk i p (a%p)
  have bad (i : Bool) (p : ℕ) (prime : p.Prime) (hit : p∣val i) :
      row i p∈s.badRows ↔ p∣der i ∨ p∣val (!i) := by
    have base := (smooth i).2.2 p prime hit
    have root := (zero_at_mark (s.coeffs i) a p).1.mpr hit
    have member : row i p∈s.rows := mem_rows.mpr ⟨base,Nat.mod_lt _ prime.pos,by simpa only [horner_correct] using root⟩
    change row i p∈s.rows.filter (fun j => j.bad s) ↔ _
    rw [List.mem_filter,and_iff_right member]
    simp only [row,Row.bad,Row.isRoot,Bool.or_eq_true,decide_eq_true_eq]
    exact or_congr (zero_at_mark (s.coeffs i) a p).2 (zero_at_mark (s.coeffs (!i)) a p).1
  constructor
  · intro avoid
    have clean (i : Bool) (p : ℕ) (pp : p.Prime) (hit : p∣val i) : ¬(p∣der i ∨ p∣val (!i)) :=
      fun h => avoid _ ((bad i p pp hit).mpr h) rfl
    refine ⟨Nat.coprime_of_dvd (fun p pp hit other => clean false p pp hit (.inr other)),?_⟩
    exact fun i => Nat.coprime_of_dvd (fun p pp hit slope => clean i p pp hit (.inl slope))
  · rintro ⟨cop,simple⟩ ⟨i,p,r⟩ mem eq
    change a%p = r at eq
    subst r
    have hm := mem_rows.mp (List.mem_filter.mp mem).1
    have pp := (mem_base.mp hm.1).2.1
    have hit : p∣val i := (zero_at_mark (s.coeffs i) a p).1.mp (by simpa only [horner_correct] using hm.2.2)
    rcases (bad i p pp hit).mp mem with md|shared
    · exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt hit md (simple i)
    · cases i
      · exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt hit shared cop
      · exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt shared hit cop

end Cogentic.Marking
