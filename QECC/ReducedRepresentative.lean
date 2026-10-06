import QECC.FiniteDiagonal

namespace QECC

noncomputable section

/-- Apply the standard embedding `ZMod q -> R/Z` coordinatewise. -/
def phaseHom (n q : ℕ) (hq : 0 < q) :
    (Fin n → ZMod q) →+ PhaseVector n := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact
    { toFun := fun a j => ZMod.toAddCircle (a j)
      map_zero' := by
        funext j
        simp
      map_add' := by
        intro a b
        funext j
        simp }

theorem phaseHom_injective (n q : ℕ) (hq : 0 < q) :
    Function.Injective (phaseHom n q hq) := by
  letI : NeZero q := ⟨hq.ne'⟩
  intro a b hab
  funext j
  apply ZMod.toAddCircle_injective q
  exact congrFun hab j

/-- A phase vector encoded by residues modulo its exact common denominator. -/
structure ReducedDiagonalRepresentative (n : ℕ) where
  q : ℕ
  q_ge_two : 2 ≤ q
  a : Fin n → ZMod q
  primitive : addOrderOf a = q

namespace ReducedDiagonalRepresentative

/-- The literal common gcd of `q` and the canonical numerators in `0, ..., q - 1`. -/
def commonGCD {n : ℕ} (R : ReducedDiagonalRepresentative n) : ℕ :=
  Nat.gcd R.q (Finset.univ.gcd fun j : Fin n => (R.a j).val)

/-- Exact order of the residue vector implies the paper's reduced-form gcd condition. -/
theorem commonGCD_eq_one {n : ℕ} (R : ReducedDiagonalRepresentative n) :
    R.commonGCD = 1 := by
  let g := R.commonGCD
  have hqpos : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hqpos.ne'⟩
  have hgq : g ∣ R.q := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgq hqpos
  by_contra hne
  have hg_two : 2 ≤ g := by omega
  let k := R.q / g
  have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hqpos hgq) hgpos
  have hklt : k < R.q := Nat.div_lt_self hqpos (by omega)
  have hgvals (j : Fin n) : g ∣ (R.a j).val := by
    apply dvd_trans (Nat.gcd_dvd_right _ _)
    exact Finset.gcd_dvd (Finset.mem_univ j)
  have hqeq : g * k = R.q := Nat.mul_div_cancel' hgq
  have hka : k • R.a = 0 := by
    funext j
    change k • R.a j = 0
    rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val (R.a j)]
    obtain ⟨b, hb⟩ := hgvals j
    have hdiv : R.q ∣ k * (R.a j).val := by
      refine ⟨b, ?_⟩
      rw [hb, ← hqeq]
      ac_rfl
    have hz : ((k * (R.a j).val : ℕ) : ZMod R.q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdiv
    simpa only [Nat.cast_mul] using hz
  have hq_dvd_k : R.q ∣ k := by
    rw [← R.primitive, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hka
  exact (Nat.not_dvd_of_pos_of_lt hkpos hklt) hq_dvd_k

/-- The circle-valued phase vector represented by the residue vector. -/
def phase {n : ℕ} (R : ReducedDiagonalRepresentative n) : PhaseVector n :=
  phaseHom n R.q (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) R.a

/-- A reduced representative has the same exact additive order as its modulus. -/
theorem addOrderOf_phase {n : ℕ} (R : ReducedDiagonalRepresentative n) :
    addOrderOf R.phase = R.q := by
  rw [← R.primitive]
  exact addOrderOf_injective
    (phaseHom n R.q (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two))
    (phaseHom_injective n R.q (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two)) R.a

/-- The corresponding physical diagonal matrix has exact multiplicative order `q`. -/
theorem orderOf_diagonalGate {n : ℕ} (R : ReducedDiagonalRepresentative n) :
    orderOf (diagonalGate R.phase) = R.q := by
  rw [diagonalGate_order, R.addOrderOf_phase]

end ReducedDiagonalRepresentative

private theorem exists_zmod_preimage_of_nsmul_eq_zero {q : ℕ} [NeZero q] (hq : 0 < q)
    {u : UnitAddCircle} (hu : q • u = 0) :
    ∃ a : ZMod q, ZMod.toAddCircle a = u := by
  obtain ⟨m, hm, hu'⟩ := (AddCircle.nsmul_eq_zero_iff hq).mp hu
  refine ⟨(m : ZMod q), ?_⟩
  rw [ZMod.toAddCircle_natCast]
  simpa using hu'

/-- Every nonzero finite-order phase vector has a reduced residue representative. -/
theorem exists_reducedDiagonalRepresentative {n : ℕ} (theta : PhaseVector n)
    (hfinite : IsOfFinAddOrder theta) (hne : theta ≠ 0) :
    ∃ R : ReducedDiagonalRepresentative n, R.phase = theta := by
  let q := addOrderOf theta
  have hqpos : 0 < q := hfinite.addOrderOf_pos
  have hqne_one : q ≠ 1 := by
    intro hq
    apply hne
    exact AddMonoid.addOrderOf_eq_one_iff.mp hq
  have hq_two : 2 ≤ q := by omega
  have hqtheta : q • theta = 0 := addOrderOf_nsmul_eq_zero theta
  letI : NeZero q := ⟨hqpos.ne'⟩
  have hcoord (j : Fin n) : q • theta j = 0 := by
    exact congrFun hqtheta j
  choose a ha using fun j => exists_zmod_preimage_of_nsmul_eq_zero hqpos (hcoord j)
  have hphase : phaseHom n q hqpos a = theta := by
    funext j
    exact ha j
  have hprimitive : addOrderOf a = q := by
    have horder := addOrderOf_injective
      (phaseHom n q hqpos) (phaseHom_injective n q hqpos) a
    rw [hphase] at horder
    exact horder.symm
  let R : ReducedDiagonalRepresentative n :=
    { q := q
      q_ge_two := hq_two
      a := a
      primitive := hprimitive }
  exact ⟨R, hphase⟩

end

end QECC
