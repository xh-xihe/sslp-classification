import QECC.RankTwoCanonical
import MainTheory.Gate

/-! Canonical two-fiber coordinates for the supplied finite physical gate. -/
namespace MainTheory.FiniteGateCanonicalNormalization

noncomputable section
variable {n : ℕ}

theorem primitive_addOrder {q : ℕ} [NeZero q] (a : Fin n → ZMod q)
    (hprim : MainTheory.Gate.Primitive q a) : addOrderOf a = q := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    funext j
    change q • a j = 0
    simp [nsmul_eq_mul]
  · apply MainTheory.Gate.dvd_of_forall_mul_eq_zero a hprim
    intro j
    have h := congrFun (addOrderOf_nsmul_eq_zero a) j
    simpa [nsmul_eq_mul] using h

theorem common_divisor_phase_zero {q : ℕ} [NeZero q]
    (a : Fin n → ZMod q) (g : ℕ) (hgq : g ∣ q)
    (hga : ∀ j, g ∣ (a j).val) :
    (q / g) • QECC.phaseHom n q (Nat.pos_of_ne_zero (NeZero.ne q)) a = 0 := by
  have hkill : (q / g) • a = 0 := by
    funext j
    change (q / g) • a j = 0
    rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val (a j)]
    have hdvd : q ∣ (q / g) * (a j).val := by
      obtain ⟨b, hb⟩ := hga j
      refine ⟨b, ?_⟩
      calc
        (q / g) * (a j).val = (q / g) * (g * b) := by rw [hb]
        _ = (g * (q / g)) * b := by ring
        _ = q * b := by rw [Nat.mul_div_cancel' hgq]
    have hz := (ZMod.natCast_eq_zero_iff ((q / g) * (a j).val) q).mpr hdvd
    simpa only [Nat.cast_mul] using hz
  rw [← map_nsmul, hkill, map_zero]

theorem supplied_representative (C : QECC.CodeProjector n 2)
    (R : QECC.ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (hne : C.projectiveClassMap ⟨R.phase, hpres⟩ ≠ 0) :
    let m := addOrderOf (C.projectiveClassMap ⟨R.phase, hpres⟩)
    2 ≤ m ∧ m ∣ R.q ∧
      C.HasRankTwoCanonicalNormalization
        (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) m R.a := by
  let hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  let rep : C.preservingPhases := ⟨R.phase, hpres⟩
  let U := C.projectiveClassMap rep
  have hrep : addOrderOf rep = R.q := by
    have hi := addOrderOf_injective C.preservingPhases.subtype
      (AddSubgroup.subtype_injective C.preservingPhases) rep
    change addOrderOf R.phase = addOrderOf rep at hi
    rw [R.addOrderOf_phase] at hi
    exact hi.symm
  have hdvd : addOrderOf U ∣ R.q := by
    have h := addOrderOf_map_dvd C.projectiveClassMap rep
    rwa [hrep] at h
  have hpos : 0 < addOrderOf U := Nat.pos_of_dvd_of_pos hdvd hq
  have hne1 : addOrderOf U ≠ 1 := by
    intro h
    exact hne (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hm : 2 ≤ addOrderOf U := by omega
  refine ⟨hm, hdvd, ?_⟩
  exact C.exists_rankTwoCanonicalNormalization hq (addOrderOf U) R.a
    R.primitive hpres hne hm hdvd rfl

theorem supplied_primitive_gate {q : ℕ} [NeZero q]
    (C : QECC.CodeProjector n 2) (hq : 2 ≤ q) (a : Fin n → ZMod q)
    (hprim : MainTheory.Gate.Primitive q a)
    (hpres : C.Preserves
      (QECC.phaseHom n q (lt_of_lt_of_le Nat.zero_lt_two hq) a))
    (hne : C.projectiveClassMap ⟨_, hpres⟩ ≠ 0) :
    let m := addOrderOf (C.projectiveClassMap ⟨_, hpres⟩)
    2 ≤ m ∧ m ∣ q ∧
      C.HasRankTwoCanonicalNormalization
        (lt_of_lt_of_le Nat.zero_lt_two hq) m a := by
  let R : QECC.ReducedDiagonalRepresentative n :=
    ⟨q, hq, a, primitive_addOrder a hprim⟩
  exact supplied_representative C R hpres hne

end
end MainTheory.FiniteGateCanonicalNormalization
