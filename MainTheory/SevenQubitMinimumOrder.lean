import MainTheory.SevenQubitLogicalCharacter
import MainTheory.FiniteGateCanonicalNormalization
import QECC.PhysicalOrderMin

/-! The example has logical order six and minimum physical order twelve. -/
namespace MainTheory.SevenQubitMinimumOrder

open MainTheory.SevenQubitExampleProjector MainTheory.SevenQubitPhaseArithmetic
open MainTheory.SevenQubitCharacterArithmetic MainTheory.SevenQubitLogicalCharacter
noncomputable section

def angle12 : Fin 7 → ZMod 12 := ![3, 3, 3, 3, 4, 4, 4]

theorem angle12_primitive : MainTheory.Gate.Primitive 12 angle12 := by
  intro g _ hg
  have h3 : g ∣ 3 := by simpa only [show (angle12 0).val = 3 from rfl] using hg 0
  have h4 : g ∣ 4 := by simpa only [show (angle12 6).val = 4 from rfl] using hg 6
  have h := Nat.dvd_gcd h3 h4
  norm_num at h
  exact h

def representative : QECC.ReducedDiagonalRepresentative 7 where
  q := 12
  q_ge_two := by decide
  a := angle12
  primitive := MainTheory.FiniteGateCanonicalNormalization.primitive_addOrder
    angle12 angle12_primitive

theorem phase_pattern : representative.phase =
    pattern (ZMod.toAddCircle (1 : ZMod 4)) (ZMod.toAddCircle (1 : ZMod 3)) 0 := by
  have h3 : ZMod.toAddCircle (3 : ZMod 12) = ZMod.toAddCircle (1 : ZMod 4) := by
    rw [ZMod.toAddCircle_apply, ZMod.toAddCircle_apply]
    rw [show (3 : ZMod 12).val = 3 from by decide +kernel,
      show (1 : ZMod 4).val = 1 from by decide +kernel]
    congr 1
    norm_num
  have h4 : ZMod.toAddCircle (4 : ZMod 12) = ZMod.toAddCircle (1 : ZMod 3) := by
    rw [ZMod.toAddCircle_apply, ZMod.toAddCircle_apply]
    rw [show (4 : ZMod 12).val = 4 from by decide +kernel,
      show (1 : ZMod 3).val = 1 from by decide +kernel]
    congr 1
    norm_num
  funext j
  fin_cases j <;>
    simp only [representative, QECC.ReducedDiagonalRepresentative.phase, QECC.phaseHom,
      angle12, pattern, add_zero, sub_zero]
  all_goals first | exact h3 | exact h4

theorem preserves : projector.Preserves representative.phase := by
  rw [phase_pattern]
  apply (preserving_phases _).mpr
  refine ⟨_, _, 0, rfl, ?_, ?_⟩
  · rw [← map_nsmul]
    rw [show 4 • (1 : ZMod 4) = 0 from by decide +kernel, map_zero]
  · rw [← map_nsmul]
    rw [show 3 • (1 : ZMod 3) = 0 from by decide +kernel, map_zero]

def targetClass : projector.ProjectiveDiagonalGroup :=
  projector.projectiveClassMap ⟨representative.phase, preserves⟩

theorem target_character : logicalCharacter targetClass = ZMod.toAddCircle (1 : ZMod 6) := by
  change supportSum representative.phase (point1 0) = _
  rw [phase_pattern, supportSum_point1, pattern_weights1, circle_character]
  exact congrArg ZMod.toAddCircle (by decide +kernel : chiFn (1, 1) = 1)

theorem target_nonzero : targetClass ≠ 0 := by
  intro h
  have hc := target_character
  rw [h, map_zero] at hc
  rw [← (ZMod.toAddCircle : ZMod 6 →+ QECC.LocalPhase).map_zero] at hc
  have he := ZMod.toAddCircle_injective 6 hc.symm
  exact (by decide : (1 : ZMod 6) ≠ 0) he

theorem logical_order : addOrderOf targetClass = 6 := by
  rw [← addOrderOf_injective logicalCharacter logicalCharacter_injective targetClass,
    target_character, addOrderOf_injective (ZMod.toAddCircle : ZMod 6 →+ QECC.LocalPhase)
      (ZMod.toAddCircle_injective 6)]
  exact ZMod.addOrderOf_coe 1 (by decide : 6 ≠ 0)

theorem twelve_dvd_representative (R : QECC.ReducedDiagonalRepresentative 7)
    (hp : projector.Preserves R.phase)
    (hc : projector.projectiveClassMap ⟨R.phase, hp⟩ = targetClass) : 12 ∣ R.q := by
  obtain ⟨alpha, beta, u, he, ha, hb⟩ := (preserving_phases R.phase).mp hp
  have ht : 2 • alpha + 2 • beta = ZMod.toAddCircle (1 : ZMod 6) := by
    have hh := congrArg logicalCharacter hc
    rw [logicalCharacter_class, he, supportSum_point1, pattern_weights1,
      target_character] at hh
    exact hh
  obtain ⟨hao, hbo⟩ := circle_target_orders alpha beta ha hb ht
  have hkill : R.q • R.phase = 0 := by
    rw [← R.addOrderOf_phase]
    exact addOrderOf_nsmul_eq_zero R.phase
  have hak : R.q • alpha = 0 := by
    have hh := congrFun hkill 2
    simpa [he, pattern] using hh
  have hbk : R.q • beta = 0 := by
    have hh := congrFun hkill 6
    simpa [he, pattern] using hh
  have hd4 : 4 ∣ R.q := by
    rw [← hao, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hak
  have hd3 : 3 ∣ R.q := by
    rw [← hbo, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hbk
  have h := Nat.lcm_dvd hd4 hd3
  norm_num at h
  exact h

theorem minimum_physical_order : projector.minimalPhysicalOrder targetClass = 12 := by
  apply Nat.le_antisymm
  · exact projector.minimalPhysicalOrder_le targetClass representative preserves rfl
  · obtain ⟨R, hp, hc, hq⟩ := projector.minimalPhysicalOrder_mem
      (projector.detectsNumberOps_of_detectsSingleZ detects_single_Z) targetClass target_nonzero
    have hd := twelve_dvd_representative R hp hc
    rw [← hq]
    exact Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) hd

theorem physical_order : orderOf (QECC.diagonalGate representative.phase) = 12 :=
  representative.orderOf_diagonalGate

end
end MainTheory.SevenQubitMinimumOrder
