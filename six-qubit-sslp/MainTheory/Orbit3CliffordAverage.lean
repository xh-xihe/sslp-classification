import MainTheory.Orbit3SpectatorUnitary
import MainTheory.CodePreservingUnitary
import SixQubit.Generated.SpectatorClifford

/-! # Finite spectator averages and actual Hadamard Ward identities

The 24 complex unitary representatives close under H and S up to a verified
unit scalar. Global-phase invariant functions therefore have exact finite
average identities. Actual cubic entries and Pauli products satisfy that
invariance; no invariant-moment hypothesis is supplied by the caller.
-/

namespace MainTheory.Orbit3CliffordAverage

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel MainTheory.PauliTransferTwo
open SixQubit.Generated.SpectatorClifford SixQubit.CodeEquiv
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000

def act (U : Mat2) (w : SS.State 6 ℂ) : SS.State 6 ℂ := kernelAction (oneQubitKernel 0 U) w

theorem one_site_mul (U V : Mat2) :
    oneQubitKernel (n := 6) 0 U * oneQubitKernel 0 V = oneQubitKernel 0 (U * V) := by
  rw [← tensorKernel_single 0 U, ← tensorKernel_single 0 V,
    ← tensorKernel_single 0 (U * V), ← tensorKernel_mul]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst j
    rfl
  · simp only [Function.update_of_ne hj, mul_one]

theorem act_mul (U V : Mat2) (w : SS.State 6 ℂ) : act U (act V w) = act (U * V) w := by
  unfold act
  rw [← MainTheory.CodePreservingUnitary.kernelAction_mul, one_site_mul]

theorem act_smul (z : ℂ) (U : Mat2) (w : SS.State 6 ℂ) : act (z • U) w = scal z (act U w) := by
  have hk : oneQubitKernel (n := 6) 0 (z • U) = z • oneQubitKernel 0 U := by
    ext s t
    simp only [oneQubitKernel, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  unfold act scal
  rw [hk]
  funext s
  simp only [kernelAction, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem leftH_act (g : Fin 24) (w : SS.State 6 ℂ) :
    act hadamard (act (clifford g) w) = scal (phase (phaseH g)) (act (clifford (nextH g)) w) := by
  rw [act_mul, closureH, act_smul]

theorem leftS_act (g : Fin 24) (w : SS.State 6 ℂ) :
    act phaseGate (act (clifford g) w) = scal (phase (phaseS g)) (act (clifford (nextS g)) w) := by
  rw [act_mul, closureS, act_smul]

def PhaseStable (F : SS.State 6 ℂ → ℝ) : Prop :=
  ∀ z w, star z * z = 1 → F (scal z w) = F w

theorem average_H (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, F (act hadamard (act (clifford g) w))) =
      ∑ g : Fin 24, F (act (clifford g) w) := by
  simp_rw [leftH_act]
  have hs (g : Fin 24) := hF (phase (phaseH g)) (act (clifford (nextH g)) w) (phase_unit _)
  simp_rw [hs]
  exact (Equiv.ofBijective nextH nextH_bijective).sum_comp (fun g => F (act (clifford g) w))

theorem average_S (F : SS.State 6 ℂ → ℝ) (hF : PhaseStable F) (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, F (act phaseGate (act (clifford g) w))) =
      ∑ g : Fin 24, F (act (clifford g) w) := by
  simp_rw [leftS_act]
  have hs (g : Fin 24) := hF (phase (phaseS g)) (act (clifford (nextS g)) w) (phase_unit _)
  simp_rw [hs]
  exact (Equiv.ofBijective nextS nextS_bijective).sum_comp (fun g => F (act (clifford g) w))

theorem pauli_scalar_unit (z : ℂ) (w : SS.State 6 ℂ) (P : SS.PauliString 6)
    (hz : star z * z = 1) :
    SS.innerC (scal z w) (SS.pauliAct P (scal z w)) = SS.innerC w (SS.pauliAct P w) := by
  have ha : SS.pauliAct P (scal z w) = scal z (SS.pauliAct P w) := by
    funext s
    unfold SS.pauliAct scal
    cases hb : SS.bdot P.z (SS.bxor s P.x) <;>
      simp [SS.signC, hb, mul_left_comm]
  rw [ha]
  unfold SS.innerC scal
  apply Finset.sum_congr rfl
  intro s _
  rw [star_mul]
  calc
    _ = (star z * z) * (star (w s) * SS.pauliAct P w s) := by ring
    _ = _ := by rw [hz, one_mul]

def product (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ) : ℝ :=
  (∏ k : Fin 3, SS.innerC w (SS.pauliAct (P k) w)).re

theorem product_phase_stable (P : Fin 3 → SS.PauliString 6) : PhaseStable (product P) := by
  intro z w hz
  unfold product
  simp_rw [pauli_scalar_unit z w _ hz]

theorem actual_H_product_identity (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, product P (act hadamard (act (clifford g) w))) =
      ∑ g : Fin 24, product P (act (clifford g) w) :=
  average_H _ (product_phase_stable P) w

end
end MainTheory.Orbit3CliffordAverage
