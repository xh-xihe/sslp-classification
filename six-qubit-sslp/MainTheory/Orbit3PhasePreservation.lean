import MainTheory.Orbit3PhaseBlocks
import MainTheory.Orbit3PauliZeros

/-! # The finite cubic phase projection preserves actual encoders

Physical local fourth-root phases and the logical parity fourth-root phase
map an arbitrary normalized orbit-3 completion to the same completion type.
Thus its universal quadratic zeros hold at every point of this phase average.
-/

namespace MainTheory.Orbit3PhasePreservation

open MainTheory.Orbit3PhaseBlocks MainTheory.CubicPhaseProjection
open MainTheory.FinitePhaseAverage MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.OrderTwoScalarBridge SixQubit.ParityPauliScalars
open SixQubit.ParityLogicalState SixQubit.CodeEquiv
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem I_power_unit (n : ℕ) : star (Complex.I ^ n) * Complex.I ^ n = 1 :=
  unit_of_normSq (by simp)

theorem character_unit (p a : PhaseSite → Fin 4) :
    star (character p a) * character p a = 1 := by
  unfold character
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  exact I_power_unit _

def physicalPhase (p : PhaseSite → Fin 4) (j : Fin 6) : ℂ := Complex.I ^ (p (.inl j)).val

def logicalPhase (p : PhaseSite → Fin 4) (k : Fin 2) : ℂ :=
  Complex.I ^ ((p (.inr ())).val * (if k = 0 then 0 else 1))

theorem factor (p : PhaseSite → Fin 4) (s : SS.BitString 6) :
    character p (binaryProfile bits s) =
      (∏ j : Fin 6, if s j then physicalPhase p j else 1) *
        (if SS.bdot orbit3Mask s then Complex.I ^ (p (.inr ())).val else 1) := by
  unfold character
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, binaryProfile, bits]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    by_cases hs : s j = true <;> simp [hs, physicalPhase]
  · by_cases hs : SS.bdot orbit3Mask s = true <;> simp [hs]

theorem column_parity (W : Encoder) (k : Fin 2) (s : SS.BitString 6)
    (hs : W.states k s ≠ 0) : SS.bdot orbit3Mask s = (k == 1) := by
  by_contra hp
  apply hs
  apply (orbit3_parity W k) s
  rw [chi_bdot]
  fin_cases k <;> cases hb : SS.bdot orbit3Mask s <;>
    first | contradiction | norm_num [logicalSign, hb]

theorem modulated_column (W : Encoder) (p : PhaseSite → Fin 4) (k : Fin 2) :
    modulated bits (W.states k) p =
      scal (logicalPhase p k) (diagOn Finset.univ (physicalPhase p) (W.states k)) := by
  funext s
  by_cases hs : W.states k s = 0
  · simp [modulated, scal, diagOn, hs]
  · unfold modulated scal diagOn
    rw [factor, column_parity W k s hs]
    fin_cases k <;> simp [logicalPhase, mul_left_comm, mul_assoc]

def transform (W : Encoder) (p : PhaseSite → Fin 4) : Encoder where
  states k := modulated bits (W.states k) p
  supported := by
    intro k s hs
    simp only [modulated, W.supported k s hs, mul_zero]
  normalized := by
    intro k
    calc
      _ = SS.innerC (W.states k) (W.states k) := by
        unfold SS.innerC modulated
        apply Finset.sum_congr rfl
        intro s _
        rw [star_mul]
        calc
          _ = (star (character p (binaryProfile bits s)) * character p (binaryProfile bits s)) *
              (star (W.states k s) * W.states k s) := by ring
          _ = _ := by rw [character_unit, one_mul]
      _ = 1 := W.normalized k
  hasDistance := by
    have hdiag := detectsRaw_diagOn Finset.univ (physicalPhase p)
      (fun j => I_power_unit (p (.inl j)).val) ((hasDistance_iff W.states).mp W.hasDistance)
    have hscale := detectsRaw_scalPair (logicalPhase p) (fun k => I_power_unit _ ) hdiag
    apply (hasDistance_iff _).mpr
    have he : (fun k => modulated bits (W.states k) p) =
        fun k => scal (logicalPhase p k) (diagOn Finset.univ (physicalPhase p) (W.states k)) := by
      funext k
      exact modulated_column W p k
    rw [he]
    exact hscale

theorem transformed_superposition (W : Encoder) (p : PhaseSite → Fin 4) :
    superposition (transform W p).states = modulated bits (superposition W.states) p := by
  funext s
  change character p (binaryProfile bits s) * W.states 0 s +
    character p (binaryProfile bits s) * W.states 1 s =
      character p (binaryProfile bits s) * (W.states 0 s + W.states 1 s)
  ring

theorem constrained_expectation_zero (W : Encoder) (p : PhaseSite → Fin 4)
    (P : SS.PauliString 6) (hP : MainTheory.Orbit3PauliZeros.Constrained P) :
    SS.innerC (modulated bits (superposition W.states) p)
      (SS.pauliAct P (modulated bits (superposition W.states) p)) = 0 := by
  rw [← transformed_superposition]
  exact MainTheory.Orbit3PauliZeros.constrained_expectation_zero (transform W p) P hP

end
end MainTheory.Orbit3PhasePreservation
