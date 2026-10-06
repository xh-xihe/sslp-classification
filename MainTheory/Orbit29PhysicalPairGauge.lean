import MainTheory.Orbit29PhysicalRatios
import MainTheory.Orbit9DiagonalGauge

/-! The common ratio phase is removed by one actual local diagonal unitary
on qubit five, preserving normalization and complete physical KL. -/
set_option autoImplicit false
namespace MainTheory.Orbit29PhysicalPairGauge
open Orbit29PhysicalRatios Orbit29PrintedFaceAudit SignedPhaseSupport
open ClassificationLevels SixQubit.Orbit29
noncomputable section

def frame (c d : SS.State 6 ℂ) (H : FullKL c d) : CodeSpec.OrthonormalFrame 6 2 where
  vec := ![c,d]
  orthonormal := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using H.norm0
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d H.support0 H.support1 (by decide +kernel)
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S1 S0 d c H.support1 H.support0 (by decide +kernel)
    · simpa using H.norm1

def code (c d : SS.State 6 ℂ) (H : FullKL c d) : CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := frame c d H
  hasDistance := H.distance

theorem diagonal_fullKL (c d : SS.State 6 ℂ) (H : FullKL c d) (u : LocalPhase 6) :
    FullKL (diagonalAction u c) (diagonalAction u d) where
  support0 := by intro x hx; simp [diagonalAction,H.support0 x hx]
  support1 := by intro x hx; simp [diagonalAction,H.support1 x hx]
  norm0 := by rw [Orbit9DiagonalGauge.inner_diagonal,H.norm0]
  norm1 := by rw [Orbit9DiagonalGauge.inner_diagonal,H.norm1]
  distance := by
    have h := DiagonalLocalKernel.hasDistance (code c d H) u
    have he : (fun i => diagonalAction u ((code c d H).frame.vec i))=
        ![diagonalAction u c,diagonalAction u d] := by
      funext i
      fin_cases i <;> rfl
    rwa [he] at h

def singlePhase (u : unitary ℂ) : LocalPhase 6 :=
  fun i => if i=⟨4,by decide⟩ then u else 1

theorem single_value (u : unitary ℂ) (x : SS.BitString 6) :
    diagonalValue (singlePhase u) x=if x ⟨4,by decide⟩ then (u : ℂ) else 1 := by
  norm_num [diagonalValue,singlePhase,Fin.prod_univ_succ,Fin.succ]

def vertexWords : Fin 10 → Fin 2 → SS.BitString 6 :=
  ![![y13,y12],![y11,y10],![y7,y6],![y9,y8],![y5,y4],![y3,y2],
    ![z15,z14],![z13,z12],![z11,z10],![z7,z6]]

theorem vertex_fifth_bits : ∀ v j, vertexWords v j ⟨4,by decide⟩=decide (j=0) := by decide +kernel

theorem amplitudes_at_vertex (c d : SS.State 6 ℂ) : ∀ v j,
    amplitudes c d v j=if colors v then d (vertexWords v j) else c (vertexWords v j) := by
  intro v j
  fin_cases v <;> fin_cases j <;> rfl

theorem gauge_amplitudes (u : unitary ℂ) (c d : SS.State 6 ℂ) : ∀ v j,
    amplitudes (diagonalAction (singlePhase u) c) (diagonalAction (singlePhase u) d) v j=
      (if j=0 then (u : ℂ) else 1)*amplitudes c d v j := by
  intro v j
  rw [amplitudes_at_vertex,amplitudes_at_vertex]
  have hb := vertex_fifth_bits v j
  change vertexWords v j (4 : Fin 6)=decide (j=0) at hb
  cases colors v <;> simp [diagonalAction,single_value,hb]

theorem diagonal_normSq (u : LocalPhase 6) (c : SS.State 6 ℂ) (x : SS.BitString 6) :
    Complex.normSq (diagonalAction u c x)=Complex.normSq (c x) := by
  rw [diagonalAction,Complex.normSq_mul,Orbit9DiagonalGauge.diagonal_normSq,one_mul]

theorem physical_pair_gauge (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∃ u : unitary ℂ,
      FullKL (diagonalAction (singlePhase u) c) (diagonalAction (singlePhase u) d) ∧
      (∀ x, Complex.normSq (diagonalAction (singlePhase u) c x)=Complex.normSq (c x)) ∧
      (∀ x, Complex.normSq (diagonalAction (singlePhase u) d x)=Complex.normSq (d x)) ∧
      ∀ v, amplitudes (diagonalAction (singlePhase u) c) (diagonalAction (singlePhase u) d) v 1=
        sign (colors v) (amplitudes (diagonalAction (singlePhase u) c) (diagonalAction (singlePhase u) d) v 0) := by
  obtain ⟨m,u,hf,hu,hr⟩ := common_unit_phase c d H
  let U : unitary ℂ := ⟨u,Unitary.mem_iff_star_mul_self.mpr (by
    rw [SixQubit.star_mul_self,hu]
    norm_num)⟩
  refine ⟨U,diagonal_fullKL c d H _,diagonal_normSq _ c,diagonal_normSq _ d,?_⟩
  intro v
  rw [gauge_amplitudes,gauge_amplitudes]
  norm_num
  by_cases hv : v ∈ active m
  · have hphase := hr v hv
    have ha := active_amplitude_nonzero c d H m hf v hv 0
    have he : amplitudes c d v 1=sign (colors v) u*amplitudes c d v 0 :=
      (div_eq_iff ha).mp hphase
    change amplitudes c d v 1=sign (colors v) (u*amplitudes c d v 0)
    cases hc : colors v <;> rw [hc] at he <;> dsimp [sign] at he ⊢
    · exact he
    · linear_combination he
  · have hn : 0 ≤ vertexProbability (coordinates d) v := by
      rw [← amplitude_probabilities c d H v 0]
      exact Complex.normSq_nonneg _
    have hp : ¬ 0 < vertexProbability (coordinates d) v := fun h =>
      hv ((vertex_positive_iff m (coordinates d) (coordinate_nonneg c d H) hf v).mp h)
    have hz : vertexProbability (coordinates d) v=0 := le_antisymm (le_of_not_gt hp) hn
    have z0 := Complex.normSq_eq_zero.mp ((amplitude_probabilities c d H v 0).trans hz)
    have z1 := Complex.normSq_eq_zero.mp ((amplitude_probabilities c d H v 1).trans hz)
    rw [z0,z1,mul_zero]
    cases colors v <;> simp [sign]

end
end MainTheory.Orbit29PhysicalPairGauge
