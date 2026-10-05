import MainTheory.SevenQubitExampleStates
import MainTheory.SevenQubitPhaseArithmetic
import MainTheory.ProbabilityFrameEntries
import QECC.UniformRepresentative

/-! Physical phase preservation and the real kernel for the actual example. -/
namespace MainTheory.SevenQubitExampleProjector

open MainTheory.SevenQubitExampleData MainTheory.SevenQubitExampleStates
open MainTheory.SevenQubitPhaseArithmetic
noncomputable section
open scoped BigOperators
open Matrix

def projector : QECC.CodeProjector 7 2 := MainTheory.QECCFrameBridge.ofFrame frame

theorem edges (x y : SS.BitString 7) : projector.proj x y ≠ 0 ↔
    (probability 0 x ≠ 0 ∧ probability 0 y ≠ 0) ∨
      (probability 1 x ≠ 0 ∧ probability 1 y ≠ 0) := by
  simpa [projector, frame, probR] using
    MainTheory.ProbabilityFrameEntries.nonzero_iff probR probR_nonneg probR_sum probR_disjoint x y

def ExactEdges {A : Type*} [AddCommGroup A] (theta : Fin 7 → A) : Prop :=
  ∀ x y, projector.proj x y ≠ 0 → supportSum theta x = supportSum theta y

theorem exact_edges_iff {A : Type*} [AddCommGroup A] (theta : Fin 7 → A) :
    ExactEdges theta ↔ (∀ k, weights0 theta k = 0) ∧
      (∀ k, weights1 theta k = weights1 theta 0) := by
  have hp0 (k : Fin 4) : probability 0 (point0 k) ≠ 0 := (support0 _).mpr ⟨k, rfl⟩
  have hp1 (k : Fin 6) : probability 1 (point1 k) ≠ 0 := (support1 _).mpr ⟨k, rfl⟩
  constructor
  · intro h
    constructor
    · intro k
      have he := h (point0 k) (point0 0) ((edges _ _).mpr (Or.inl ⟨hp0 k, hp0 0⟩))
      simpa only [supportSum_point0, weights0, Matrix.cons_val_zero] using he
    · intro k
      have he := h (point1 k) (point1 0) ((edges _ _).mpr (Or.inr ⟨hp1 k, hp1 0⟩))
      simpa only [supportSum_point1] using he
  · rintro ⟨h0, h1⟩ x y hxy
    rcases (edges x y).mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · obtain ⟨k, rfl⟩ := (support0 x).mp hx
      obtain ⟨l, rfl⟩ := (support0 y).mp hy
      rw [supportSum_point0, supportSum_point0, h0 k, h0 l]
    · obtain ⟨k, rfl⟩ := (support1 x).mp hx
      obtain ⟨l, rfl⟩ := (support1 y).mp hy
      rw [supportSum_point1, supportSum_point1, h1 k, h1 l]

theorem preserving_phases (theta : QECC.PhaseVector 7) :
    projector.Preserves theta ↔ ∃ alpha beta u : QECC.LocalPhase,
      theta = pattern alpha beta u ∧ 4 • alpha = 0 ∧ 3 • beta = 0 :=
  (exact_edges_iff theta).trans (constant_supports_iff theta)

theorem detects_single_Z : projector.DetectsSingleZ :=
  projector.detectsSingleZ_of_hasDistanceAtLeast_two
    (MainTheory.QECCFrameBridge.hasDistanceAtLeast code)

theorem realSupportWeight_eq_supportSum (h : Fin 7 → ℝ) (x : SS.BitString 7) :
    QECC.realSupportWeight h x = supportSum h x := by
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp [QECC.bitReal]

noncomputable instance : Fintype projector.Edge := by
  unfold QECC.CodeProjector.Edge
  exact Fintype.ofFinite _

theorem matrix_kernel_iff_exact_edges (h : Fin 7 → ℝ) :
    (projector.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)) *ᵥ h = 0 ↔ ExactEdges h := by
  constructor
  · intro he x y hxy
    have hh := congrFun he (⟨(x, y), hxy⟩ : projector.Edge)
    rw [projector.edgeMatrix_mulVec, realSupportWeight_eq_supportSum,
      realSupportWeight_eq_supportSum] at hh
    exact sub_eq_zero.mp hh
  · intro he
    funext e
    rw [projector.edgeMatrix_mulVec, realSupportWeight_eq_supportSum,
      realSupportWeight_eq_supportSum, he e.val.1 e.val.2 e.property, sub_self]
    rfl

theorem real_kernel (h : Fin 7 → ℝ) :
    (projector.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)) *ᵥ h = 0 ↔
      ∃ u : ℝ, h = fun j => u * (direction j : ℝ) := by
  rw [matrix_kernel_iff_exact_edges, exact_edges_iff, constant_supports_iff]
  constructor
  · rintro ⟨alpha, beta, u, rfl, ha, hb⟩
    have ha0 : alpha = 0 := by norm_num [nsmul_eq_mul] at ha; linarith
    have hb0 : beta = 0 := by norm_num [nsmul_eq_mul] at hb; linarith
    subst alpha
    subst beta
    refine ⟨u, ?_⟩
    funext j
    fin_cases j <;> simp [pattern, direction]
  · rintro ⟨u, rfl⟩
    refine ⟨0, 0, u, ?_, by simp, by simp⟩
    funext j
    fin_cases j <;> simp [pattern, direction]

end
end MainTheory.SevenQubitExampleProjector
