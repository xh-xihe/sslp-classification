import QECC.FiniteDiagonal
import QECC.RationalSection

namespace QECC

open scoped BigOperators

noncomputable section

/-- A phase vector whose coordinates are integer multiples of `1 / Q`. -/
def rationalPhase {n : ℕ} (Q : ℕ) (a : Fin n → ℤ) : PhaseVector n :=
  fun j ↦ (((a j : ℝ) / (Q : ℝ) : ℝ) : LocalPhase)

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- Ordered computational-basis pairs joined by a nonzero projector entry. -/
def Edge := {e : BitString n × BitString n // C.proj e.1 e.2 ≠ 0}

/-- The integer incidence matrix recording support differences along projector edges. -/
def edgeMatrix : Matrix C.Edge (Fin n) ℤ :=
  fun e j ↦ bitInt (e.1.1 j) - bitInt (e.1.2 j)

/-- The real edge matrix computes differences of computational-basis subset sums. -/
theorem edgeMatrix_mulVec (h : Fin n → ℝ) (e : C.Edge) :
    (C.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)).mulVec h e =
      realSupportWeight h e.1.1 - realSupportWeight h e.1.2 := by
  simp only [edgeMatrix, Matrix.mulVec, dotProduct, Matrix.map_apply, realSupportWeight]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases e.1.1 j <;> cases e.1.2 j <;> simp [bitInt, bitReal]

private theorem exists_int_sub_of_addCircle_eq {u v : ℝ}
    (h : ((u : ℝ) : LocalPhase) = ((v : ℝ) : LocalPhase)) :
    ∃ z : ℤ, u - v = (z : ℝ) := by
  have hc : (((u - v : ℝ) : LocalPhase)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hc
  exact ⟨z, by simpa using hz.symm⟩

/-- Preservation makes every lifted real edge value an integer. -/
theorem preserves_integral_edge_values (theta : PhaseVector n)
    (htheta : C.Preserves theta) :
    ∃ b : C.Edge → ℤ,
      (C.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)).mulVec (phaseLift theta) =
        fun e ↦ (b e : ℝ) := by
  classical
  have hint : ∀ e : C.Edge, ∃ z : ℤ,
      realSupportWeight (phaseLift theta) e.1.1 -
        realSupportWeight (phaseLift theta) e.1.2 = (z : ℝ) := by
    intro e
    apply exists_int_sub_of_addCircle_eq
    rw [supportPhase_lift, supportPhase_lift]
    exact htheta e.1.1 e.1.2 e.2
  choose b hb using hint
  refine ⟨b, funext fun e ↦ ?_⟩
  rw [C.edgeMatrix_mulVec]
  exact hb e

/-- A real vector in the edge-matrix kernel induces a scalar phase on a detecting code. -/
theorem actsAsScalar_of_edgeMatrix_mulVec_eq_zero (h : Fin n → ℝ)
    (hdetect : C.DetectsNumberOps)
    (hzero : (C.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)).mulVec h = 0) :
    C.ActsAsScalar (fun j ↦ ((h j : ℝ) : LocalPhase)) := by
  apply C.actsAsScalar_of_exact_edges h hdetect
  intro x y hxy
  let e : C.Edge := ⟨(x, y), hxy⟩
  have he := congrFun hzero e
  rw [C.edgeMatrix_mulVec] at he
  exact sub_eq_zero.mp he

private theorem sub_rationalPhase_eq_lift_difference
    (theta : PhaseVector n) (Q : ℕ) (a : Fin n → ℤ) :
    theta - rationalPhase Q a =
      (fun j ↦ ((phaseLift theta j - (a j : ℝ) / (Q : ℝ) : ℝ) : LocalPhase)) := by
  funext j
  change theta j - (((a j : ℝ) / (Q : ℝ) : ℝ) : LocalPhase) = _
  rw [← coe_phaseLift theta j]
  rfl

/-- One denominator, depending only on the code, supplies rational representatives
for all code-preserving phase vectors modulo scalar actions. -/
theorem exists_uniform_rationalPhase_representative
    (hdetect : C.DetectsNumberOps) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ theta : PhaseVector n, C.Preserves theta →
        ∃ a : Fin n → ℤ,
          C.Preserves (rationalPhase Q a) ∧
            C.ActsAsScalar (theta - rationalPhase Q a) := by
  classical
  letI : Finite C.Edge := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype C.Edge := Fintype.ofFinite C.Edge
  obtain ⟨Q, hQ, hsection⟩ := integerMatrix_uniform_rational_lift C.edgeMatrix
  refine ⟨Q, hQ, ?_⟩
  intro theta htheta
  obtain ⟨b, hb⟩ := C.preserves_integral_edge_values theta htheta
  obtain ⟨a, ha⟩ := hsection (phaseLift theta) b hb
  let h : Fin n → ℝ :=
    fun j ↦ phaseLift theta j - (a j : ℝ) / (Q : ℝ)
  have hzero :
      (C.edgeMatrix.map ((Int.castRingHom ℝ) : ℤ → ℝ)).mulVec h = 0 := by
    simpa [h, Pi.sub_apply] using ha
  have hscalarReal :=
    C.actsAsScalar_of_edgeMatrix_mulVec_eq_zero h hdetect hzero
  have hscalar : C.ActsAsScalar (theta - rationalPhase Q a) := by
    rw [sub_rationalPhase_eq_lift_difference]
    simpa [h] using hscalarReal
  have hscalarPreserves : C.Preserves (theta - rationalPhase Q a) :=
    C.preserves_of_actsAsScalar hscalar
  have hrat' : C.Preserves (theta + -(theta - rationalPhase Q a)) :=
    C.preserves_add htheta (C.preserves_neg hscalarPreserves)
  have hphase : theta + -(theta - rationalPhase Q a) = rationalPhase Q a := by
    abel
  refine ⟨a, ?_, hscalar⟩
  rw [← hphase]
  exact hrat'

end CodeProjector

end

end QECC
