import MainTheory.MatrixPositiveSupportVertices
import MainTheory.Orbit31SupportSemantics

/-! Integer reconstruction certificates prove uniqueness on a moment face,
and hence actual real-polytope extremality. -/
set_option autoImplicit false
namespace MainTheory.Orbit31VertexCertificateBase
noncomputable section
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.Generated.Orbit31SupportArithmetic
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.MatrixPositiveSupportVertices
open scoped BigOperators Matrix

def Valid (v : Fin 204) (C : Matrix (Fin 16) (Fin 7) ℤ) : Prop :=
  (∀ j k, (primalMasks v).testBit k.val = true →
    (∑ i, C j i*integerRows i k) = 8*(if j=k then 1 else 0)) ∧
  (∀ j, (∑ i, C j i*rhsTwice i) = 2*primalNumerators v j)

instance (v : Fin 204) (C : Matrix (Fin 16) (Fin 7) ℤ) : Decidable (Valid v C) := by
  unfold Valid
  infer_instance

def realCertificate (C : Matrix (Fin 16) (Fin 7) ℤ) : Matrix (Fin 16) (Fin 7) ℝ :=
  fun j i => (C j i : ℝ)/8

theorem unique_on_support {v : Fin 204} {C : Matrix (Fin 16) (Fin 7) ℤ}
    (hv : Valid v C) (q : Fin 16 → ℝ) (hq : Feasible M b q)
    (hoff : ∀ k, k ∉ maskSet (primalMasks v) → q k = 0) : q = primal v := by
  apply matrix_face_unique (maskSet (primalMasks v)) (realCertificate C) _ _ hq hoff
  · intro j k hk
    have he : (∑ i, (C j i : ℝ)*(integerRows i k : ℝ)) =
        8*(if j=k then 1 else 0) := by
      exact_mod_cast hv.1 j k ((mem_maskSet _ _).mp hk)
    change (∑ i, ((C j i : ℝ)/8)*(integerRows i k : ℝ)) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,he]
    split_ifs <;> norm_num
  · ext j
    have he : (∑ i, (C j i : ℝ)*(rhsTwice i : ℝ)) =
        2*(primalNumerators v j : ℝ) := by exact_mod_cast hv.2 j
    change (∑ i, ((C j i : ℝ)/8)*b i) = primal v j
    simp_rw [rhs_real]
    simp only [div_mul_div_comm,← Finset.sum_div]
    rw [he]
    unfold primal
    ring

theorem extreme {v : Fin 204} {C : Matrix (Fin 16) (Fin 7) ℤ}
    (hv : Valid v C) :
    primal v ∈ ({p | Feasible M b p} : Set (Fin 16 → ℝ)).extremePoints ℝ := by
  apply extreme_of_unique_face (primal_feasible v)
  intro q hq hz
  apply unique_on_support hv q hq
  intro k hk
  apply hz k
  exact zero_off_support (primal_feasible v).nonneg (primal_support v) hk

end
end MainTheory.Orbit31VertexCertificateBase
