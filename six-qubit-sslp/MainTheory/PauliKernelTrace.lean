import MainTheory.ClassificationLevels
import SixQubit.MacWilliams

/-!
# `eq:A-enumerator` as an actual operator trace

`eq:A-enumerator` reads `A_w(P) = K^{-2} sum_{wt(E)=w} |tr(E Pi)|^2`, and
`SS.MacWilliams.Aco` is that sum, built on
`trProj psi P = sum_a innerC (psi a) (pauliAct P (psi a))`.  The normalisation
matches the paper, but `trProj`'s identification with `Tr (E Pi)` lived only in
the module docstring and a comment: no Pauli was ever written as a matrix, so
no trace was ever formed, and `Aco` was a sum of frame inner products that the
prose *called* a trace.

This file forms it.  `pauliKernel` is the Pauli word as an `OperatorKernel`,
checked against `SS.pauliAct` by `kernelAction_pauliKernel`, and

  `Tr (E * Pi) = trProj psi E`

is `trace_pauliKernel_mul_projector`, for the projector kernel of any
orthonormal frame.  So `Aco` really is the enumerator of `eq:A-enumerator`, and
that is now a theorem rather than a naming convention.

The proof is the one-line-per-row observation that a Pauli has exactly one
nonzero entry in each row -- at column `t xor P.x` -- so the trace's inner sum
collapses, and what is left is the definition of `trProj` with the two sums
exchanged.
-/

namespace MainTheory.PauliKernelTrace

open MainTheory.ClassificationLevels
open MainTheory.CodeSpec

variable {n K : ℕ}

/-- A Pauli word as a matrix on the computational basis.  Its only nonzero
entry in row `t` is at column `t xor P.x`. -/
def pauliKernel (P : SS.PauliString n) : OperatorKernel n :=
  fun t y =>
    if y = SS.bxor t P.x then
      (Complex.I ^ P.numY) * SS.signC (SS.bdot P.z (SS.bxor t P.x)) 1
    else 0

/-- The matrix acts the way `SS.pauliAct` does, so it is the right matrix. -/
theorem kernelAction_pauliKernel (P : SS.PauliString n) (phi : SS.State n ℂ) :
    kernelAction (pauliKernel P) phi = SS.pauliAct P phi := by
  classical
  funext t
  rw [kernelAction, SS.pauliAct, Finset.sum_eq_single (SS.bxor t P.x)]
  · by_cases hb : SS.bdot P.z (SS.bxor t P.x) <;>
      simp [pauliKernel, hb, SS.signC]
  · intro y _ hy
    simp [pauliKernel, hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- One diagonal entry of `E * Pi`, with the row's single nonzero entry used. -/
private theorem diag_entry (F : OrthonormalFrame n K) (P : SS.PauliString n)
    (t : SS.BitString n) :
    (pauliKernel P * (CodeProjector.ofFrame F).kernel) t t
      = ∑ a, star (F.vec a t) * SS.pauliAct P (F.vec a) t := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (SS.bxor t P.x)]
  · show pauliKernel P t (SS.bxor t P.x) * projectorKernel F (SS.bxor t P.x) t = _
    rw [projectorKernel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hb : SS.bdot P.z (SS.bxor t P.x) <;>
      simp [pauliKernel, SS.pauliAct, hb, SS.signC] <;> ring
  · intro y _ hy
    simp [pauliKernel, hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`Tr (E * Pi) = trProj psi E`.** -/
theorem trace_pauliKernel_mul_projector (F : OrthonormalFrame n K)
    (P : SS.PauliString n) :
    Matrix.trace (pauliKernel P * (CodeProjector.ofFrame F).kernel)
      = SS.MacWilliams.trProj F.vec P := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => diag_entry F P t),
    Finset.sum_comm, SS.MacWilliams.trProj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [SS.innerC]

/-- **`Aco` is the unnormalised `eq:A-enumerator`**, with the trace formed. -/
theorem Aco_eq_sum_normSq_trace (F : OrthonormalFrame n K) (j : ℕ) :
    SS.MacWilliams.Aco F.vec j
      = ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
          Complex.normSq (Matrix.trace (pauliKernel P * (CodeProjector.ofFrame F).kernel)) := by
  rw [SS.MacWilliams.Aco]
  exact Finset.sum_congr rfl fun P _ => by
    rw [trace_pauliKernel_mul_projector]

end MainTheory.PauliKernelTrace
