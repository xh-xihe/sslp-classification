import SixQubit.Realize

/-! Literal relation between the mathematical binary-coordinate convention
and the integer encoding used by the finite six-qubit certificates.
-/

namespace MainTheory.BinaryMaskConvention
open scoped BigOperators

theorem num_as_sum (x : SS.BitString 6) :
    SixQubit.Realize.num x = ∑ i : Fin 6, (if x i then 1 else 0)*2^i.val := by
  simp [SixQubit.Realize.num,Fin.sum_univ_succ,Fin.succ,add_assoc]

end MainTheory.BinaryMaskConvention
