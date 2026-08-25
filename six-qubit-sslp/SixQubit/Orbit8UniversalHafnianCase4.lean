import SixQubit.Orbit8UniversalHafnianDecode
namespace SixQubit.Orbit8Universal
open scoped ComplexConjugate
open SixQubit
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000 in
theorem hafVia_eq_compHaf_four (d : SS.BitString 6 → ℂ)
    (j m : Fin 6) (hij : (4 : Fin 6) ≠ j) (him : (4 : Fin 6) ≠ m)
    (hjm : j ≠ m) : hafVia d 4 j m = compHaf d 4 m := by
  fin_cases j <;> fin_cases m <;>
    simp [compHaf, hafVia_decode, spare, awayPairs_four, touches, topRecip,
      edgeDecode, edgeState, pairMask, SS.stdBasis, SS.complement, SS.bxor] at * <;> ring
end
end SixQubit.Orbit8Universal
