import SixQubit.Orbit8UniversalHafnianIsolate

/-! Kernel-checked transpose symmetry of the complementary hafnian. -/

namespace SixQubit.Orbit8Universal

open scoped ComplexConjugate
open SixQubit
noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000 in
theorem compHaf_swap (d : SS.BitString 6 → ℂ) (i m : Fin 6) :
    compHaf d i m = compHaf d m i := by
  fin_cases i <;> fin_cases m <;>
    simp [compHaf, hafVia_decode, spare, awayPairs_zero, awayPairs_one,
      awayPairs_two, awayPairs_three, awayPairs_four, awayPairs_five,
      touches, topRecip, edgeDecode, edgeState, pairMask, SS.stdBasis,
      SS.complement, SS.bxor]

/-- If either endpoint is an active singleton, the complementary hafnian
vanishes.  The second branch uses the kernel-checked transpose symmetry. -/
theorem compHaf_eq_zero_of_endpoint (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i m : Fin 6) (him : i ≠ m)
    (hactive : u d i ≠ 0 ∨ u d m ≠ 0) :
    compHaf d i m = 0 := by
  rcases hactive with hi | hm
  · have h := compHaf_forced c d hc hd hnc hnd hcode m i (Ne.symm him)
    rcases mul_eq_zero.mp h with hui | hstar
    · exact (hi hui).elim
    · rw [compHaf_swap d m i] at hstar
      simpa using congrArg star hstar
  · have h := compHaf_forced c d hc hd hnc hnd hcode i m him
    rcases mul_eq_zero.mp h with hum | hstar
    · exact (hm hum).elim
    · simpa using congrArg star hstar

end
end SixQubit.Orbit8Universal
