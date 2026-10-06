import SixQubit.MaskBridge
import SixQubit.Orbit47Code
import SixQubit.Orbit12Code

/-!
# Axiom audit for the code-to-moment bridge

Every declaration below must print exactly

  `[propext, Classical.choice, Quot.sound]`

i.e. no `sorryAx`, no `Lean.ofReduceBool` (which is what `native_decide` would
introduce).
-/

-- The generic bridge: the two obligations and the derived orthogonality.
#print axioms SixQubit.MaskBridge.innerC_eq_walsh
#print axioms SixQubit.MaskBridge.IsCode.offSumG_eq_zero
#print axioms SixQubit.MaskBridge.IsCode.diagBotG_eq_diagTopG
#print axioms SixQubit.MaskBridge.IsCode.charSum_eq
#print axioms SixQubit.MaskBridge.IsCode.occ1_eq
#print axioms SixQubit.MaskBridge.IsCode.occ2_eq
#print axioms SixQubit.MaskBridge.IsCode.orthogonal
#print axioms SixQubit.MaskBridge.mass_eq_one
#print axioms SixQubit.MaskBridge.charSum_zMask1
#print axioms SixQubit.MaskBridge.charSum_zMask2

-- The orbit-47 instantiation.
#print axioms SixQubit.Orbit47.offSum_eq_offSumG
#print axioms SixQubit.Orbit47.logical_orthogonal
#print axioms SixQubit.Orbit47.moments
#print axioms SixQubit.Orbit47.no_code

-- The orbit-12 instantiation (exercises the diagonal obligation too).
#print axioms SixQubit.Orbit12.diagBot_eq_diagBotG
#print axioms SixQubit.Orbit12.diagTop_eq_diagTopG
#print axioms SixQubit.Orbit12.logical_orthogonal
#print axioms SixQubit.Orbit12.moments
#print axioms SixQubit.Orbit12.no_code
