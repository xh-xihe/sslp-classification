import SixQubit.CodeWrap47
import SixQubit.CodeWrap18
import SixQubit.CodeWrap13

/-!
# Axiom audit for the three code-level wrappers

Every declaration below must print exactly

  `[propext, Classical.choice, Quot.sound]`

so in particular no `sorryAx` (which `sorry` would introduce) and no
`Lean.ofReduceBool` (which `native_decide` would introduce).

This module also serves as a *collision* test: the three wrappers live in three
distinct namespaces (`SixQubit.CodeWrap47`, `SixQubit.CodeWrap18`,
`SixQubit.CodeWrap13`) and share only `SixQubit.CodeBridge`, so they can all be
imported into one environment at once.
-/

-- The bridge: the two Knill--Laflamme obligations, the occupation-number rows
-- obtained by the character/occupation change of basis, the normalization, and
-- the derived orthogonality.
#print axioms SixQubit.innerC_eq_offSumOn
#print axioms SixQubit.innerC_eq_diagOn
#print axioms SixQubit.offSumOn_eq_zero_of_hasDistance
#print axioms SixQubit.diagOn_eq_of_hasDistance
#print axioms SixQubit.charOn_eq_of_hasDistance
#print axioms SixQubit.charOn_stdBasis
#print axioms SixQubit.charOn_stdBasis_pair
#print axioms SixQubit.occOn_eq_of_hasDistance
#print axioms SixQubit.occ2On_eq_of_hasDistance
#print axioms SixQubit.massOn_eq_one
#print axioms SixQubit.innerC_eq_zero_of_disjoint

-- Orbit 47: two off-diagonal rows, isolation certificate.
#print axioms SixQubit.CodeWrap47.moments
#print axioms SixQubit.CodeWrap47.orthogonal
#print axioms SixQubit.CodeWrap47.no_code

-- Orbit 18: seven off-diagonal rows.
#print axioms SixQubit.CodeWrap18.moments
#print axioms SixQubit.CodeWrap18.orthogonal
#print axioms SixQubit.CodeWrap18.no_code

-- Orbit 13: sixteen off-diagonal rows and eight diagonal rows.
#print axioms SixQubit.CodeWrap13.moments
#print axioms SixQubit.CodeWrap13.orthogonal
#print axioms SixQubit.CodeWrap13.no_code
