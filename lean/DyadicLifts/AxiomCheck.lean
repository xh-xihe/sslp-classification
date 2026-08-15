import DyadicLifts.DistanceTheorem
import DyadicLifts.CyclicOrder
import DyadicLifts.CarryTag
import DyadicLifts.LogicalGroup

/-!
# Axiom-footprint regression guard

This module pins the axiom dependencies of the headline theorems.  The build
*fails* (via `#guard_msgs`) if any of these ever start depending on a new axiom
— in particular if a `sorry`/`sorryAx` is ever introduced upstream, the printed
axiom set changes and this file stops compiling.

The expected footprint for every headline result is exactly the three sound
axioms of Lean/Mathlib: `propext`, `Classical.choice`, `Quot.sound`.  Notably
there is **no** `sorryAx` and **no** `Lean.ofReduceBool`/`Lean.trustCompiler`
(the abstract ladder uses no `native_decide`).
-/

namespace DyadicLifts

/-- info: 'DyadicLifts.two_anchor_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_anchor_ladder

/-- info: 'DyadicLifts.two_anchor_ladder_KLmat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_anchor_ladder_KLmat

/-- info: 'DyadicLifts.kl_propagation_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kl_propagation_step

/-- info: 'DyadicLifts.rung_orthonormal_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_orthonormal_SS

/-- info: 'DyadicLifts.rung_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_diagonal

/-- info: 'DyadicLifts.liftPair_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms liftPair_orthonormal

-- Tier-1 additions (exact diagonal orders and the general carry-tag criterion).

/-- info: 'DyadicLifts.orderOf_Rm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orderOf_Rm

/-- info: 'DyadicLifts.strong_carry_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strong_carry_tag

-- Tier-2 addition: the binary-dihedral clause realized on the rung code.

/-- info: 'DyadicLifts.rung_binary_dihedral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_binary_dihedral

end DyadicLifts
