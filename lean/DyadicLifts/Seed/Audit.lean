import DyadicLifts.Seed.Ladder

/-!
# Axiom audit for the kernel-checked seed

Every entry below is wrapped in `#guard_msgs`, so a change in the axiom
footprint is a build error rather than a line of output somebody has to read.
The target is the three standard axioms of Mathlib,

    [propext, Classical.choice, Quot.sound]

and in particular the absence of `Lean.ofReduceBool` and `Lean.trustCompiler`,
whose presence would mean a step was closed by compiled evaluation rather than
by the kernel, and of `sorryAx`, which would mean a gap.

This module is reached from the `DyadicLifts` root, so it runs in the default
build.
-/

/-- info: 'BD16Kernel.exists_distance3_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.exists_distance3_family

/-- info: 'BD16Kernel.seed_rung_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.seed_rung_diagonal

/-- info: 'BD16Kernel.seed_rung_binary_dihedral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.seed_rung_binary_dihedral

/-- info: 'BD16Kernel.hKL0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hKL0

/-- info: 'BD16Kernel.hKL1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hKL1

/-- info: 'BD16Kernel.hss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hss

/-- info: 'BD16Kernel.hn0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hn0

/-- info: 'BD16Kernel.hn1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hn1

/-- info: 'BD16Kernel.hsupp0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hsupp0

/-- info: 'BD16Kernel.hsupp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hsupp1

/-- info: 'BD16Kernel.hanchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hanchor

/-- info: 'BD16Kernel.hsc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.hsc

/-- info: 'BD16Kernel.k7_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.k7_two

/-- info: 'BD16Kernel.k9_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BD16Kernel.k9_two

/-- info: 'DyadicLifts.pauli_le_two_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DyadicLifts.pauli_le_two_decomp

/-- info: 'DyadicLifts.KLmatK_of_sites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DyadicLifts.KLmatK_of_sites

