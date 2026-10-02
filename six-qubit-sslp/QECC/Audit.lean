import QECC

/-!
# Axiom audit for Section III (the `QECC` library)

One line per main declaration listed in `QECC/README.md`. A clean report for
each reads `[propext, Classical.choice, Quot.sound]`. `tools/verify.py` reads
this file as one of its audit roots, so every name below is also checked by
the repository-wide axiom gate.
-/

-- Section III.A: finite diagonal logical groups and reduced representatives.
#print axioms QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives

-- Section III.B: SSLP normal form, its converse, and the rank-two case.
#print axioms QECC.CodeProjector.general_sslp_normal_form
#print axioms QECC.CodeProjector.general_sslp_canonical_normal_form
#print axioms QECC.CodeProjector.general_sslp_converse
#print axioms QECC.general_sslp_directSum_converse
#print axioms QECC.CodeProjector.sslp_sector_probabilities_and_moments
#print axioms QECC.CodeProjector.rankTwo_sslp_normal_form
#print axioms QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic
#print axioms QECC.CodeProjector.exists_projectiveDiagonalGroup_zmod_model
#print axioms QECC.CodeProjector.rankTwo_sslp_canonical_normal_form

-- Section III.C: physical-order bounds and the distance-three refinement.
#print axioms QECC.CodeProjector.phaseSectors_positive_probability_commonFirstMoments
#print axioms QECC.NonsingularBinaryMatrix.exists_integral_finalSmithInvariant_smul
#print axioms QECC.CodeProjector.general_physicalOrder_bound
#print axioms QECC.CodeProjector.distanceThree_physicalOrder_bound
#print axioms QECC.CodeProjector.rankTwo_distanceTwo_physicalOrder_cutoff
#print axioms QECC.CodeProjector.rankTwo_distanceThree_physicalOrder_cutoff
#print axioms QECC.CodeProjector.rankTwo_physicalOrder_cutoff
