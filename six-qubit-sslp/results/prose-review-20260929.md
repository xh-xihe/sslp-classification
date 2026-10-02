# Prose review of the 20260929 manuscripts

Review status: **partial**.

Two-agent semantic review on 2026-10-02 of the 20260929 sources against the QECC library (Bei Zeng's formalization of Section III) and the existing MainTheory, SixQubit and SS libraries. Section III (main.tex lines 606-2074) was split into seven chunks. For each chunk one agent reviewed every ledger entry and classified every mathematically substantive assertion of the running prose, including assertions inside proofs; a second agent re-read the same range and the cited declarations, tried to refute each judgement in both directions, and added what the first had missed; a third agent decided the entries on which the two disagreed. The same two-agent process re-reviewed the passages of main.tex outside Section III that changed since 20260924 (abstract, introduction, parts of Section II, the opening of Section IV), the 16 entries outside Section III that had a 20260924 review, the supplement's references into main.tex, the four recorded errata and four of the six 20260924 prose assertions (the other two lie in Section III and were re-reviewed there). A consistency reviewer then compared all chunks and found six cross-chunk contradictions, in four groups; each group was re-judged under one stated rule by a resolver and an adversarial verifier. No agent ran Lean; declarations were read from source, and names were then checked mechanically against the repository sources and by the kernel axiom gate. Reviews and reasons are written in our own words; no manuscript text is reproduced.

This is a version-bound review record, not a successful kernel run.
No previous-version coverage is transferred. No manuscript text is reproduced.

Generated from `results/prose-review-20260929.json`.

## main.tex:12 — nonmath

Preamble switch that loads the supplementary cross-references with or without citation import. Typesetting only.


## main.tex:67 — nonmath

Title, author, date and front matter. The reworded title is a scope label, not an assertion.


## main.tex:76 — covered

First abstract sentence: a transversal gate can have infinite physical order while its logical action has finite order. This is an existential claim. fully_certified, for any irrational t, gives an exact ((5,2,2)) code and a code-preserving diagonal product gate D(theta(t)) with no positive power equal to the identity whose projective class has order 3. Instantiating any irrational t gives the claim.

- `MainTheory.FiveQubitRationalization.fully_certified`

## main.tex:76 — tracked

Abstract claim that SSLP exhaustively describes exact exact codes with d>=2 whose diagonal logical action is nontrivial. This previews the forward and converse general normal form. The QECC carriers assume HasDistanceAtLeast d with 2<=d and a nonzero class, which matches the stated scope.

- `QECC.CodeProjector.general_sslp_normal_form`
- `QECC.CodeProjector.general_sslp_converse`

## main.tex:76 — tracked

The abstract claims that, in a fixed basis, the group is a finite abelian group, each of whose elements has a representative of finite order whose order is bounded uniformly in the code parameters. This previews thm:finite-projective-group together with thm:colored-finite-lift. The QECC carriers assume single-Z (number-operator) detection, which the distance-two scope of the preceding sentence supplies. They give q <= smithBeta(n+K-1), a uniform bound that needs no identification with beta. The identity class is represented by the identity.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.general_physicalOrder_bound`

## main.tex:76 — gap

Abstract claim that the structural results reduce classification at general rank to enumerating finitely many symmetry data and then imposing moment constraints and exact KL completion. That requires the SSLP normal form at a representative that also obeys the uniform order bound. No declaration in either library states this composite for general K. QECC.CodeProjector.general_sslp_normal_form is existential in its representative, MainTheory.PaperGeneralSSLP.general_sslp_normal_form is existential in q, and the bound theorems produce separate representatives. The fix is short, since every field of IntrinsicSSLPData is proved by lemmas valid for any reduced representative, but no declaration states the composite. Rank two is carried by the cited SSLPCompleteness theorems. Severity raised from the reader's medium to high: this is a headline abstract claim, and the rubric ties severity to the claim, not to the size of the fix.

- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_two`
- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_three`

## main.tex:76 — tracked

Abstract claim that the possible nontrivial full groups of exact ((6,2,3)) codes are exactly C_2, C_3 and C_5 (Result I). natCard_mem limits the group order to {1,2,3,5}, and isCyclic gives cyclicity. two_three_five_attained gives codes with elements of orders 2, 3 and 5. With natCard_mem and Lagrange the full group then has that order; for order five this step is OrderFiveOrbitMembership.natCard_eq_five_of_orderFive, while for 2 and 3 it is not a separate declaration.

- `MainTheory.IntrinsicOrderAudit.natCard_mem`
- `MainTheory.GeneralFiniteness.isCyclic`
- `MainTheory.SixQubitIntrinsicAttainment.two_three_five_attained`

## main.tex:76 — tracked

Abstract count of 15 realizable symmetry classes; previews Result II.

- `MainTheory.RealizationOrbits15.card_realization_orbits`

## main.tex:76 — tracked

Abstract claim that complete enumerator sets are determined for 11 of the 15 classes; previews Result III.

- `MainTheory.WImageSettled62.all_11_realized_WImages`

## main.tex:76 — tracked

Abstract claim that six qubits is the minimum for one logical qubit at d>=3 with a single-block transversal gate of projective order 5, and that the code is unique at that length up to LU and permutations. This previews the three clauses of the corollary. The non-Clifford qualifier is a separate item.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

## main.tex:76 — gap

The abstract calls the order-5 gate non-Clifford. Neither library defines a Clifford group, so nothing states that the attaining code's transversal group lies outside the projective Clifford group. The qualifier is mathematically automatic, because the projective one-qubit Clifford group has no element of order 5. The lower bound and the uniqueness do not depend on it.


## main.tex:123 — nonmath

Motivational remark that the first difficulty is that no discrete algebraic description is available.


## main.tex:127 — nonmath

Literature survey of nonadditive constructions and descriptions, attributed to cited work. It ends with commentary that continuous families must be handled from the start.


## main.tex:152 — tracked

Description of SSLP, attributed to the cited reference. A fixed finite-order diagonal gate splits the basis into modular subset-sum sectors, and the KL conditions for diagonal Paulis become linear constraints on sector distributions. This previews the moment consequence of the general normal form. The QECC carrier proves the forward implication from full KL to the target distance.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`

## main.tex:160 — nonmath

Attribution of earlier constructions to the cited reference: a ((6,2,3)) code carrying a transversal order-five rotation, and ((7,2,3)) codes with T and sqrt T. The six-qubit code is re-established in Section IV (MinimumLengthOrderFive.canonical_attains). The seven-qubit codes are cited, not claimed.


## main.tex:163 — covered

Claims that a diagonal product gate preserving the code may have infinite physical order while its projective logical order is finite. fully_certified exhibits one: a ((5,2,2)) code and a gate D(theta(t)), irrational t, with no identity power and projective class of order 3.

- `MainTheory.FiveQubitRationalization.fully_certified`

## main.tex:166 — tracked

Claims that even q_min can exceed m, previewing the seven-qubit example of III.A, which concludes q_min = 12 > 6 = m in eq:example-minimum-order-gap. Its coverage is that entry's. No Lean declaration witnesses q_min > m for any code. The formalized five-qubit example has q_min = m = 3 (FiveQubitRationalization.minimum_lift_three).


## main.tex:168 — nonmath

Rhetorical question and statement of the paper's central problem.


## main.tex:172 — gap

The Introduction says the projective diagonal group is finite abelian, that every element has a finite-order representative and that the order is uniformly bounded. It gives no detection or distance hypothesis, and the surrounding introduction supplies none. Without single-site Z detection the claim fails. For the d=1 code span{|00>,|10>}, D(phi,0) acts as diag(1,e^{2 pi i phi}): the group is a circle, and irrational phi has no finite-order representative. The qualified statements are carried by the cited QECC theorems, which assume DetectsSingleZ or DetectsNumberOps. Medium rather than high: this is a dropped hypothesis in a summary sentence whose qualified content is carried, and the abstract states the qualified form.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.general_physicalOrder_bound`

## main.tex:176 — tracked

Previews the sharper bound for K=2 and d>=3. Its hypotheses (rank two, d>=3) are stated in the sentence and match the corollary and the QECC carrier.

- `QECC.CodeProjector.distanceThree_physicalOrder_bound`

## main.tex:177 — gap

Claims that the preceding results make SSLP a finite classification procedure, with no stabilizer or additivity assumption. This is the same composite as the abstract's reduction sentence: the normal form at a representative that obeys the uniform order bound. Neither library states it for general K; only K=2 is carried, by the SSLPCompleteness theorems. The no-stabilizer scope is accurate, since ExactCode and CodeProjector carry no stabilizer data. Severity raised from medium to high because this is the paper's central structural claim.

- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_two`
- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_three`

## main.tex:180 — tracked

Of the 66 candidate classes exactly 15 have exact realizations; previews Result II.

- `MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys`

## main.tex:182 — tracked

The possible nontrivial full groups are C_2, C_3 and C_5; previews Result I. Attainment of each as a full group needs the Lagrange step noted for the abstract.

- `MainTheory.IntrinsicOrderAudit.natCard_mem`
- `MainTheory.SixQubitIntrinsicAttainment.two_three_five_attained`

## main.tex:183 — tracked

Complete enumerator sets are determined for eleven realizable classes; previews Result III.

- `MainTheory.WImageSettled62.all_11_realized_WImages`

## main.tex:184 — tracked

Claims the order-five code is, up to LU and permutations, the only minimal-length exact code with one logical qubit, d>=3 and a transversal gate of projective order five. This previews the corollary together with thm:unique-C5-LU. Identifying the displayed code with the cited reference's code is attribution. The non-Clifford wording is covered by the next item.

- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

## main.tex:189 — gap

Defines non-Clifford: no logical basis puts the whole projective transversal group inside the projective Clifford group. Neither library defines a Clifford group, and nothing proves that the order-five code's group lies outside it, although that is automatic for an element of order 5. The definition carries the broader minimum-length claim about non-Clifford gates at lines 2633-2639, outside these ranges, which has no Lean counterpart. Medium for that reason.


## main.tex:193 — nonmath

Author contributions and workflow attribution.


## main.tex:200 — nonmath

Section II heading and roadmap, plus the scope remark that no additivity or stabilizer structure is assumed.


## main.tex:212 — nonmath

Subsection heading and roadmap about separating diagonal from off-diagonal KL matrix elements.


## main.tex:268 — tracked

Restates eq:logical-basis-KL in words: equal diagonal and zero off-diagonal logical matrix elements. Only line 269 is in the changed range.


## main.tex:269 — gap

New bridge sentence: all diagonal requirements become moment equations in squared amplitudes, while the off-diagonal ones belong to the completion. That holds only for diagonal Paulis Z_J. For an error with an X or Y factor, the diagonal logical element pairs amplitudes at x and x XOR e and is not a function of |c_x|^2. Section II.C (lines 586-590) itself places both requirements for such errors in the KL stage. The Z_J-restricted implication is carried by the QECC moment theorem. Low, because no result rests on the overstatement.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`

## main.tex:274 — tracked

Lead-in attributing the bound to the cited reference. Its coverage is that of the partial entry eq:quantum-Singleton, which is unqualified and false for K=1.


## main.tex:274 — gap

This is the 20260924 item recorded at line 284; the lead-in was at 285 there and is at 274 in 20260929. The lead-in credits the cited reference with the display that follows and adds no rank restriction, so eq:quantum-Singleton is still stated for all codes. Under the paper's KL definition that is false at rank one, because a rank-one code meets the KL equations at every distance. violates_unrestricted_singleton exhibits such a code. Only the K>=2 form is proved, by quantum_singleton. Severity stays high, matching the 20260924 record and the open erratum singleton-rank-one: the text states a false bound, not merely an unformalized true one, although by importance alone it would be a medium-tier standalone fact.

- `MainTheory.SingletonRankOneCounterexample.violates_unrestricted_singleton`
- `MainTheory.QuantumSingleton.quantum_singleton`

## main.tex:279 — covered

For n=6 and K=2 the bound gives d<=3, which needs only the K>=2 bound: six_qubit_distance_le_three. Imposing KL for weight<=2 is by definition SS.HasDistance 3, and exactCode_distance_three shows that every ExactCode 6 2 3 has distance 3 and not 4, with a weight-3 Pauli that violates KL.

- `MainTheory.QuantumSingleton.six_qubit_distance_le_three`
- `MainTheory.SixQubitExactDistance.exactCode_distance_three`

## main.tex:279 — covered

This is the consequence sentence of the same Singleton paragraph. For n=6 and K=2 it concludes d<=3, and so it certifies exact ((6,2,3)) codes by imposing KL for all Paulis of weight <=2. It is the K=2 case, where the bound is valid. MainTheory.QuantumSingleton.six_qubit_distance_le_three proves d<=3 for every ExactCode 6 2 d, using the genuine KL predicate. SS.HasDistance with d=3 means detection of every Pauli of weight at most two, which matches the certification convention. The rank-one defect of the display does not reach this sentence.

- `MainTheory.QuantumSingleton.six_qubit_distance_le_three`
- `SS.HasDistance`

## main.tex:283 — tracked

Lead-in to the Shor-Laflamme enumerator definitions. The remark that they do not depend on a logical basis holds because they are defined from the projector P. In Lean the frame-based Aco is rewritten as a sum of |tr(E P)|^2 over the projector kernel by Aco_eq_sum_normSq_trace.

- `MainTheory.PauliKernelTrace.Aco_eq_sum_normSq_trace`

## main.tex:320 — tracked

Roadmap remark that the search and the final classification use different equivalences, then the lead-in to the LU-with-permutations definition. Line 323 completes the sentence. Formal counterpart: LUEquivalent.

- `MainTheory.ClassificationLevels.LUEquivalent`

## main.tex:357 — tracked

Says bit flips and coordinate permutations supply the canonical normalizations of SSLP data. The canonical normal forms do this: their witnesses are an XOR shift (local X) and a coordinate permutation, with the coefficients sorted. The rank-two form also uses label interchange and a unit power of the generator.

- `QECC.CodeProjector.rankTwo_sslp_canonical_normal_form`
- `QECC.CodeProjector.general_sslp_canonical_normal_form`

## main.tex:360 — nonmath

Subsection heading and motivation for separating logical action from physical representatives.


## main.tex:433 — nonmath

Commentary that the cited no-go results supply neither a finite-order representative nor a uniform order bound, with a roadmap pointer to Section III.


## main.tex:442 — tracked

Describes the three SSLP layers (discrete subset-sum sets, convex LP, full complex KL completion) and defines exact completion. This previews the staged form eq:sslp-three-layers and its general-rank version eq:three-layers.


## main.tex:599 — tracked

Rank-two context of II.C: once q is bounded the search is finite. This previews the rank-two finite enumeration. MainTheory carries it with bounded q and the sorted normal form together, and QECC gives the symbolic cutoff.

- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_three`
- `QECC.CodeProjector.rankTwo_physicalOrder_cutoff`

## main.tex:600 — tracked

Roadmap: Section III will show that finite-order gates lose no diagonal symmetry (thm:finite-projective-group) and that q can be bounded in advance (thm:colored-finite-lift).


## main.tex:606 — nonmath

Section title and label.


## main.tex:609 — tracked

Poses the two questions the section answers: existence of finite-order representatives (thm:finite-projective-group) and a uniform bound on q (thm:colored-finite-lift, label at main.tex 1618). The claim that SSLP becomes an exhaustive finite classification summarizes those results.


## main.tex:615 — tracked

Previews the III.A proof: integer-matrix description of preservation, scalar action of homogeneous directions, and a common rational denominator for every class. Coverage is that of the named entries.


## main.tex:619 — tracked

Previews III.B: the eigenspaces of the representative give the SSLP subset-sum data.


## main.tex:620 — tracked

Previews the III.C uniform bound on q, which makes the outer enumeration finite.


## main.tex:623 — nonmath

Points to Section IV and fixes the convention that diagonal means diagonal in the chosen local product basis.


## main.tex:627 — nonmath

Subsection title and label.


## main.tex:630 — tracked

Sets up the existence question and leads into the preservation condition displayed at 633.


## main.tex:636 — covered

The claim is that a code-preserving diagonal gate restricts to a unitary on the code. MainTheory.DiagonalLogicalMatrixBridge.logicalMatrix_unitary states that whenever a diagonal product gate maps an orthonormal frame of the code to the frame times a K-by-K matrix Q (Q is the matrix of the restriction in that frame), Q is unitary on both sides. QECC.CodeProjector.logicalEquiv supplies the restriction of a preserving gate as an invertible linear map of the code space. The reader found no unitarity statement in QECC; the MainTheory declaration states it in frame coordinates.

- `MainTheory.DiagonalLogicalMatrixBridge.logicalMatrix_unitary`
- `QECC.CodeProjector.logicalEquiv`

## main.tex:636 — tracked

Says logical operators are identified up to a common scalar and leads into the definition of G_diag(P).


## main.tex:648 — covered

Defines the projective logical order as the order of an element of G_diag(P). In Lean this is addOrderOf U for U in ProjectiveDiagonalGroup, the quantity used in the main III.A theorem.

- `QECC.CodeProjector.ProjectiveDiagonalGroup`
- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`

## main.tex:649 — nonmath

Remarks that finiteness is not yet established. Commentary only.


## main.tex:652 — tracked

Says only single-site Z detection is assumed. The Lean main theorem's only hypothesis is DetectsSingleZ.


## main.tex:658 — covered

The paper defines N_j through Z_j and then asserts its eigenvalue on |x> is x_j. QECC.numberOp j is the diagonal matrix with entry x_j, and zOp_eq_one_sub_two_numberOp identifies it with (I - Z_j)/2, so together they state the assertion.

- `QECC.numberOp`
- `QECC.CodeProjector.zOp_eq_one_sub_two_numberOp`

## main.tex:659 — tracked

States the equivalence displayed in eq:Nj-detection; only the forward direction with an existential mu is in Lean (see that entry).


## main.tex:667 — tracked

Introduces the phase torus defined in the next display.


## main.tex:677 — covered

preservingPhases is an AddSubgroup of the torus with carrier Preserves.

- `QECC.CodeProjector.preservingPhases`

## main.tex:683 — tracked

Previews the integer-constraint description of preservation.


## main.tex:684 — gap

The sentence describes the lemma as producing a rational representative while keeping the homogeneous component. The lemma does the opposite: it keeps the image At and changes t by a vector in ker A, i.e. it removes a homogeneous component. As written, no declaration states this description. The correct property is carried by QECC.integerMatrix_uniform_rational_lift (whose docstring has a similar loose phrasing); only the description is off.

- `QECC.integerMatrix_uniform_rational_lift`

## main.tex:699 — tracked

Proof setup: B is the transpose of A times A over Q, and G is chosen as its generalized inverse.


## main.tex:706 — covered

matrix_exists_generalizedInverse proves a rational generalized inverse exists, by the same right-inverse-on-the-range construction.

- `QECC.matrix_exists_generalizedInverse`

## main.tex:707 — covered

A positive integer clearing all denominators of G exists: Mathlib's Matrix.den is nonzero and Matrix.num divided by Matrix.den recovers G entrywise. The QECC lemma takes Q_A to be G.den.

- `Matrix.den_ne_zero`
- `Matrix.num_div_den`

## main.tex:710 — gap

Local step inside the proof of lem:uniform-rational-section: integrality of the auxiliary vectors and the identity d = Bt. They appear only as internal steps of QECC.integerMatrix_uniform_rational_lift, which carries the enclosing lemma.


## main.tex:716 — gap

Local step: t - a/Q_A lies in ker B. It is internal to the proof of QECC.integerMatrix_uniform_rational_lift, which carries the enclosing lemma.


## main.tex:716 — covered

Mathlib's Matrix.ker_mulVecLin_transpose_mul_self states this kernel equality over any linearly ordered field; the QECC proof uses it.

- `Matrix.ker_mulVecLin_transpose_mul_self`

## main.tex:721 — tracked

States the lemma's conclusion.


## main.tex:724 — nonmath

Describes the scope and ingredients of the coming theorem and defines the word abelian.


## main.tex:748 — tracked

Lead-in to the definition of s_t(x).


## main.tex:752 — covered

diagonalGate is diagonal with entry toCircle(supportPhase theta x); supportPhase_coe_real identifies supportPhase of a real vector with the class of the real subset sum, and AddCircle.toCircle_apply_mk evaluates toCircle of a real class as exp(2 pi i s).

- `QECC.diagonalGate`
- `QECC.supportPhase_coe_real`
- `AddCircle.toCircle_apply_mk`

## main.tex:752 — tracked

Lead-in to the entry formula.


## main.tex:763 — tracked

Lead-in to the definition of A_P; Lean indexes rows by the finite Edge subtype instead of an ordering.


## main.tex:768 — tracked

Lead-in to the preservation iff.


## main.tex:777 — tracked

Lead-in: take h in the real kernel of A_P and form H_h.


## main.tex:783 — covered

The paper defines H_h as a weighted sum of number operators and asserts it is diagonal with eigenvalue h.x. weightedNumberOp h is the diagonal with entry s_h(x), and weightedNumberOp_eq_sum identifies it with the weighted sum.

- `QECC.CodeProjector.weightedNumberOp`
- `QECC.CodeProjector.weightedNumberOp_eq_sum`

## main.tex:787 — covered

weightedNumberOp_commutes states the commutation under the edge-equality hypothesis, which is kernel membership by edgeMatrix_mulVec. The line also leads into displaymath@788.

- `QECC.CodeProjector.weightedNumberOp_commutes`
- `QECC.CodeProjector.edgeMatrix_mulVec`

## main.tex:791 — tracked

Lead-in to the chain giving H_h P as a scalar times P.


## main.tex:795 — tracked

Lead-in: exponentiate to get the scalar action of D(h). The entry is carried with its explicit scalar via MainTheory (one_parameter_scalar with same_cell_direction), whose proof is entrywise rather than by exponentiation; QECC alone exports only an unspecified scalar.


## main.tex:800 — covered

Under number-operator detection, every real h with A_P h = 0 gives a phase that acts as one common scalar on the code.

- `QECC.CodeProjector.actsAsScalar_of_edgeMatrix_mulVec_eq_zero`
- `QECC.CodeProjector.actsAsScalar_iff_gate_mul_proj`

## main.tex:802 — covered

preserves_integral_edge_values gives integrality of A_P on the canonical real lift of a preserving theta (any other lift is covered by the eq:preservation-integer-matrix chain). integerMatrix_uniform_rational_lift applied to the edge matrix supplies Q_0 and c.

- `QECC.integerMatrix_uniform_rational_lift`
- `QECC.CodeProjector.preserves_integral_edge_values`

## main.tex:815 — covered

A_P h = 0 is the lemma's conclusion. For the paper's own c, A_P r = A_P t is integral by linearity, and the reverse direction of eq:preservation-integer-matrix, carried by the chain of stated equivalences recorded there, gives that D(r) preserves P. The packaged Lean form for Lean's own witness is exists_uniform_rationalPhase_representative, which obtains preservation of its rational representative by another route (theta minus a scalar-acting phase).

- `QECC.integerMatrix_uniform_rational_lift`
- `QECC.CodeProjector.preserves_iff_gate_conjugates`
- `QECC.supportPhase_coe_real`
- `AddCircle.coe_eq_zero_iff`
- `QECC.CodeProjector.edgeMatrix_mulVec`
- `QECC.CodeProjector.exists_uniform_rationalPhase_representative`

## main.tex:816 — tracked

Lead-in to the factorization of D(t)P.


## main.tex:821 — covered

For the paper's own h = t - r, A_P h = 0 makes h act as a scalar (actsAsScalar_of_edgeMatrix_mulVec_eq_zero); with diagonalGate_add this gives D(t)P = z D(r)P for a unit z, which projectiveClass_eq_iff_gate_restrictions turns into equality of projective classes. exists_uniform_rationalPhase_representative states the same for Lean's own witness.

- `QECC.CodeProjector.actsAsScalar_of_edgeMatrix_mulVec_eq_zero`
- `QECC.CodeProjector.actsAsScalar_iff_gate_mul_proj`
- `QECC.diagonalGate_add`
- `QECC.CodeProjector.projectiveClass_eq_iff_gate_restrictions`

## main.tex:823 — covered

rationalPhase Q c is phaseHom of c mod Q, so it depends only on the residues; every class has such a representative, and the finite residue set surjects onto the group.

- `QECC.rationalPhase_eq_phaseHom`
- `QECC.CodeProjector.exists_uniform_rationalPhase_representative`
- `QECC.CodeProjector.projectiveDiagonalGroup_finite_of_uniform`

## main.tex:829 — covered

Finiteness under number-operator detection, which the main theorem obtains from Z detection.

- `QECC.CodeProjector.projectiveDiagonalGroup_finite`

## main.tex:829 — covered

The commutes field of the conclusion. The Lean group is an additive quotient of phase vectors, which encodes commuting diagonal gates through diagonalGate_add.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`

## main.tex:832 — tracked

Fixes a nonidentity element and its rational representative and leads into the definition of q.


## main.tex:840 — covered

Q times rationalPhase Q c is zero, so the rational representative has finite order.

- `QECC.rationalPhase_nsmul`
- `QECC.rationalPhase_isOfFinAddOrder`

## main.tex:840 — covered

projectiveClassMap is an additive homomorphism, so a representative of a nonzero class is nonzero; exists_reducedDiagonalRepresentative turns a nonzero finite-order phase into R with R.phase equal to it and q >= 2.

- `QECC.exists_reducedDiagonalRepresentative`
- `QECC.CodeProjector.projectiveClassMap`

## main.tex:843 — tracked

Lead-in to writing r with numerators a_j over q.


## main.tex:848 — covered

diagonalGate of R.phase is the product gate with phases a_j/q, i.e. D(a;q).

- `QECC.ReducedDiagonalRepresentative.phase`
- `QECC.diagonalGate`

## main.tex:848 — covered

Proved by evaluating at the one-hot basis strings, the same argument as the text.

- `QECC.diagonalGateHom_injective`

## main.tex:851 — covered

The matrix order equals the additive order of the phase vector, which is R.q.

- `QECC.diagonalGate_order`
- `QECC.ReducedDiagonalRepresentative.orderOf_diagonalGate`

## main.tex:854 — tracked

Lead-in to the gcd contradiction step.


## main.tex:861 — covered

commonGCD_eq_one states that the gcd of q and the canonical numerators is 1.

- `QECC.ReducedDiagonalRepresentative.commonGCD_eq_one`

## main.tex:862 — covered

The representative clause includes that addOrderOf U divides R.q, proved by mapping the physical order through the class map.

- `QECC.CodeProjector.exists_reduced_representative`

## main.tex:868 — nonmath

Transition sentence.


## main.tex:869 — tracked

Relates the kernel step to the Eastin-Knill infinitesimal principle; the general form for arbitrary detectable single-site generators is attributed to cited work reviewed in Section II. The instance used here, for Z-type generators, is eq:kernel-direction-scalar, which is carried with its explicit scalar via MainTheory (one_parameter_scalar with same_cell_direction).


## main.tex:872 — tracked

Restates the theorem's scope: only Z_j detection is assumed and the conclusion is restricted to gates diagonal in the fixed basis.


## main.tex:874 — tracked

Previews the seven-qubit example (rational replacement of an irrational phase, and q_min strictly above m). Its coverage is that example's, outside this chunk; QECC has no seven-qubit model.


## main.tex:1042 — tracked

Restates the conclusion of thm:finite-projective-group for each code under its Z-detection hypothesis: finitely many projective diagonal logical elements, each with a finite-order physical representative. The QECC theorem gives finiteness and, for every nonzero class, a reduced representative of exact order q; the identity class is trivially represented by the zero phase vector. The opening clause, that the first question is now answered, is roadmap.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`

## main.tex:1044 — tracked

Previews the uniform bounds on q_min proved in Section III.C: thm:colored-finite-lift gives the bound in n and K, and cor:d3-physical-order-bound the distance-three refinement. The remark that per-code finiteness gives no uniform bound describes what Section III.A provides and is not a separate theorem. MainTheory's colored lift bounds qmin by betaOf(n+ell-1) <= betaOf(n+K-1), which is beta_{n+K-1} through the Smith-witness bridge and betaOf_eq_of_exact. QECC bounds minimalPhysicalOrder U by smithBeta(n+K-1). That is a uniform bound in (n, K) even though smithBeta is not identified with beta.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.D3AffineRankBound.d3_bound_same_class_at_affineRank`
- `QECC.CodeProjector.general_physicalOrder_bound`
- `QECC.CodeProjector.distanceThree_physicalOrder_bound`

## main.tex:1049 — gap

A standalone remark that the modulus of a presentation is not an invariant, with three clauses: replacing (q,a) by (rq,ra) keeps the local phases, keeps the subset-sum solution sets, and introduces a common factor. The solution-set clause is carried in general by Sk_scale: the solution set of the scaled vector at the scaled residue equals S_b(a;q) for r > 0. The local-phase clause is carried in the scaling direction by scaled_color_phase, which gives omega_{Q}^{(Q/m) gamma} = e^{2 pi i gamma/m} for m | Q. With Q = rq, m = q and canonicalRoot_pow, this gives omega_{rq}^{r a_j} = omega_q^{a_j} coordinatewise; finiteLocalPhase_reduced gives the same identity in the reduction direction. The common-factor clause, that gcd(rq, ra_1, ..., ra_n) is divisible by r so the scaled pair is not in reduced form when r >= 2, has no general Lean statement; only one fixed instance (MainTheory.Gate.not_primitive_allEven) exists. That clause is elementary, and nothing later depends on the remark, but under this run's rubric a standalone fact with an unstated clause is a medium gap.

- `MainTheory.ScaledModulusFibres.Sk_scale`
- `MainTheory.ScaledColorPhases.scaled_color_phase`
- `MainTheory.ScaledColorPhases.canonicalRoot_pow`
- `MainTheory.PrimitiveReduction.finiteLocalPhase_reduced`

## main.tex:1051 — tracked

States the scope of the III.C result: it bounds q_min, not every presentation or every physical representative. The Lean conclusion matches. GeneralPhysicalOrderBoundConclusion bounds minimalPhysicalOrder U and the order of one constructed representative, never all representatives. The implied existence of unbounded presentations or representatives rests on the preceding scaling remark and on the example's irrational-t family, not on a separate theorem.

- `QECC.CodeProjector.general_physicalOrder_bound`

## main.tex:1055 — nonmath

Section title and label.


## main.tex:1058 — tracked

Recalls the finite-order representative from III.A and previews the theorem: the representative forces the logical eigenspaces into labeled fibers, stated as a normal form at arbitrary rank K.


## main.tex:1063 — gap

The first clause (the statement concerns one chosen nontrivial element) restates the theorem's setup. The second clause asserts that for general K the finite abelian projective diagonal group can fail to be cyclic. No declaration in QECC, MainTheory, SixQubit or SS exhibits a code with a non-cyclic projective diagonal group; a search for non-cyclicity statements found none. It is a standalone remark.


## main.tex:1065 — tracked

Previews the rank-two corollary, where one element generates the whole group. Its cyclicity clause is stated by projectiveDiagonalGroup_isAddCyclic under single-Z detection.

- `QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic`

## main.tex:1117 — covered

Distance at least two implies detection of every single-qubit Z.

- `QECC.CodeProjector.detectsSingleZ_of_hasDistanceAtLeast_two`

## main.tex:1118 — covered

The representative field of the III.A theorem gives, for each nonzero class, a reduced D(a;q) representing it, with gcd one, exact physical order q and logical order dividing q. intrinsic_sslp_normal_form records the same facts (class_eq, commonGCD_eq_one, physicalOrder, logicalOrder_dvd_physical) for the representative it uses.

- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`
- `QECC.CodeProjector.intrinsic_sslp_normal_form`

## main.tex:1122 — nonmath

Paragraph heading and lead-in to the display defining H_b and E_b.


## main.tex:1131 — covered

fiberSubspace_eq_eigenspace states that each fiber subspace equals the eigenspace of the finite diagonal gate for eigenvalue zeta^b. In QECC the gate acts on the fiber at b by the scalar for b, and distinct residues give distinct scalars.

- `MainTheory.GeneralColoredSubspaces.fiberSubspace_eq_eigenspace`
- `QECC.diagonalGate_phaseHom_mulVec_of_mem_fiberSubspace`
- `QECC.zmodPhaseScalar_injective`

## main.tex:1131 — covered

If the modular gate preserves the code, the code projector commutes with every fiber projector, so the spectral projectors preserve the code.

- `QECC.CodeProjector.commutes_fiberProjector`

## main.tex:1137 — covered

The residues with nonzero sector form C.ActiveResidue a, and each such sector has positive finrank.

- `QECC.CodeProjector.ActiveResidue`
- `QECC.CodeProjector.activeResidue_finrank_pos`

## main.tex:1144 — covered

A nonzero projective class of the modular gate has at least two active sectors: 2 <= Fintype.card (C.ActiveResidue a).

- `QECC.CodeProjector.two_le_card_activeResidue_of_projectiveClass_ne_zero`

## main.tex:1146 — covered

phaseSector_support says that a sector vector vanishes at every x outside its fiber. So any x0 with nonzero amplitude in a vector of the anchor sector has A_a(x0) equal to the anchor label, which is the asserted implication. Despite its name, exists_support_string_of_activeResidue only states that some string lies in the anchor fiber, without the nonzero-amplitude property; that is all the later normalization needs.

- `QECC.CodeProjector.phaseSector_support`
- `QECC.CodeProjector.exists_support_string_of_activeResidue`

## main.tex:1153 — tracked

Lead-in to the one-qubit identity.


## main.tex:1159 — tracked

Connective introducing the n-qubit conjugation identity.


## main.tex:1168 — tracked

Lead-in to the subset-sum translation identity.


## main.tex:1175 — covered

xorPhaseSectorEquiv is the linear equivalence (by X^t reindexing) from the sector at b to the conjugated code's sector at b - A_a(t), with equal finrank. xorActiveResidueEquiv_apply_val gives the label shift, and the conjugation identity supplies the discarded common scalar.

- `QECC.CodeProjector.xorPhaseSectorEquiv`
- `QECC.CodeProjector.xorActiveResidueEquiv_apply_val`
- `QECC.CodeProjector.finrank_xorPhaseSector`
- `QECC.reindexOperator_xor_diagonalGate_phaseHom`

## main.tex:1181 — covered

The anchor's relative residue is zero. Sign flips preserve the exact order q of the residue vector, which is reducedness, and the order of the physical gate. X-conjugation preserves Pauli weight and the distance-at-least-d property for every d. Because X^t reindexing is involutive, the reverse direction is an instance of the same lemma, so the distance is preserved exactly.

- `QECC.CodeProjector.relativeResidues_anchor`
- `QECC.xorCoefficient_primitive`
- `QECC.orderOf_diagonalGate_xorCoefficient`
- `QECC.PauliString.weight_xorReindex`
- `QECC.CodeProjector.hasDistanceAtLeast_reindex_xor`
- `QECC.CodeProjector.reindex_xor_involutive`

## main.tex:1185 — tracked

Lead-in stating that the projective order is the least r of the next display; carried with that entry.


## main.tex:1191 — covered

The relativeOrder clause of the intrinsic normal form states that the additive order of the relative residues equals addOrderOf U = m. The rest of the sentence introduces the m-torsion display (mem_range_colorEmbed_iff).

- `QECC.CodeProjector.intrinsic_sslp_normal_form`
- `QECC.CodeProjector.projectiveOrder_eq_relativeResiduesOrder`
- `QECC.mem_range_colorEmbed_iff`

## main.tex:1197 — covered

Every residue mod q killed by m has a unique color in Z_m under the embedding.

- `QECC.existsUnique_color_of_nsmul_eq_zero`

## main.tex:1202 — covered

The color function obtained from the relative residues is injective and vanishes at the anchor. The trailing clause introduces the order display.

- `QECC.CodeProjector.exists_primitive_sslp_colors`

## main.tex:1208 — covered

The pointwise color embedding is an injective additive map, so the color vector has the same order as the relative residues, namely m. exists_primitive_sslp_colors concludes ColorPrimitive and colorGCD = 1.

- `QECC.CodeProjector.colorVectorEmbed_injective`
- `QECC.CodeProjector.exists_primitive_sslp_colors`
- `QECC.colorPrimitive_iff_gcd_eq_one`

## main.tex:1212 — covered

Some coordinate permutation makes the canonical numerators nondecreasing. The normalization theorem combines it with the X^t step and transports the fibers.

- `QECC.exists_permuteCoefficient_monotone_val`
- `QECC.CodeProjector.exists_xor_permutation_normalization`

## main.tex:1215 — covered

Exact residue order and gcd one survive the permutation, as does the physical gate order. Sector finranks are preserved, and the canonical data records the preserved projective order. The distance-at-least-d property is preserved for every d; this is the reading of 'code distance' the paper uses for ((n,K,d)) codes and the one the theorem needs. The converse inequality would be the same lemma applied to the inverse permutation, which Lean does not package.

- `QECC.permuteCoefficient_primitive`
- `QECC.orderOf_diagonalGate_permuteCoefficient`
- `QECC.CodeProjector.canonical_commonGCD_eq_one`
- `QECC.CodeProjector.finrank_coordinatePhaseSector`
- `QECC.CodeProjector.hasDistanceAtLeast_reindex_coordinate`
- `QECC.CodeProjector.exists_canonical_general_sslp_data`

## main.tex:1224 — tracked

Concludes the forward half of the theorem.


## main.tex:1224 — gap

Asserts that a sector can be a proper subspace of its fiber span, so zero coefficients must be kept. Lean proves only the inclusion. No public declaration states that an active sector is strictly smaller than its fiber span for some code; the SixQubit files mention proper supports only in docstrings. The methodological consequence is commentary.


## main.tex:1228 — covered

Distinct colors embed to distinct residues. Subspaces in distinct fibers are then mutually orthogonal (ColoredSubspaces.orthogonal) and independent; both are derived from the paper's hypotheses, not assumed.

- `MainTheory.ColoredResidueArithmetic.scaledColor_injective`
- `QECC.colorEmbed_injective`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.orthogonal`
- `MainTheory.GeneralColoredSubspaceConverse.ColoredSubspaces.independent`

## main.tex:1238 — covered

A sum of mutually orthogonal orthogonal projectors is Hermitian and idempotent. The orthogonality input is the fact established in the preceding sentence.

- `QECC.FiberProjectorFamily.totalProjector_hermitian`
- `QECC.FiberProjectorFamily.totalProjector_idempotent`

## main.tex:1247 — tracked

Lead-in to the scalar display.


## main.tex:1253 — covered

The modular gate preserves the direct-sum code. MainTheory's converse returns D(a;q) as an element of that code's diagonal symmetry group.

- `QECC.FiberProjectorFamily.codeProjector_preserves`
- `MainTheory.PaperGeneralSSLP.general_sslp_converse`

## main.tex:1253 — covered

The k-th power is projectively trivial exactly when k kills every relative residue in Z_q. Because gamma_1 = 0, the relative residues are the scaled colors, and k kills a scaled color in Z_q exactly when k kills the color in Z_m (colorEmbed is an injective additive map; mul_scaledColor_eq_zero_iff in MainTheory). MainTheory's intrinsicClass_pow_eq_one_iff gives the frame form, without primitivity: a power of the class is trivial iff every eigenvalue ratio to the zero-label eigenvalue is killed. The reader's class_pow_iff already assumes primitivity, so it states the next step, not this one.

- `QECC.CodeProjector.nsmul_projectiveClass_eq_zero_iff`
- `QECC.colorEmbed_injective`
- `MainTheory.ColoredResidueArithmetic.mul_scaledColor_eq_zero_iff`
- `MainTheory.GeneralColoredConverse.intrinsicClass_pow_eq_one_iff`

## main.tex:1260 — covered

Both state that the induced class of D(a;q) on the constructed code has order exactly m.

- `MainTheory.PaperGeneralSSLP.general_sslp_converse`
- `QECC.FiberProjectorFamily.projectiveOrder_eq_of_primitive_colors`

## main.tex:1260 — covered

Basis-independent KL on the subspace is equivalent to the frame KL condition. The converse returns an ExactCode of rank K and distance at least d0 that spans the sum.

- `MainTheory.SubspaceCode.hasDistance_iff`
- `MainTheory.PaperGeneralSSLP.general_sslp_converse`

## main.tex:1266 — tracked

Previews that every exact completion yields the LP moment data defined and asserted in the next two entries.


## main.tex:1274 — covered

Nonnegativity, total mass one and vanishing outside the fiber are each stated. Zero values inside the fiber are not excluded, which is the paper's remark.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`
- `QECC.CodeProjector.sectorDistribution_nonneg`
- `QECC.CodeProjector.sum_sectorDistribution`
- `QECC.CodeProjector.sectorDistribution_eq_zero_of_not_mem`
- `MainTheory.GeneralColoredTheory.probability_sum_eq_one`

## main.tex:1276 — covered

Detecting the diagonal binary-monomial observable makes the J-moment equal across sectors. The observable is a linear combination of Z strings on subsets of J (binaryMonomial_eq_pauliExpansion), each of weight at most |J| < d0, and detection is closed under such combinations. So the diagonal (Z-string) KL equations suffice. detects_binaryMonomial_of_hasDistanceAtLeast, cited by the reader, assumes full HasDistanceAtLeast and does not by itself carry the 'diagonal only' qualifier.

- `QECC.CodeProjector.sectorMoment_eq_of_detects_binaryMonomial`
- `QECC.CodeProjector.binaryMonomial_eq_pauliExpansion`
- `QECC.CodeProjector.detects_sum`
- `QECC.CodeProjector.detects_smul`

## main.tex:1282 — covered

The momentsIndependent clause states equality of every moment of degree below d0 across all active sectors.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`
- `MainTheory.GeneralColoredTheory.all_binary_moments_eq`

## main.tex:1282 — covered

The moment equalities are derived from the KL hypothesis for any preserved code, so they cannot exclude a valid code. The phrase that they are not an independent ansatz is commentary.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`

## main.tex:1285 — gap

Asserts that when a sector has dimension above one, the moment equations do not capture all within-sector KL matrix constraints, i.e. they are strictly weaker than the exact KL completion. No declaration states this non-sufficiency or gives a witness. It is a standalone remark.


## main.tex:1289 — tracked

Previews the rank-two corollary (two labeled solution sets, one generator for the whole group). The sentence continues past the chunk boundary.


## main.tex:1290 — tracked

Previews the rank-two corollary: only two labeled fibers, and a single generator for the whole projective group. Its coverage is the corollary's.


## main.tex:1328 — covered

HasDistanceAtLeast d with d >= 2 implies HasDistanceAtLeast 2 directly from the definition, and that gives single-site Z detection (detectsSingleZ_of_hasDistanceAtLeast_two). The III.A theorem then supplies groupFinite and commutativity of the projective diagonal group.

- `QECC.CodeProjector.detectsSingleZ_of_hasDistanceAtLeast_two`
- `QECC.CodeProjector.finite_diagonal_logical_group_and_physical_representatives`

## main.tex:1332 — covered

A nonzero class has a reduced representative. On a rank-two code that representative has exactly two active sectors, each one-dimensional; these are the two eigenlines. phaseSectorMap restricts every code-preserving diagonal gate to an endomorphism of each sector, and its well-typedness is the invariance claim. On a one-dimensional sector it is a scalar (phaseSectorMap_eq_supportPhase_smul_id), which gives lambda_0 and lambda_1. Lean uses the reduced representative where the text speaks of a unitary representative; the proof only needs one.

- `QECC.CodeProjector.exists_reduced_representative`
- `QECC.CodeProjector.card_activeResidue_eq_two_of_projectiveClass_ne_zero`
- `QECC.CodeProjector.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero`
- `QECC.CodeProjector.phaseSectorMap`
- `QECC.CodeProjector.phaseSectorMap_eq_supportPhase_smul_id`

## main.tex:1342 — gap

The text claims that the specific eigenvalue-ratio map chi is well defined on G and injective. The proof of exists_injective_projectivePhaseRatio_of_two_sectors builds exactly this map, but its statement only says that some injective homomorphism from G to the circle exists. eigenvalueRatio_injective is an abstract version that assumes the individual eigenphases are already homomorphisms on G. This is a local step; the enclosing cyclicity result is carried.

- `QECC.CodeProjector.exists_injective_projectivePhaseRatio_of_two_sectors`
- `QECC.eigenvalueRatio_injective`

## main.tex:1346 — covered

Finite subgroups of the circle are cyclic (the instance unitAddCircle_isAddCyclic), and a finite group that embeds in the circle is cyclic. projectiveDiagonalGroup_isAddCyclic_of_rankTwo concludes cyclicity, and exists_projectiveDiagonalGroup_zmod_model gives an additive equivalence with ZMod m, where m >= 2 and m = Nat.card.

- `QECC.AddSubgroup.unitAddCircle_isAddCyclic`
- `QECC.isAddCyclic_of_finite_injective_unitAddCircle`
- `QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic_of_rankTwo`
- `QECC.CodeProjector.exists_projectiveDiagonalGroup_zmod_model`

## main.tex:1349 — covered

The general normal form applies to the generator. For a nonzero class on a rank-two code, Fintype.card (C.ActiveResidue a), which is the paper's ell, equals 2, and each active sector has finrank 1. The labels 0 and gamma are the anchor color and the other color in GeneralSSLPData.

- `QECC.CodeProjector.general_sslp_normal_form`
- `QECC.CodeProjector.card_activeResidue_eq_two_of_projectiveClass_ne_zero`
- `QECC.CodeProjector.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero`

## main.tex:1359 — covered

For a unit gamma in ZMod m with m | q, exists_unit_lift_mul_eq_one gives a unit u mod q whose reduction mod m times gamma is 1. Primitivity of gamma supplies the unit hypothesis via isUnit_of_addOrderOf_eq_modulus.

- `QECC.exists_unit_lift_mul_eq_one`
- `QECC.isUnit_of_addOrderOf_eq_modulus`

## main.tex:1368 — gap

The prime-by-prime choice of units mod p^{e_p} is not formalized; Lean gets the lift from surjectivity of the unit reduction map instead. This is a local step of the unit-lifting argument, whose conclusion is carried.

- `QECC.exists_unit_lift_inverse`

## main.tex:1370 — covered

The conclusion, a unit mod q that reduces to an inverse of gamma mod m, is stated by exists_unit_lift_mul_eq_one, reached by a different route (surjectivity of ZMod.unitsMap).

- `QECC.exists_unit_lift_mul_eq_one`
- `QECC.exists_unit_lift_inverse`

## main.tex:1374 — covered

Scaling the coefficient vector by a unit keeps its exact additive order q (unitScaleCoefficient_primitive), and the unit power still preserves the code. Exact order q of the residue vector gives physical order q and gcd one (orderOf_diagonalGate for the resulting reduced representative). The canonical record states both for the final vector.

- `QECC.unitScaleCoefficient_primitive`
- `QECC.CodeProjector.preserves_phaseHom_unitScaleCoefficient`
- `QECC.ReducedDiagonalRepresentative.orderOf_diagonalGate`
- `QECC.CodeProjector.HasRankTwoCanonicalNormalization`

## main.tex:1376 — gap

No Lean statement says that the class of the u-th power generates the code's projective group. It is not said for the transported canonical gate on the X-conjugated and permuted code either, and that transported group is never shown isomorphic to the original. QECC records only that the canonical class has exact order m. MainTheory.CoprimePowerRecovery.exists_pow_eq_self proves the abstract group fact (a group element is a power of any coprime power of itself), but nothing applies it to this class or to the u-th power. This is a local step; the corollary's statement is carried without it.

- `QECC.CodeProjector.HasRankTwoCanonicalNormalization`
- `MainTheory.CoprimePowerRecovery.exists_pow_eq_self`

## main.tex:1377 — covered

unitScaleCoefficient is coordinatewise multiplication by u. subsetSumFiber_unitScaleCoefficient shows that the fiber of u a at u b is the old fiber at b, so residues are multiplied by u.

- `QECC.unitScaleCoefficient`
- `QECC.subsetSumFiber_unitScaleCoefficient`

## main.tex:1382 — covered

exists_rankTwoCanonicalNormalization produces the sorted, gcd-one canonical vector, with one-dimensional transported sectors at residues 0 and q/m that exhaust the active residues. QECC applies the unit power before the X and permutation steps, which reaches the same endpoint. MainTheory's rank_two_sslp gives the orthonormal frame with zero amplitudes allowed.

- `QECC.CodeProjector.exists_rankTwoCanonicalNormalization`
- `MainTheory.PaperGeneralSSLP.rank_two_sslp`

## main.tex:1387 — nonmath

A remark about which normalizations are allowed. Lean does not need the interchange.


## main.tex:1389 — tracked

Introduces the eigenvalue display at 1391-1395 for the converse.


## main.tex:1396 — covered

The residue q/m has additive order m in ZMod q (addOrderOf_div). On the code built from the orthonormal KL pair (codeOfPair), the class of D(a;q) has order exactly m (orderOf_intrinsicClass_resolutionOfPair).

- `MainTheory.RankTwo.addOrderOf_div`
- `MainTheory.SSLPConverse.orderOf_intrinsicClass_resolutionOfPair`
- `MainTheory.SSLPConverse.codeOfPair`

## main.tex:1401 — covered

From any code with d >= 2 and a nonzero class, the general normal form derives the finite-order reduced representative (class_eq, physicalOrder), labeled fibers via primitive colors, and support of each sector in its fiber.

- `QECC.CodeProjector.general_sslp_normal_form`
- `QECC.CodeProjector.general_sslp_canonical_normal_form`

## main.tex:1405 — covered

sslp_sector_probabilities_and_moments shows that for any code satisfying the KL conditions below d0, the normalized sector diagonals are fiber-supported probability distributions whose binary moments of degree below d0 do not depend on the sector. A valid code therefore always passes the test. That theorem assumes the full KL system. sectorMoment_eq_of_detects_binaryMonomial derives the same moment equality from detection of the diagonal monomial operator alone, which the diagonal (Z-type) KL equations supply, so the claim that these are consequences of the diagonal equations is also carried.

- `QECC.CodeProjector.sslp_sector_probabilities_and_moments`
- `QECC.CodeProjector.sectorMoment_eq_of_detects_binaryMonomial`

## main.tex:1407 — gap

This claims the moment test is not sufficient, which needs a witness: a feasible moment system with no code. No declaration in QECC or MainTheory states LP feasibility and non-existence together. The six-qubit development has the ingredients: 66 moment orbits, MainTheory.SSLPOrbitLevels.card_realizationOrbit (15 realized), realization_or_empty, and MainTheory.CubeAction.DegreeTwoFeasible. But no theorem states DegreeTwoFeasible for an orbit whose completion set is empty. It is a standalone claim outside any proof, not a local step, so the rubric gives medium rather than low.


## main.tex:1408 — covered

Distance is defined as the full Pauli KL system, which makes the KL layer necessary. The direct-sum converse makes the fiber-supported data plus that system sufficient for a code with the stated order and distance.

- `QECC.CodeProjector.HasDistanceAtLeast`
- `QECC.general_sslp_directSum_converse`
- `MainTheory.GeneralColoredConverse.ColoredFrame.sslp_converse`

## main.tex:1420 — tracked

Completes the sentence of the boxed display (an exact staged normal form at arbitrary K, with the rank-two corollary as the two-fiber instance).


## main.tex:1424 — tracked

Roadmap: so far q is only known to be finite and code dependent, and III.C supplies a uniform cutoff. This previews the general physical-order bound.


## main.tex:1427 — tracked

Restates the minimum-order gap example (q_min can exceed m) to argue that searching only q = m is incomplete; the m | q part restates eq:K2-bound. Coverage is that entry's. An earlier review reports that the seven-qubit example is not formalized.


## main.tex:1431 — nonmath

Section heading and label only.


## main.tex:1434 — nonmath

Roadmap: the finite search still needs a code-independent cutoff on q, and this subsection derives one.


## main.tex:1436 — tracked

Previews the method of the general bound: rational replacement through common first moments (lem:common-mean-rational-replacement), then binary denominator control.


## main.tex:1438 — tracked

Previews the distance-three, K=2 refinement stated later in III.C (label at line 1902, outside this chunk).


## main.tex:1441 — tracked

Previews the common-barycenter lemma, including sectors of dimension above one.


## main.tex:1445 — covered

The setup presupposes that the gate restricted to the code splits into mutually orthogonal eigenspaces with distinct eigenvalues, ranks k_alpha and projectors Pi_alpha. GeneralSpectral builds exactly this for any real preserving theta and any code shape: an orthogonal family of eigenspaces of the restricted gate and a subordinate orthonormal basis.

- `MainTheory.GeneralSpectral.spectralExtractionPrinciple`
- `MainTheory.GeneralSpectral.logicalSectorResolution`
- `MainTheory.GeneralSpectral.sectorOrthogonalFamily`

## main.tex:1453 — covered

Every sector support is nonempty, proved from positive rank and unit total mass: for real theta in MainTheory, for modular gates in QECC.

- `MainTheory.PhaseSectorFull.sectorSupport_nonempty`
- `QECC.CodeProjector.actualSectorSupport_nonempty`

## main.tex:1454 — tracked

Lead-in to the congruence display, through the eigen-relation of Pi_alpha. The cited proof of thm:general-sslp-normal-form (lines 1110 onward in 20260929) no longer contains a diagonal-entry argument: it defines sectors as fibre intersections and treats only modular gates, so the cross-reference is stale. The congruence itself is carried by PhaseSectorFull.phase_congruence.


## main.tex:1461 — covered

Distinct sectors have disjoint supports: in MainTheory for any real-theta decomposition with distinct sector eigenvalues, in QECC for modular sectors.

- `MainTheory.PhaseSectorFull.sectorSupport_disjoint`
- `QECC.CodeProjector.actualSectorSupport_disjoint`

## main.tex:1461 — gap

For real theta, MainTheory states support containment only for the orthonormal sector vectors. QECC states it for every vector of a sector, but only for modular gates. No declaration states it for an arbitrary vector of a real-theta eigenspace. The fact feeds the hypothesis of lem:common-mean-rational-replacement in the later proof of thm:colored-finite-lift, but that theorem is carried by MainTheory through frame vectors, and the extension is linear.

- `MainTheory.FiniteLift.vec_ne_zero_mem_sectorSupport`
- `QECC.CodeProjector.phaseSector_vanishes_off_actualSupport`

## main.tex:1483 — covered

Positivity on the support holds by definition. MainTheory's sectorSupport is defined as the positivity locus, and the QECC lemma states positivity as its first clause.

- `QECC.CodeProjector.phaseSectors_positive_probability_commonFirstMoments`
- `MainTheory.PhaseSectorFull.sectorSupport`

## main.tex:1488 — tracked

Restates the equivalence between Z_j detection and number-operator detection, which is the content of eq:Nj-detection (line 664, outside this chunk); its coverage is that entry's.


## main.tex:1488 — gap

The operator identity Pi_alpha N_j Pi_alpha = mu_j Pi_alpha, derived from Pi_alpha lying under P, is not stated. QECC proves only its traced form, and only for modular sectors. This is a local step of the proof of lem:phase-sectors, which MainTheory carries by another route (per-vector occupations through sectorMean_eq_klScalar).

- `QECC.CodeProjector.normalizedSectorTrace_eq_detectedScalar`

## main.tex:1494 — tracked

The last step of the common-mean proof, dividing the trace identity by the sector rank.


## main.tex:1497 — tracked

Motivating remark: irrational sector probabilities do not obstruct rational replacement, because only the shared barycenter is used. It previews the replacement lemma.


## main.tex:1534 — tracked

Restates the difference hypothesis as constancy of Delta.x on each support. The two forms agree by additivity of the dot product, which the ledger reads through the linear map QECC.realSupportWeightLinear at displaymath@1516.


## main.tex:1535 — tracked

Lead-in to the averaging computation.


## main.tex:1544 — tracked

Conclusion of the averaging display: every sector constant equals Delta.mu, so none depends on alpha.


## main.tex:1544 — tracked

Lead-in to the vector identity on each E_alpha: the ratio of the two diagonal gates is constant on the support of each vector.


## main.tex:1551 — tracked

Assembles the per-sector identity into the lemma's restricted-gate conclusion.


## main.tex:1555 — covered

The hypotheses confirm that neither rational probabilities nor weight-two Knill-Laflamme equations are needed. colored_finite_lift_of_zDetects assumes only ZDetectsFrame, with d free. code_action assumes only ZDetects of the sectors. The QECC replacement theorem assumes common first moments, plus modular preservation and no second moments. The remark that second moments enter later is a roadmap.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.WithinSectorCodeAction.code_action`
- `QECC.CodeProjector.rationalVectorPhase_same_projectiveClass_of_sameSectorEquations_of_commonFirstMoments`

## main.tex:1559 — tracked

Previews the binary formulation used in the theorem's proof: n physical and ell-1 auxiliary coordinates, then an invertible binary pivot of size at most n+ell-1.


## main.tex:1567 — covered

In both libraries a binary matrix has zero-one integer entries. Nonsingularity is a nonzero integer determinant, not invertibility modulo two. For the pivot systems used, realRank_eq_size equates real rank with the rational rank recorded in BinaryPivotSolution.size_eq_rank.

- `QECC.NonsingularBinaryMatrix`
- `MainTheory.BinaryBeta.IsZeroOne`
- `QECC.BinaryPivotSolution.realRank_eq_size`

## main.tex:1569 — tracked

Lead-in to the Smith normal form definition.


## main.tex:1577 — tracked

Completes the SNF definition: unimodular U and V, and the d_i named as invariant factors. Only d_s is shown witness-independent in Lean, which suffices for every later use.


## main.tex:1578 — tracked

Previews that the last factor clears solution denominators.


## main.tex:1580 — gap

The sentence identifies the last Smith factor with the exponent of Z^s/CZ^s. QECC proves that cokernel finite and defines finalSmithInvariant as its exponent, and MainTheory proves that every Smith witness's last factor equals inverseDenominator. No declaration in QECC, MainTheory, SS, SixQubit or Mathlib relates the cokernel exponent to either. The two libraries do not import each other, and QECC has no minimality lemma for its exponent among clearing multipliers. In Mathlib, Submodule.quotientEquivPiZMod uses abstract Smith-basis coefficients, not a given matrix's factors. Both divisibilities could be assembled from the two clearing lemmas with Mathlib's nonsingular inverse, cast injectivity and quotient reasoning, but none of this is stated. Without the identity, QECC's finalSmithInvariant and smithBeta are not the manuscript's d_s(C) and beta, and every ledger clause carried only through them is uncarried.

- `QECC.NonsingularBinaryMatrix.finalSmithInvariant`
- `QECC.NonsingularBinaryMatrix.cokernelFinite`
- `QECC.smithBeta`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`

## main.tex:1581 — nonmath

Signpost to the next lemma.


## main.tex:1595 — tracked

Lead-in to the Smith-form expression for the inverse.


## main.tex:1599 — covered

For every Smith witness, the last factor times each inverse entry is integral, so it clears C^{-1}h for every integral h.

- `MainTheory.SharpClearing.SmithWitness.lastFactor_mul_inverse_entry`
- `MainTheory.SharpClearing.SmithWitness.lastFactor_universallyClears`

## main.tex:1603 — tracked

Lead-in to the beta definition.


## main.tex:1611 — covered

inverseDenominator C clears every integral system for C (inverseDenominator_universallyClears). By universallyClears_iff_dvd, every other clearing multiplier is a multiple of it. betaBound_betaOf bounds it by betaOf nu for every nonsingular zero-one matrix of size 1..nu. For nu >= 1, betaOf nu = beta_nu: the witness bridge (nonempty_smithWitness_of_det, inverseDenominator_eq_smithLastFactor) makes beta_nu a BetaExact certificate, and betaOf_eq_of_exact applies. QECC's finalSmithInvariant_le_smithBeta instead bounds the cokernel exponent, which no declaration identifies with d_s(C).

- `MainTheory.SharpClearing.universallyClears_iff_dvd`
- `MainTheory.SharpClearing.inverseDenominator_universallyClears`
- `MainTheory.BetaExists.betaBound_betaOf`
- `MainTheory.BinaryBeta.BetaExact`
- `MainTheory.BetaExactValue.betaOf_eq_of_exact`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`
- `QECC.finalSmithInvariant_le_smithBeta`

## main.tex:1615 — nonmath

Signpost to the theorem.


## main.tex:1650 — tracked

Recalls the supports T_alpha and their common first moment from the earlier lemma; coverage is that lemma's.


## main.tex:1654 — tracked

Announces the normalization and chooses a point x0 of the first support for the XOR relabelling shown in the display.


## main.tex:1659 — tracked

Says the relabelling is conjugation of code and gate by X^{x0}, introducing the displayed sign rule; carried by QECC.reindexOperator_xor_diagonalGate, QECC.CodeProjector.reindex and MainTheory.RealXNormalization.gate_shift.


## main.tex:1665 — covered

After the relabelling the real-gate sector data is shiftedSectors D x0, whose distributions are the originals read at x xor x0 (shifted_probability). shifted_zDetects transports Z detection, and exists_common_sector_mean applied to the shifted decomposition gives a common first moment for all relabelled sector distributions. The manuscript's affine-image mechanism is not formalized, but its conclusion is.

- `MainTheory.NormalizedRealSectors.shifted_probability`
- `MainTheory.NormalizedRealSectors.shifted_zDetects`
- `MainTheory.PhaseSectorFull.exists_common_sector_mean`

## main.tex:1668 — covered

detectsNumberOps_reindex_xor proves that number-operator detection survives XOR reindexing of the code projector (mu_j becomes 1 - mu_j on flipped coordinates). shifted_zDetects proves Z detection is preserved for the shifted real-gate decomposition.

- `QECC.CodeProjector.detectsNumberOps_reindex_xor`
- `MainTheory.NormalizedRealSectors.shifted_zDetects`

## main.tex:1668 — tracked

Drops the scalar and gives the reason for the normalized first-sector display; coverage is that entry's, which is covered by MainTheory.NormalizedRealSectors.zero_mem_shifted_support and shifted_reference_phase_zero.


## main.tex:1678 — tracked

Introduces the lifted phase equations displayed next.


## main.tex:1687 — tracked

States that the right sides are integers (part of the lifted-equation entry) and introduces the vector u of the next display.


## main.tex:1691 — tracked

Says the lifted equations form the consistent integral system displayed next.


## main.tex:1697 — tracked

The binary and column-count clauses of the Ru = h entry (partial).


## main.tex:1699 — gap

The prose defines s as the rational rank and says it equals the real rank. Both libraries work with Q-rank only and no declaration (nor a Mathlib matrix-rank field-extension lemma in the tree) states that the ranks agree. This is a side remark in a proof whose result is carried another way.


## main.tex:1699 — tracked

Justifies s >= 1 by the auxiliary-column row of the second sector; coverage is that entry's (partial), and both libraries use a different argument.


## main.tex:1707 — tracked

Describes the selection of independent rows and columns for the pivot minor.


## main.tex:1713 — tracked

Defines h_I and the zero extension of u' that the pivot equation solves.


## main.tex:1720 — covered

The pivot solution in QECC.BinaryPivotSolution and MainTheory's binarySolution are Q-valued vectors solving the integral pivot system.

- `QECC.exists_binaryPivotSolution`
- `MainTheory.BinaryPivotLift.binarySolution_solves`

## main.tex:1722 — tracked

Introduces the row-combination display.


## main.tex:1727 — tracked

Introduces the consistency calculation for h_r.


## main.tex:1733 — tracked

Introduces the same calculation for u'.


## main.tex:1740 — covered

The solves field of QECC's pivot solution, in the same witness as the selected minor, states that the zero-extended solution solves the full system for any consistent zero-one system. MainTheory's fullSolution_solves states it for every pivot of the given gate's sign-twisted system.

- `QECC.exists_binaryPivotSolution`
- `MainTheory.FiniteLift.PivotData.fullSolution_solves`

## main.tex:1742 — tracked

Invokes denominator clearing for the pivot equation.


## main.tex:1747 — tracked

Notes that the coordinates off J vanish, which extends integrality to all of u'.


## main.tex:1752 — tracked

Defines theta', Delta, phi'_alpha and gamma_alpha and announces the subtraction displayed next (partial).


## main.tex:1761 — tracked

Introduces the pairwise within-sector constancy display.


## main.tex:1766 — tracked

Invokes the common-mean replacement lemma to get the common phase shift.


## main.tex:1772 — tracked

Connective to the rational replacement display.


## main.tex:1778 — covered

common_phase_shift holds at every support point; zero_mem_shifted_support puts the zero string in the normalized first support, where the angle is 0, so Delta.mu = 0. code_action with this zero common shift gives equality of D(theta') and D(theta) on the code, hence preservation and the same logical action.

- `MainTheory.WithinSectorRationalization.common_phase_shift`
- `MainTheory.WithinSectorCodeAction.code_action`
- `MainTheory.NormalizedRealSectors.zero_mem_shifted_support`

## main.tex:1783 — tracked

Defines q as the least clearing integer and gives the reason for q | d_s(C).


## main.tex:1789 — tracked

Defines a~_j and the residues a_j used in the display.


## main.tex:1794 — covered

For R with R.phase = theta', the diagonal gate has multiplicative order R.q, the additive order of theta', which is the least clearing integer.

- `QECC.ReducedDiagonalRepresentative.orderOf_diagonalGate`
- `QECC.exists_reducedDiagonalRepresentative`

## main.tex:1795 — covered

commonGCD_eq_one gives gcd(q, canonical numerators) = 1. eq_one_of_dvd_lcmDen_of_dvd_liftNum gives the same conclusion by the manuscript's minimality route on the integer numerators.

- `QECC.ReducedDiagonalRepresentative.commonGCD_eq_one`
- `MainTheory.Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum`

## main.tex:1802 — covered

Finishes the gcd argument by contradicting minimality; the conclusion is the statement of these declarations.

- `MainTheory.Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum`
- `QECC.ReducedDiagonalRepresentative.commonGCD_eq_one`

## main.tex:1804 — covered

For any reduced representative in the class U, addOrderOf U divides its physical order q.

- `QECC.CodeProjector.projectiveOrder_dvd_of_mem_physicalRepresentativeOrders`

## main.tex:1807 — covered

QECC's reduced representative carries q >= 2 and a primitive residue vector, and commonGCD_eq_one gives the gcd condition; exists_reduced_representative_of_nsmul_eq_zero produces it in the class with m | q. MainTheory states 2 <= m and 2 <= q for the supplied gate's lift.

- `QECC.ReducedDiagonalRepresentative`
- `QECC.ReducedDiagonalRepresentative.commonGCD_eq_one`
- `QECC.CodeProjector.exists_reduced_representative_of_nsmul_eq_zero`
- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`

## main.tex:1810 — covered

Transporting a replacement back through the sign change preserves the projective class. Sign changes keep the common denominator (xorPhase_rationalPhase) and the exact additive and physical orders (addOrderOf_xorPhase, orderOf_diagonalGate_xorPhase); xorPhase_phaseHom expresses them on residue vectors, so primitivity is kept.

- `QECC.CodeProjector.exists_preserves_projectiveClass_eq_of_xor_replacement`
- `QECC.addOrderOf_xorPhase`
- `QECC.orderOf_diagonalGate_xorPhase`
- `QECC.xorPhase_rationalPhase`
- `QECC.xorPhase_phaseHom`

## main.tex:1817 — tracked

Connective to the final inequality chain.


## main.tex:1823 — tracked

Justifies each link of the chain; coverage is that entry's (partial, because of the ell and beta identifications).


## main.tex:1825 — tracked

Derives the minimum-order bound of the theorem statement. QECC carries it as minimalPhysicalOrder_le_sectorBeta and minimalPhysicalOrder_le_rankBeta in GeneralPhysicalOrderBoundConclusion, with ell taken from the internal representative.


## main.tex:1830 — nonmath

Signposting sentence that the general argument is complete.


## main.tex:1830 — covered

Distance at least two gives single-site Z detection, in QECC for a code projector and in MainTheory for an exact code linked to a sector decomposition.

- `QECC.CodeProjector.detectsSingleZ_of_hasDistanceAtLeast_two`
- `MainTheory.FiniteLift.ExactCodeSectorLink.zDetects`

## main.tex:1831 — covered

Distance at least two gives the detection hypothesis (detectsSingleZ_of_hasDistanceAtLeast_two, then detectsNumberOps_of_detectsSingleZ). Every nonzero class then has a reduced representative of order at most smithBeta(n+K-1), and the minimum order obeys the same bound. That constant depends only on n and K, so finiteness needs no identification of smithBeta with beta. On the MainTheory side, zDetectsFrame_of_hasDistance supplies the Z-detection hypothesis from d >= 2, and the colored lift gives the manuscript's own bound betaOf(n+K-1) = beta_{n+K-1}. The mention of the SSLP normal form is roadmap.

- `QECC.CodeProjector.general_physicalOrder_bound`
- `QECC.CodeProjector.detectsSingleZ_of_hasDistanceAtLeast_two`
- `QECC.CodeProjector.detectsNumberOps_of_detectsSingleZ`
- `MainTheory.ZDetection.zDetectsFrame_of_hasDistance`
- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`

## main.tex:1835 — nonmath

Attributes the tabulated values to tables in a cited reference; the values themselves are the eq:small-beta entry.


## main.tex:1850 — covered

For any real gate with a projectively nontrivial action, two_le_sectorCount_of_resolution gives at least two sectors and sectorCount_le at most K, with no detection hypothesis, so ell = 2 when K = 2. colored_finite_lift_of_zDetects packages the same bounds for the supplied gate, and QECC proves them for every modular representative.

- `MainTheory.SectionTwoGeneral.two_le_sectorCount_of_resolution`
- `MainTheory.SectionTwoGeneral.sectorCount_le`
- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `QECC.CodeProjector.two_le_card_activeResidue_of_projectiveClass_ne_zero`
- `QECC.CodeProjector.card_activeResidue_le`

## main.tex:1850 — tracked

Introduces the K = 2 specialization displayed next.


## main.tex:1859 — covered

At n = 6 and K = 2, the coloured lift has order at most betaOf(n + K - 1) = betaOf 7, and betaOf_eq_of_exact applied to betaSevenExact gives betaOf 7 = 18; this uses Z detection only. qMin_le_eighteen states the bound directly for six-qubit rank-two codes of distance at least two. QECC alone cannot give 18, because smithBeta 7 is not evaluated.

- `MainTheory.PaperColoredFiniteLift.colored_finite_lift_of_zDetects`
- `MainTheory.BetaExactValue.betaOf_eq_of_exact`
- `MainTheory.BinaryBetaSeven.betaSevenExact`
- `MainTheory.SixQubitDistanceTwoBound.qMin_le_eighteen`

## main.tex:1859 — tracked

Previews the distance-three improvement to q <= 9 and its equal-affine-span mechanism (lem:positive-affine-moments), proved in the next part of the section.


## main.tex:1864 — tracked

Introduces affine-span notation and the base-point formula.


## main.tex:1869 — tracked

Independence of the base point, part of the affine-span entry; Mathlib's affineSpan has no base point.


## main.tex:1889 — gap

Proof step: with strictly positive weights the weighted mean square of an affine function is zero exactly when the function vanishes on the support, so under the hypothesis vanishing on T_0 and on T_1 are equivalent. QECC proves this only in a private lemma for zero-one supports, used inside the cited public theorem. MainTheory.Covariance.quad_eq_zero_iff, read with quad_eq_sum_sq, states the positivity half for any finite weighted point family in R^n and affine functions written as w·(x − μ), which covers every affine function except nonzero constants. The transfer between the two supports under the affine mean-square hypothesis is not stated publicly. The enclosing lemma is carried for zero-one supports.

- `QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation`
- `MainTheory.Covariance.quad_eq_zero_iff`
- `MainTheory.Covariance.quad_eq_sum_sq`

## main.tex:1893 — gap

A step in the lemma's proof: the affine hull of a set equals the intersection of the zero sets of all affine functions vanishing on it, so the two spans coincide. The Lean proof of the zero-one case uses an equivalent dual-annihilator argument internally, but no project declaration states this characterization, and the R^n case is not formalized.

- `QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation`

## main.tex:1897 — tracked

Announces that applying the affine-span identity to the phase equations gives the sharper rank-two bound. This previews the corollary, and its coverage is that entry's (partial).


## main.tex:1944 — nonmath

Opens the proof and introduces the display that defines p_k.


## main.tex:1949 — gap

Because Π_k has rank one, its diagonal on T_k is a strictly positive distribution of unit mass. For the given real gate, MainTheory states nonnegativity and unit mass of the rank-normalized projector diagonal of every eigen-sector, and exactly two sectors for a rank-two code with nontrivial action; it does not state that each of those sectors has rank one, which is what makes the normalized weight equal p_k. QECC states the rank-one fact and unit mass, but for the sectors of a modular representative. Strict positivity on T_k holds by definition. The enclosing corollary is carried, for an internally chosen representative, by distanceThree_physicalOrder_bound.

- `MainTheory.PhaseSectorFull.sectorProbability_nonneg`
- `MainTheory.PhaseSectorFull.sectorProbability_sum_eq_one`
- `MainTheory.SectionTwoGeneral.sectorCount_eq_two`
- `QECC.CodeProjector.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero`
- `QECC.CodeProjector.sum_sectorDistribution`

## main.tex:1950 — gap

Low-weight diagonal KL forces p_0 and p_1 to share their moments of orders one and two. MainTheory.GeneralSectorMoments.sector_moment_eq states equal binary moments below d for the rank-normalized projector diagonals of any orthonormal frame of a distance-d code grouped into positive-rank sectors, and wordMoment_eq states it for the squared amplitudes of any such frame; both are generic and so apply to the given gate's eigen-sectors and eigenvectors. QECC states it for the sectors of a modular representative. No declaration states it for the unnormalized p_k of the given gate, which agrees with the normalized weight only once its sectors are known to be one-dimensional.

- `MainTheory.GeneralSectorMoments.sector_moment_eq`
- `MainTheory.GeneralSectorMoments.wordMoment_eq`
- `QECC.CodeProjector.sectorMoment_eq_of_hasDistanceAtLeast`
- `MainTheory.CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame`

## main.tex:1952 — covered

Expanding the square with x_j^2 = x_j shows that equal mass and equal first and second moments give equal affine mean squares for all c and w. QECC.affineSquareExpectation_eq_of_moments states this implication for arbitrary real weight functions on bit strings, independent of the gate, so it applies to any zero-one supports.

- `QECC.affineSquareExpectation_eq_of_moments`
- `QECC.CodeProjector.binaryMonomialValue_pair`

## main.tex:1954 — covered

Applies the lemma to zero-one supports. QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation states that case for any two nonnegative weight functions of unit mass on bit strings.

- `QECC.affineSpan_positiveSupportImage_eq_of_affineSquareExpectation`

## main.tex:1957 — covered

The local bit flip acts on basis strings as XOR with x0, which is the restriction of the affine involution. QECC.xorRealAffineEquiv_bitVector proves that the real affine map agrees with XOR on embedded bit strings.

- `QECC.xorRealAffineEquiv`
- `QECC.xorRealAffineEquiv_bitVector`

## main.tex:1966 — covered

Stated exactly, for every t and x, by QECC.xorRealAffineEquiv_bitVector.

- `QECC.xorRealAffineEquiv_bitVector`

## main.tex:1967 — covered

The linear part of F_{x0} is the diagonal sign change: the linear field of QECC.xorRealAffineEquiv is QECC.xorRealLinearEquiv, which negates the coordinates where x0 is set. For any set S and any map v ↦ a + L v with L an invertible linear map, MainTheory.RealSupportAffineRank.vectorSpan_image_affine transports the direction of the affine span by L, and finrank_direction_image_affine shows the affine dimension is unchanged. MainTheory.RealSupportAffineRank.bitPoint_bxor shows that XOR with x0 on embedded bit strings has exactly this form with L the sign change. These statements are general in S, so they carry the assertion for any supports, including the given gate's.

- `QECC.xorRealLinearEquiv`
- `QECC.xorRealAffineEquiv`
- `MainTheory.RealSupportAffineRank.vectorSpan_image_affine`
- `MainTheory.RealSupportAffineRank.finrank_direction_image_affine`
- `MainTheory.RealSupportAffineRank.bitPoint_bxor`

## main.tex:1968 — gap

After conjugating by X^{x0}, 0^n lies in T_0, the anchor eigenvalue is 1, and the common span is a linear subspace of dimension r. Lean proves the analogues for a modular gate: zero lies in the transported anchor support, the anchor residue is zero, preservation and distance carry over, and the affine direction equals the row span. It does not prove them for an arbitrary real D(θ).

- `QECC.CodeProjector.zero_mem_transported_actualSectorSupport`
- `QECC.CodeProjector.transported_anchor_val_eq_zero`
- `QECC.CodeProjector.reindex_xor_preserves_phaseHom`
- `QECC.CodeProjector.hasDistanceAtLeast_reindex_xor`
- `QECC.CodeProjector.direction_actualSectorAffineSpan_eq_rowSpan`

## main.tex:1974 — covered

For any exact code and any code-preserving real phase vector θ, MainTheory.PaperGeneralSSLP.phase_sector_support states that the projector-diagonal supports of the eigen-sectors of D(θ) (MainTheory.PhaseSectorFull.sectorSupport over MainTheory.SectionTwoGeneral.resolutionOf) are nonempty and pairwise disjoint, and that each supported string satisfies its sector's phase congruence; disjointness comes from the distinct eigenvalues, as in the text. The statement holds for any code and gate, so it covers the normalized pair. QECC's actualSectorSupport_nonempty and actualSectorSupport_disjoint are the analogues for a modular representative.

- `MainTheory.PaperGeneralSSLP.phase_sector_support`
- `MainTheory.PhaseSectorFull.phase_congruence`
- `MainTheory.SectionTwoGeneral.resolutionOf`

## main.tex:1975 — gap

If r were zero both supports would collapse to one point, contradicting disjointness, so 1 ≤ r ≤ n. The upper bound is generic: MainTheory.RealSupportAffineRank.supportAffineRank_le bounds the support affine rank of any state by n. The lower bound is proved by the same disjointness argument only for the modular representative's sectors (exists_ne_zero_mem_actualSectorSupport_of_affineSpan_eq, normalizedActualSupportDimension_pos), not for the given gate's r.

- `QECC.CodeProjector.exists_ne_zero_mem_actualSectorSupport_of_affineSpan_eq`
- `QECC.CodeProjector.normalizedActualSupportDimension_pos`
- `QECC.CodeProjector.normalizedActualSupportDimension_le`
- `MainTheory.RealSupportAffineRank.supportAffineRank_le`

## main.tex:1980 — gap

With 0 in T_0 the support spans V, a basis of support strings gives B, and its real and rational ranks are r. MainTheory.SixQubitSemanticEntrance.supportedBitBasis extracts, for the nonzero support of any state, real-independent supported bit strings with the same real span, and SupportedBitBasis.rank_eq_supportAffineRank gives their number as the support's affine dimension when the zero string is supported; these are generic, so they apply to a normalized eigenvector of the given gate. QECC.BinaryPivotSolution.realRank_eq_size equates real and rational rank for an integral matrix with a pivot solution. The subspace identity span(T_0) = V is stated only for modular sector supports, and no declaration packages the step for the given gate's projector-diagonal T_0.

- `MainTheory.SixQubitSemanticEntrance.supportedBitBasis`
- `MainTheory.RealSupportAffineRank.SupportedBitBasis.rank_eq_supportAffineRank`
- `QECC.BinaryPivotSolution.realRank_eq_size`
- `QECC.CodeProjector.direction_actualSectorAffineSpan_eq_rowSpan`

## main.tex:1984 — covered

QECC.exists_binaryPivotSolution applies to any zero-one integer matrix with a consistent right-hand side (for B take the zero right-hand side) and returns a QECC.BinaryPivotSolution whose size is the rational rank, with selected rows, selected columns and a nonzero-determinant minor on them. For B, whose r rows are independent, the size is r, every row is selected, and the selected columns form a set I with det B[:, I] ≠ 0 up to a row reordering. The statement is generic in the matrix, so it covers any prescribed basis matrix, including one built from the given gate's support.

- `QECC.exists_binaryPivotSolution`
- `QECC.BinaryPivotSolution`

## main.tex:1989 — nonmath

A convention remark: nonsingularity is meant over Q or R, not modulo two. QECC.NonsingularBinaryMatrix follows it by requiring a nonzero integer determinant.


## main.tex:1992 — gap

Each basis string has trivial phase under the normalized gate, so h = Bθ is an integer vector. Lean states that the lifted phase of a modular gate solves the anchor support system with integral right-hand side when the anchor residue is zero. It does not state this for the given real θ.

- `QECC.CodeProjector.phaseLift_solves_anchorActualSupportSystem`

## main.tex:2001 — gap

Bθ' = h = Bθ, so θ' − θ kills every row of B and hence V. In Lean the pivot solution solves every row of the anchor support matrix (field solves) and agrees with the lifted phase on the whole anchor support. Both facts are for the modular source representative, not the given gate.

- `QECC.BinaryPivotSolution`
- `QECC.CodeProjector.anchorBinaryPivotSolution_agrees_on_anchor`

## main.tex:2007 — gap

The two gates agree on both supports, and eigenspace vectors are supported on T_k, so their restrictions to the code coincide, and D(theta') preserves the code with the same projective action. For any assembled FreshSparsePhase on two states, FreshSparsePhase.realGate_eq_left and realGate_eq_right give equality of the two real diagonal actions on each state. QECC proves the analogue for the modular source representative: constancy on all actual sector supports gives a scalar action, and the rational replacement lies in the same projective class. No declaration assembles a fresh phase from the given gate's normalized eigenvectors and angles, or passes from equality on the two eigenvectors to the same restriction and projective action on the code.

- `MainTheory.D3FreshSparseAssembly.FreshSparsePhase.realGate_eq_left`
- `MainTheory.D3FreshSparseAssembly.FreshSparsePhase.realGate_eq_right`
- `QECC.CodeProjector.actsAsScalar_of_constant_on_actualSectorSupports`
- `QECC.CodeProjector.phaseSector_vanishes_off_actualSupport`
- `QECC.CodeProjector.NormalizedDistanceThreePhaseSystem.exists_smithBoundedPhysicalRepresentative`

## main.tex:2013 — covered

Instantiate D3SparseRationalization.Data at the manuscript's (B, I, h), with a Smith witness W of its zero-one minor from nonempty_smithWitness_of_det. selectedSolution_smith_integral makes W.lastFactor times theta'_I integral. Data.lcmDen_full_dvd_inverseDenominator gives lcmDen theta' | inverseDenominator C, where theta' is the zero-extended solution and lcmDen theta' is Data.order; inverseDenominator_eq_smithLastFactor rewrites the right side to W.lastFactor, the same for every witness, that is d_r(C). For each coordinate, lcmDen_clears and Nat.dvd_trans give (theta'_j).den | d_r(C), and clears_iff with lastFactor_pos makes d_r(C) theta'_j an integer. QECC's lemma states the same for the integer-cokernel exponent, which no declaration identifies with d_r(C).

- `MainTheory.D3SparseRationalization.Data`
- `MainTheory.SparseSmithDisplays.selectedSolution_smith_integral`
- `MainTheory.D3SparseRationalization.Data.lcmDen_full_dvd_inverseDenominator`
- `MainTheory.D3SparseRationalization.Data.order`
- `MainTheory.Denominator.lcmDen_clears`
- `MainTheory.Denominator.clears_iff`
- `MainTheory.SharpClearing.SmithWitness.lastFactor_pos`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `MainTheory.PivotSmithNormalForm.nonempty_smithWitness_of_det`
- `QECC.BinaryPivotSolution.exists_integral_finalSmithInvariant_smul_solution`

## main.tex:2015 — covered

The least denominator q of θ' divides d_r(C), and reduction gives exact order q with the gcd-one condition, m | q and m ≥ 2. QECC.exists_reducedDiagonalRepresentative gives a reduced representative whose phase is exactly θ', and its q is the additive order of that phase (addOrderOf_phase), i.e. the least denominator. commonGCD_eq_one gives the gcd condition. QECC.CodeProjector.exists_reduced_representative_of_nsmul_eq_zero gives m | q, q | d and exact physical order for any preserving phase killed by d in a nonzero class. q ≥ 2 is a field of the representative, and m ≥ 2 follows from U ≠ 0.

- `QECC.exists_reducedDiagonalRepresentative`
- `QECC.ReducedDiagonalRepresentative.addOrderOf_phase`
- `QECC.ReducedDiagonalRepresentative.commonGCD_eq_one`
- `QECC.CodeProjector.exists_reduced_representative_of_nsmul_eq_zero`

## main.tex:2029 — tracked

Closes the derivation of eq:d3-full-bound; its coverage is that entry's (partial).


## main.tex:2031 — covered

Undoing the normalization keeps the affine dimension, the exact physical order and the projective action. Sign changes of a modular coefficient vector keep its additive order and the exact order of the physical gate (QECC.addOrderOf_xorCoefficient, QECC.orderOf_diagonalGate_xorCoefficient). Transporting a replacement back from the X-normalized code recovers the original projective class (QECC.CodeProjector.exists_preserves_projectiveClass_eq_of_xor_replacement). XOR preserves the affine dimension of sector supports (QECC.CodeProjector.actualSectorAffineDimension_xor) and of the nonzero support of any state (MainTheory.RealSupportAffineRank.supportAffineRank_bxor). Each statement is generic in the code and phase; the Lean proof of the corollary orders the steps differently (transport, then reduce), but the step itself is carried.

- `QECC.orderOf_diagonalGate_xorCoefficient`
- `QECC.addOrderOf_xorCoefficient`
- `QECC.CodeProjector.exists_preserves_projectiveClass_eq_of_xor_replacement`
- `QECC.CodeProjector.actualSectorAffineDimension_xor`
- `MainTheory.RealSupportAffineRank.supportAffineRank_bxor`

## main.tex:2034 — covered

Any reduced representative of the class bounds q_min. The resulting eq:d3-qmin, and its dependence on r, are covered by that entry.

- `QECC.CodeProjector.minimalPhysicalOrder_le`

## main.tex:2039 — tracked

Introduces the finite-enumeration cutoff; its coverage is that entry's (partial). The attribution is inaccurate: neither cited corollary supplies the β_{n+1} branch for d_0 = 2, since one has no bound on q and the other assumes d ≥ 3. That branch comes from thm:colored-finite-lift with K = 2 (eq:K2-q-bound-summary), carried in Lean by rankTwo_distanceTwo_physicalOrder_cutoff.

- `QECC.CodeProjector.rankTwo_distanceTwo_physicalOrder_cutoff`

## main.tex:2053 — tracked

The requirement that a be in canonical form is part of the cutoff assertion. That entry notes it is not assembled with the cutoff in one declaration.


## main.tex:2053 — covered

Take any reduced preserving representative of a nonzero class of order m (2 ≤ m, m | q). The unit-power, local-X and permutation normalization then gives canonical data with the same q: coefficients of additive order q, gcd one, and exact physical order q on the transported code.

- `QECC.CodeProjector.exists_rankTwoCanonicalNormalization`

## main.tex:2056 — nonmath

Describes the search: fiber-form logical vectors with zero coefficients allowed, followed by the full KL equations below weight d_0.


## main.tex:2059 — covered

Completeness half: completeness_of_nontrivial_two (with B1 = betaOf(n+1), a bound by betaBound_betaOf) and completeness_three_sharp cover every rank-two code of distance d >= d_0 with a nontrivial intrinsic diagonal group. Each such code gets a SortedNormalForm with q at most betaOf(n+1) or betaOf n, m | q, m >= 2, sorted primitive angles below q, the frame in fibres 0 and q/m, distance d, and an X string and permutation back to the code. Distance d >= d_0 implies the weight-below-d_0 conditions, as weakenDistance shows. betaOf N = beta_N for N >= 1, through the BetaExact certificate built from the Smith-witness bridge and betaOf_eq_of_exact. Converse half: sslp_converse builds an exact ((n,2,d_0)) code on any orthonormal fibre-form pair satisfying the Knill-Laflamme conditions, and orderOf_intrinsicClass_resolutionOfPair shows the class of D(a;q) on that code has order exactly m. QECC's cutoff uses smithBeta, which no declaration identifies with beta, and is not the carrier.

- `MainTheory.SSLPCompleteness.completeness_of_nontrivial_two`
- `MainTheory.SharpOuterCutoff.completeness_three_sharp`
- `MainTheory.SortedForm.SortedNormalForm`
- `MainTheory.SSLPCompleteness.weakenDistance`
- `MainTheory.BetaExists.betaBound_betaOf`
- `MainTheory.BetaExactValue.betaOf_eq_of_exact`
- `MainTheory.SSLPConverse.sslp_converse`
- `MainTheory.SSLPConverse.orderOf_intrinsicClass_resolutionOfPair`
- `QECC.CodeProjector.rankTwo_physicalOrder_cutoff`

## main.tex:2060 — covered

MainTheory.SSLPConverse.sslp_converse states it at the vector level: for primitive a with m | q and 2 ≤ m, any orthonormal pair supported in the fibres 0 and q/m that satisfies the full KL conditions below d is the frame of an exact ((n,2,d)) code whose projective diagonal logical group has an element of exact order m (also restated as MainTheory.PaperGeneralSSLP.rank_two_sslp_converse). QECC.general_sslp_directSum_converse gives the projector-level form for D(a;q) itself, with exact projective order m, but needs the vectors turned into a fibre projector family and the KL hypothesis supplied for the resulting projector.

- `MainTheory.SSLPConverse.sslp_converse`
- `MainTheory.PaperGeneralSSLP.rank_two_sslp_converse`
- `QECC.general_sslp_directSum_converse`

## main.tex:2061 — tracked

Restates the q ≤ β_r refinement of eq:d3-full-bound, which is partial. Using it as a filter on canonical enumeration data needs r to be unchanged by the canonical normalizations. MainTheory proves the support affine rank of any state invariant under local X (supportAffineRank_bxor) and qubit permutations (supportAffineRank_permAct), and a unit power does not change the code or its eigenvectors, so that part is not an extra gap.

- `MainTheory.RealSupportAffineRank.supportAffineRank_bxor`
- `MainTheory.RealSupportAffineRank.supportAffineRank_permAct`

## main.tex:2065 — gap

Two facts support the finite-enumeration claim: the set of triples (q, m, a) is finite once q is bounded, while the KL completion requirements form polynomial equations in the amplitudes' real and imaginary components. Both are elementary, but no declaration states either. Lean provides only the bound on q.

- `QECC.CodeProjector.rankTwo_physicalOrder_cutoff`

## main.tex:2068 — covered

The bounds hold for every nontrivial element, so testing reduced representatives within the cutoff recovers the whole group. rankTwo_physicalOrder_cutoff gives, for every nonzero class U of a rank-two code with distance at least two, a code-preserving reduced representative in U with q within the piecewise cutoff. That is exactly the surjectivity the procedure needs; the identification and identity steps follow from the definition of the projective quotient.

- `QECC.CodeProjector.rankTwo_physicalOrder_cutoff`

## main.tex:2084 — covered

Reworded lead-in to six:eq:qcutoff: the distance-three corollary together with beta_6 = 9 gives the exhaustive cutoff m | q, 2 <= q <= 9. d3_bound_nine states the conclusion for every element g of the intrinsic group of every ExactCode 6 2 3: a primitive lift D(a;q) with 0 < q <= 9 and orderOf g dividing q. For nontrivial g this forces q >= 2. The value 9 is betaOf_six; MainTheory's beta is built from inverse denominators, which inverseDenominator_eq_smithLastFactor identifies with the last Smith factor of each nonsingular matrix. The stated route through QECC's corollary is not closed numerically: distanceThree_physicalOrder_bound gives q <= smithBeta 6, but QECC proves no value of smithBeta, and no bridge to betaOf exists.

- `MainTheory.QMinBound.d3_bound_nine`
- `MainTheory.SmallBetaValues.betaOf_six`
- `MainTheory.SharpClearing.inverseDenominator_eq_smithLastFactor`
- `QECC.CodeProjector.distanceThree_physicalOrder_bound`

## main.tex:2234 — tracked

The passage says four things. Within q <= 9, the subset-sum, moment and support-dimension tests and the symmetry quotient leave 66 candidate classes. KL rules out 51 of them and realizes 15. The supplement's moment orbits are these classes, and its table numbering applies to them. In Lean, 66 is the number of labelled cube classes of the 215 certified pairs passing RankRow.CompatibilityCondition (PaperReductionChain.six_66_orbits with FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries), and 15 is the number of completable directory keys (RealizationOrbits15.card_realization_orbits). Two links are missing: the identification of those keys with the classes as def:six-sslp-orbits words them, and the tie of the generated numbering to the table rows. Both are recorded as uncovered under def:six-sslp-orbits, thm:six-15-sslp-realization-orbits and supplementary thm:main-result-II, so the passage is tracked there.

- `MainTheory.PaperReductionChain.six_66_orbits`
- `MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries`
- `MainTheory.RealizationOrbits15.card_realization_orbits`

## supplementary.tex:5340 — tracked

The supplement is byte-identical, so this clause is unchanged at the same lines. It is clause (iii) of cor:m2-current-status and leaves only the weight-enumerator images of orbits 1-4 unresolved, consistent with supp 60-62, 892-894 and 5686-5687, which record their physical realizations. The rewritten main.tex agrees: 2251-2254, Result II, and the Discussion at 2679-2681. Its coverage is that of cor:m2-current-status, whose three clauses MainTheory.PaperSupplementaryImages.m2_current_status_full states together: the order-two sector, fourteen empty images, seven determined images, and completions for classes 1-4. openKeys_hasCompletion and openKeys_paperIds give the realizations of the four open keys and identify them as paper classes 1-4. The erratum open-orbits-existence is resolved_in_text.

- `MainTheory.PaperSupplementaryImages.m2_current_status_full`
- `MainTheory.OpenOrbitsRealized.openKeys_hasCompletion`
- `MainTheory.DirectoryOrbitStatus.openKeys_paperIds`

## supplementary.tex:5742 — tracked

The section opening equates the main text's candidate classes with the moment orbits of thm:six-66-orbits and fixes one table numbering shared by both documents. paperOrbitId_injective and paperOrbitId_range make the generated paperOrbitId a bijection from the 66 keys onto 1..66, and PaperReductionChain.six_66_orbits says what the keys classify. No declaration equates those keys with the classes as def:six-sslp-orbits defines them, and none relates paperOrbitId to the table rows, which OrbitTableRecords.paperKey indexes. Both gaps are recorded as uncovered under def:six-sslp-orbits and the two Result II entries, so this sentence is tracked there.

- `MainTheory.PaperReductionChain.six_66_orbits`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_injective`
- `MainTheory.PaperSupplementaryNoGo.paperOrbitId_range`
- `MainTheory.Generated.OrbitTableRecords.paperKey`

## supplementary.tex:5772 — gap

The proof of thm:main-result-I takes the finite-cyclic structure of the rank-two projective diagonal group from main-text Corollary III.4, cited by hard-coded number. In 20260924 that number was cor:rank-two-sslp, the rank-two SSLP normal form, which contains the cyclicity claim (20260924/out/main.aux). 20260929 inserts lem:uniform-rational-section as III.1 and later lemmas in the shared Section III counter. III.4 now prints as Theorem III.4, thm:general-sslp-normal-form at main.tex 1069. That theorem is the general-K normal form for one chosen element, and the text before it says explicitly that the general group need not be cyclic. cor:rank-two-sslp is now Corollary III.5 (main.tex 1294; 20260929/out/main.aux). No corollary carries the number III.4, and the number now names a theorem that does not supply cyclicity. The intended mathematics is still carried in Lean. Single-number-operator detection gives finiteness via QECC.CodeProjector.projectiveDiagonalGroup_finite, and single-Z detection gives cyclicity via QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic. MainTheory.GeneralFiniteness.isCyclic covers exact distance-three rank-two codes. The statement of Result I does not depend on the number, so severity is low.

- `QECC.CodeProjector.projectiveDiagonalGroup_finite`
- `QECC.CodeProjector.projectiveDiagonalGroup_isAddCyclic`
- `MainTheory.GeneralFiniteness.isCyclic`

## supplementary.tex:5858 — tracked

This sets up Result III. It defines W_r as the A-vectors realized by exact codes whose projectors lie in class r, normalized as in eq:o36Ajdef, and so restates level (iii) of def:six-classification-levels for the supplement; thm:main-result-III reads its W_r from here. Lean defines only MainTheory.Levels.WImage, the normalized image on one fibre pair, which matches eq:o36Ajdef through the /4 factor. No public declaration states that this image equals the class-level set. That gap is already recorded as uncovered under def:six-classification-levels and thm:main-result-III, so this item adds nothing beyond those entries.

- `MainTheory.Levels.WImage`

## supplementary.tex:6003 — covered

The supplement is unchanged. This is the proof body (the proof environment runs 6002-6030), where the 20260924 record started at 6003. Each step has a Lean counterpart. Local diagonalization keeps (n,K,d) and the LU class and rescales the logical matrix by a unit scalar (exists_diagonal_normal_form). Each zero ancilla kills X/Y compressions and leaves I/Z ones (compression_snocPauli), so the padded frame keeps the distance (hasDistance_padFrame). The padded gate has the same logical matrix (intertwining_padFrame). A_1 grows by exactly the number of ancillas and is then positive (AWeight_padFrame_one, AWeight_padFrame_one_pos). At six qubits, exact distance three follows both from the weight-three obstruction (exactCode_distance_three) and from the K=2 Singleton bound (six_qubit_distance_le_three), so the unrestricted display is not needed. The opposite conclusion, that A_1 vanishes for any six-qubit code with an order-five transversal gate, through Result IV and LU invariance, is six_qubit_AWeight_one_zero. minimum_length derives the contradiction for an arbitrary tensor-product unitary whose logical matrix has projective order five. canonical_attains and six_qubit_lu_unique_of_distance_ge_three give attainment and uniqueness up to LU and qubit permutations at length six.

- `MainTheory.TransversalDiagonalization.exists_diagonal_normal_form`
- `MainTheory.AncillaPadding.compression_snocPauli`
- `MainTheory.AncillaPadding.hasDistance_padFrame`
- `MainTheory.AncillaGatePadding.intertwining_padFrame`
- `MainTheory.AncillaPadding.AWeight_padFrame_one`
- `MainTheory.AncillaPadding.AWeight_padFrame_one_pos`
- `MainTheory.SixQubitExactDistance.exactCode_distance_three`
- `MainTheory.QuantumSingleton.six_qubit_distance_le_three`
- `MainTheory.MinimumLengthOrderFive.six_qubit_AWeight_one_zero`
- `MainTheory.MinimumLengthOrderFive.minimum_length`
- `MainTheory.MinimumLengthOrderFive.canonical_attains`
- `MainTheory.MinimumLengthOrderFive.six_qubit_lu_unique_of_distance_ge_three`

## supplementary.tex:6032 — gap

This is the 20260924 item recorded at line 6036. The paragraph actually spans 6032-6057, and the file is byte-identical. It extends the length-six minimum to the case where no logical basis makes the whole projective transversal group Clifford. The argument diagonalizes each element separately and applies the III.C rank-two bound with beta_5=5, so element orders are at most five. It excludes order five with the corollary and uses Eastin-Knill to make the group G a finite subgroup of SO(3). It then invokes the classification of finite rotation groups to conjugate all of G into the octahedral (Clifford) group in one common logical basis. Only the order-five exclusion has a Lean counterpart (MainTheory.MinimumLengthOrderFive.minimum_length). Nothing in QECC, MainTheory, SixQubit or SS formalizes the full transversal group, the rotation-group classification or the single common conjugation; a grep for Clifford, octahedral and rotation-group terms finds only unrelated comments. None of these follows from the separate per-element order bounds. main.tex 2632-2638 relies on this paragraph, so the severity stays medium. The argument appears mathematically sound; this is a coverage gap, not an erratum.


## Remaining review

Not reviewed for 20260929: the running prose of main.tex outside Section III that is unchanged since 20260924, and the running prose of supplementary.tex beyond its references into main.tex and the three carried 20260924 assertions. Their 20260908 prose audit is background only. The ledger entries of both documents outside Section III, except the 16 re-reviewed ones, remain unreviewed for 20260929, as they were for 20260924.
