import Orbit2.Global
import Orbit2.Analytic
import Orbit2.MatrixSteps
import Orbit2.MacWilliams
import Orbit2.Encoder
import Orbit2.Defects
import Orbit2.PauliConjugation
import Orbit2.Reconstruction
import Orbit2.Attainment
import Orbit2.LowWeightFlatness
import Orbit2.PauliReconstruction
import Orbit2.PhysicalDefects
import Orbit2.TraceReality
import Orbit2.FinalReduction
import Orbit2.Complete

/-! Axiom audit: these should report only propext, Classical.choice, Quot.sound.
In particular there is no sorryAx, native_decide, or custom axiom. -/
#print axioms Orbit2.checked_polynomial_rigidity
#print axioms Orbit2.enumerator_of_flatness_and_rigidity
#print axioms Orbit2.commonJ_block_identity
#print axioms Orbit2.split_isometry
#print axioms Orbit2.split_projection
#print axioms Orbit2.macWilliams_normal_form
#print axioms Orbit2.alternating_shadow_identity
#print axioms Orbit2.Encoder.macWilliams
#print axioms Orbit2.Encoder.shadow
#print axioms Orbit2.Frames.omega_left
#print axioms Orbit2.Defects.frame_compressionDefect
#print axioms Orbit2.Quartic.J_trace_shortcut
#print axioms Orbit2.Quartic.twiceCoefficient_offblock
#print axioms Orbit2.Quartic.Coefficient000.certified_matrix
#print axioms Orbit2.FiveQubit.code_pure_KL
#print axioms Orbit2.Quartic.reconstructed_polynomial_eq_certificate
#print axioms Orbit2.SplitSeed.every_parameter_attained_exact_distance
#print axioms Orbit2.Encoder.flat
#print axioms Orbit2.PhysicalFlatness.target_masses_zero
#print axioms Orbit2.TensorPauli.matrix_reconstruction
#print axioms Orbit2.Encoder.spectatorDensity_flat
#print axioms Orbit2.Encoder.computationalFrames_isometry
#print axioms Orbit2.Encoder.schmidtFrame_parity
#print axioms Orbit2.Encoder.physical_commonJ
#print axioms Orbit2.Encoder.physicalT_equations
#print axioms Orbit2.Encoder.A3_projector
#print axioms Orbit2.Encoder.activeProjector_diagonal
#print axioms Orbit2.Encoder.physicalOmega_distance_one_zero
#print axioms Orbit2.Encoder.physicalT_support
#print axioms Orbit2.Encoder.physicalT_expansion
#print axioms Orbit2.Quartic.wordTrace_four_real
#print axioms Orbit2.Encoder.A3_zero_of_T_rigidity
#print axioms Orbit2.Encoder.enumerator_of_certificate_nonpositive
#print axioms Orbit2.Quartic.projection_contraction_expansion
#print axioms Orbit2.Quartic.J_contraction_expansion
#print axioms Orbit2.Quartic.c_contraction_expansion
#print axioms Orbit2.Quartic.physical_raw_nonpositive
#print axioms Orbit2.Quartic.orderedPolynomial_eq_fullEnergy
#print axioms Orbit2.Quartic.fullCoefficientEnergy_eq_certificate
#print axioms Orbit2.Encoder.certificate_nonpositive
#print axioms Orbit2.Encoder.enumerator
#print axioms Orbit2.Encoder.A3_zero
#print axioms Orbit2.Encoder.exact_distance_three
#print axioms Orbit2.orbit2_exact_enumerator_image
