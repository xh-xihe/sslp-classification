import MainTheory.Orbit31SupportCoverageBase
import MainTheory.Orbit31SignedSupport

/-! Each signed-graph audit record carries its own real moment witness. -/
set_option autoImplicit false
namespace MainTheory.Orbit31PhaseCoverageBase
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase (M b)
open MainTheory.Orbit31SupportSemantics (maskSet)

structure Entry where
  mask : Fin 65536
  vertices : List (Fin 204)
  phase : MainTheory.Orbit31SignedSupport.Certificate

def Valid (entry : Entry) : Prop :=
  entry.vertices ≠ [] ∧
    MainTheory.Orbit31SupportCoverageBase.unionMasks entry.vertices = entry.mask.val ∧
    MainTheory.Orbit31SignedSupport.NoSingleton entry.mask.val ∧
    MainTheory.Orbit31SignedSupport.Valid entry.mask.val entry.phase

instance (entry : Entry) : Decidable (Valid entry) := by
  unfold Valid
  infer_instance

theorem real_feasible {entry : Entry} (hv : Valid entry) :
    ∃ p, Feasible M b p ∧ ExactSupport (maskSet entry.mask.val) p :=
  MainTheory.Orbit31SupportCoverageBase.support_exists_of_union hv.1 hv.2.1

theorem graph_iff {entry : Entry} (hv : Valid entry) :
    MainTheory.Orbit31SignedSupport.GraphCompatible entry.mask.val ↔
      MainTheory.Orbit31SignedSupport.isColoring entry.phase = true :=
  MainTheory.Orbit31SignedSupport.compatible_iff hv.2.2.2

end MainTheory.Orbit31PhaseCoverageBase
