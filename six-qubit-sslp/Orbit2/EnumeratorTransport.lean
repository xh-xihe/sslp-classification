import Orbit2.ActiveProjector

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false

namespace Orbit2.PhysicalFlatness
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.PurityReduction
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem low_weight_spectator_zero (V : Encoder) (p : Label 6)
    (hw : physicalWeight p≤3) (hs : ¬ supported (Fin.cons 0 p) A) :
    physicalMass V p=0 := by
  let d (q : Label 6) : ℝ := (if physicalWeight q≤3 then physicalMass V q else 0) -
    (if supported (Fin.cons 0 q) A then physicalMass V q else 0)
  have hn (q : Label 6) : 0≤d q := by
    by_cases hq : supported (Fin.cons 0 q) A
    · by_cases hwt : physicalWeight q≤3
      · simp [d,hq,hwt]
      · have hz := active_supported_high_zero V q hq (by omega)
        simp [d,hq,hwt,hz]
    · by_cases hwt : physicalWeight q≤3
      · simpa [d,hq,hwt] using physicalMass_nonneg V q
      · simp [d,hq,hwt]
  have hsum : (∑ q, d q)=0 := by
    simp only [d,Finset.sum_sub_distrib]
    rw [low_weight_partition,← active_projection,active_mass,V.A_zero]
    have hf := V.flat
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hn q)).mp hsum p (Finset.mem_univ p)
  simpa [d,hw,hs] using hz

end Orbit2.PhysicalFlatness

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.PhysicalFlatness Orbit2.PurityReduction
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def splitLabel64 : Label 6 ≃ Label 2 × Label 4 where
  toFun p := (![p 0,p 1],![p 2,p 3,p 4,p 5])
  invFun x := joinLabel x.1 x.2
  left_inv p := by funext i; fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨p,q⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem sum_splitLabel64 (f : Label 6 → ℝ) :
    (∑ p, f p)=∑ b : Label 2, ∑ a : Label 4, f (joinLabel b a) := by
  simpa [Fintype.sum_prod_type,splitLabel64] using (splitLabel64.symm.sum_comp f).symm

theorem active_support_split : ∀ (p : Label 2) (q : Label 4),
    supported (Fin.cons 0 (joinLabel p q)) A ↔ p=(fun _ => 0) := by decide +kernel

theorem active_weight_split (q : Label 4) : physicalWeight (joinLabel (fun _ => 0) q)=activeWeight q := by
  simp [physicalWeight,activeWeight,joinLabel,Fin.sum_univ_succ]

/-- The weight-three enumerator contains only active coefficients; all
spectator-dressed low-weight mass has been rigorously eliminated. -/
theorem Encoder.A3_active (V : Encoder) :
    V.A 3 = ∑ q : Label 4, if activeWeight q=3 then physicalMass V (joinLabel (fun _ => 0) q) else 0 := by
  rw [physical_enumerator,sum_splitLabel64]
  have he (p : Label 2) :
      (∑ q : Label 4, if physicalWeight (joinLabel p q)=3 then physicalMass V (joinLabel p q) else 0) =
      if p=(fun _ => 0) then
        (∑ q : Label 4, if activeWeight q=3 then physicalMass V (joinLabel (fun _ => 0) q) else 0) else 0 := by
    by_cases hp : p=(fun _ => 0)
    · subst p
      simp [active_weight_split]
    · simp only [hp,if_false]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hw : physicalWeight (joinLabel p q)=3
      · have hs : ¬ supported (Fin.cons 0 (joinLabel p q)) PurityReduction.A := by
          simpa [active_support_split] using hp
        have hz := low_weight_spectator_zero V (joinLabel p q) (by omega) hs
        simp [hw,hz]
      · simp [hw]
  simp_rw [he]
  simp

theorem Encoder.activeMass_projector (V : Encoder) (q : Label 4) :
    physicalMass V (joinLabel (fun _ => 0) q) =
      4 * Complex.normSq (tau (operator q * V.activeProjector)) := by
  rw [V.activeProjector_trace_transport]
  unfold physicalMass
  simp [Complex.normSq_div]
  ring

/-- Exact normalization of A3 in terms of the actual rank-eight projector. -/
theorem Encoder.A3_projector (V : Encoder) :
    V.A 3 = 4 * ∑ q : Label 4,
      if activeWeight q=3 then Complex.normSq (tau (operator q * V.activeProjector)) else 0 := by
  rw [V.A3_active,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp [V.activeMass_projector]

end Orbit2
