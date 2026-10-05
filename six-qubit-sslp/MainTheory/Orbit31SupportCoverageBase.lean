import MainTheory.Orbit31SupportSemantics

/-! A finite primal-union or strict-support dual certificate covers a mask.
The witness check is computational; its conclusion concerns arbitrary real
probabilities in the actual orbit-31 moment system.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit31SupportCoverageBase
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.Generated.Orbit31SupportArithmetic
noncomputable section

def unionMasks (w : List (Fin 204)) : ℕ :=
  w.foldr (fun v mask => primalMasks v ||| mask) 0

theorem union_bit (w : List (Fin 204)) (j : ℕ) :
    (unionMasks w).testBit j = true ↔
      ∃ v ∈ w, (primalMasks v).testBit j = true := by
  induction w with
  | nil => simp [unionMasks,Nat.zero_testBit]
  | cons v vs ih =>
    simp only [unionMasks,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true,
      List.mem_cons,exists_eq_or_imp]
    exact or_congr Iff.rfl ih

theorem member_subset {w : List (Fin 204)} {v : Fin 204} (hv : v ∈ w) :
    primalMasks v &&& unionMasks w = primalMasks v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  cases h : (primalMasks v).testBit j with
  | false => simp
  | true => rw [(union_bit w j).mpr ⟨v,hv,h⟩]; rfl

theorem support_exists_of_union {mask : ℕ} {w : List (Fin 204)}
    (hne : w ≠ []) (hunion : unionMasks w = mask) :
    ∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p := by
  have hhead : ∃ v, v ∈ w := List.exists_mem_of_ne_nil w hne
  have hw : ∀ j : Fin 16, ∃ v : Fin 204,
      (primalMasks v &&& mask = primalMasks v) ∧
      (mask.testBit j.val = true → (primalMasks v).testBit j.val = true) := by
    intro j
    by_cases hj : mask.testBit j.val = true
    · obtain ⟨v,hv,hbit⟩ := (union_bit w j.val).mp (hunion.symm ▸ hj)
      exact ⟨v,hunion ▸ member_subset hv,fun _ => hbit⟩
    · obtain ⟨v,hv⟩ := hhead
      exact ⟨v,hunion ▸ member_subset hv,fun h => False.elim (hj h)⟩
  choose witness hvalid using hw
  exact support_exists_of_primal hvalid

inductive Certificate where
  | primal (vertices : List (Fin 204))
  | dual (profile : Fin 68) (coordinate : Fin 16)

def Valid (mask : ℕ) : Certificate → Prop
  | .primal w => w ≠ [] ∧ unionMasks w = mask
  | .dual v j => DualWitness mask v j

instance (mask : ℕ) (certificate : Certificate) : Decidable (Valid mask certificate) := by
  cases certificate <;> unfold Valid
  · infer_instance
  · unfold DualWitness
    infer_instance

def isPrimal : Certificate → Bool
  | .primal _ => true
  | .dual _ _ => false

theorem feasible_iff {mask : ℕ} {certificate : Certificate}
    (hv : Valid mask certificate) :
    (∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p) ↔ isPrimal certificate = true := by
  cases certificate with
  | primal w =>
    exact iff_of_true (support_exists_of_union hv.1 hv.2) rfl
  | dual v j =>
    exact iff_of_false (support_excluded_of_dual hv) Bool.false_ne_true

end
end MainTheory.Orbit31SupportCoverageBase
