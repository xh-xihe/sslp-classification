import MainTheory.Orbit3QuadraticZeros

/-! # Actual Pauli zero factors in the orbit-3 degree-six certificate

The constraints concern the actual logical superposition of an arbitrary
completion. A Pauli label is decoded in the certificate convention x+64*z,
with physical site zero the least significant bit.
-/

namespace MainTheory.Orbit3PauliZeros

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.PhysicalPauliCategories
open MainTheory.OrderTwoScalarBridge MainTheory.Orbit3CategoryShift
open SixQubit.ParityPauliScalars SixQubit.ParityLogicalState SS.MacWilliams
open SixQubit.Generated

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def decode (r : Fin 4096) : SS.PauliString 6 :=
  ⟨SixQubit.Realize.nbit (r.val % 64), SixQubit.Realize.nbit (r.val / 64)⟩

def label (P : SS.PauliString 6) : Fin 4096 :=
  ⟨SixQubit.Realize.num P.x + 64 * SixQubit.Realize.num P.z, by
    have hx := SixQubit.Realize.num_lt P.x
    have hz := SixQubit.Realize.num_lt P.z
    omega⟩

theorem decode_label (P : SS.PauliString 6) : decode (label P) = P := by
  have hx := SixQubit.Realize.num_lt P.x
  have hmod : (label P).val % 64 = SixQubit.Realize.num P.x := by
    simp only [label, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hdiv : (label P).val / 64 = SixQubit.Realize.num P.z := by
    change (SixQubit.Realize.num P.x + 64 * SixQubit.Realize.num P.z) / 64 = _
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hx, zero_add]
  unfold decode
  rw [hmod, hdiv, SixQubit.Realize.nbit_num, SixQubit.Realize.nbit_num]

theorem label_decode : ∀ r : Fin 4096, label (decode r) = r := by
  decide +kernel

def labelEquiv : Fin 4096 ≃ SS.PauliString 6 where
  toFun := decode
  invFun := label
  left_inv := label_decode
  right_inv := decode_label

def Constrained (P : SS.PauliString 6) : Prop :=
  (P.wt ≤ 2 ∧ SS.bdot orbit3Mask P.x = true) ∨
    (shift P).wt ≤ 2 ∨
    ∃ c : Fin 5, category P = Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c)

instance (P : SS.PauliString 6) : Decidable (Constrained P) := by
  unfold Constrained
  infer_instance

theorem constrained_mel_zero (W : Encoder) (P : SS.PauliString 6)
    (hP : Constrained P) :
    mel (superposition W.states) (superposition W.states) P = 0 := by
  rcases hP with ⟨hwt, hodd⟩ | hwt | ⟨c, hc⟩
  · apply superposition_anticommuting_kl_zero W.states (orbit3_parity W) P
    · rw [chi_bdot, hodd]
      rfl
    · exact W.hasDistance P hwt
  · have h := superposition_twisted_kl_zero W.states (orbit3_parity W) (shift P)
      (W.hasDistance (shift P) hwt)
    change mel (superposition W.states) (superposition W.states) (shift (shift P)) = 0 at h
    rw [shift_involution] at h
    exact h
  · exact MainTheory.Orbit3QuadraticZeros.zero_category_quadratic W c P hc

theorem constrained_expectation_zero (W : Encoder) (P : SS.PauliString 6)
    (hP : Constrained P) :
    SS.innerC (superposition W.states) (SS.pauliAct P (superposition W.states)) = 0 := by
  rw [innerC_eq_mel, constrained_mel_zero W P hP, mul_zero]

theorem triple_zero (W : Encoder) (P : Fin 3 → SS.PauliString 6)
    (hP : ∃ k : Fin 3, Constrained (P k)) :
    (∏ k : Fin 3, SS.innerC (superposition W.states)
      (SS.pauliAct (P k) (superposition W.states))) = 0 := by
  obtain ⟨k, hk⟩ := hP
  exact Finset.prod_eq_zero (Finset.mem_univ k) (constrained_expectation_zero W (P k) hk)

end MainTheory.Orbit3PauliZeros
