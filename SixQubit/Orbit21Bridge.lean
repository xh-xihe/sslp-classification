import Mathlib
import SixQubit.MacWilliams
import SixQubit.Realize
import SixQubit.Orbit21Coef
import SixQubit.Orbit21Bound

/-!
# Orbit 21: from masks to Paulis

`SixQubit/Orbit21Coef.lean` decides the certificate's finite content over `Nat`
masks, because `decide` over `Fin 6 -> Bool` is too slow to reach it.
`SixQubit/Orbit21Bound.lean` consumes the same content over `SS.PauliString 6`.
This module is the transport between them, using the `num`/`nbit` pair of
`SixQubit/Realize.lean`, which is already proved to be inverse on all 64
strings.

The two symmetries become equivalences of `SS.PauliString 6`: both are
involutions on the `Z`-part, so each is its own inverse and `Equiv` is
immediate.
-/

namespace SixQubit.Orbit21Bridge

open SS.MacWilliams SixQubit.Realize

/-! ## The symmetries as equivalences -/

/-- The `Z`-mask of the forced stabilizer, as a bitstring. -/
def gbits : SS.BitString 6 := nbit Orbit21Coef.gmask

/-- Multiplication by `G`: exclusive-or the `Z`-part with `gbits`. -/
def sigG : SS.PauliString 6 ≃ SS.PauliString 6 where
  toFun P := ⟨P.x, SS.bxor P.z gbits⟩
  invFun P := ⟨P.x, SS.bxor P.z gbits⟩
  left_inv P := by
    cases P with
    | mk x z =>
        have hz : ∀ i, SS.bxor (SS.bxor z (fun i => gbits i)) (fun i => gbits i) i = z i := by
          intro i
          have : ∀ p q : Bool, xor (xor p q) q = p := by decide
          simpa only [SS.bxor_apply] using this (z i) (gbits i)
        simp only [SS.PauliString.mk.injEq, true_and]
        exact funext hz
  right_inv P := by
    cases P with
    | mk x z =>
        have hz : ∀ i, SS.bxor (SS.bxor z (fun i => gbits i)) (fun i => gbits i) i = z i := by
          intro i
          have : ∀ p q : Bool, xor (xor p q) q = p := by decide
          simpa only [SS.bxor_apply] using this (z i) (gbits i)
        simp only [SS.PauliString.mk.injEq, true_and]
        exact funext hz

/-- Conjugation by the diagonal gate: exclusive-or the `Z`-part with
`x and gbits`.  The `X`-part is untouched, so this too is an involution. -/
def sigD : SS.PauliString 6 ≃ SS.PauliString 6 where
  toFun P := ⟨P.x, SS.bxor P.z (fun i => P.x i && gbits i)⟩
  invFun P := ⟨P.x, SS.bxor P.z (fun i => P.x i && gbits i)⟩
  left_inv P := by
    cases P with
    | mk x z =>
        have hz : ∀ i, SS.bxor (SS.bxor z (fun i => x i && gbits i)) (fun i => x i && gbits i) i = z i := by
          intro i
          have : ∀ p q : Bool, xor (xor p q) q = p := by decide
          simpa only [SS.bxor_apply] using this (z i) (x i && gbits i)
        simp only [SS.PauliString.mk.injEq, true_and]
        exact funext hz
  right_inv P := by
    cases P with
    | mk x z =>
        have hz : ∀ i, SS.bxor (SS.bxor z (fun i => x i && gbits i)) (fun i => x i && gbits i) i = z i := by
          intro i
          have : ∀ p q : Bool, xor (xor p q) q = p := by decide
          simpa only [SS.bxor_apply] using this (z i) (x i && gbits i)
        simp only [SS.PauliString.mk.injEq, true_and]
        exact funext hz

@[simp] lemma sigG_x (P : SS.PauliString 6) : (sigG P).x = P.x := rfl
@[simp] lemma sigD_x (P : SS.PauliString 6) : (sigD P).x = P.x := rfl

/-! ## `num` is a homomorphism for the two mask operations

The bridge needs the encoding to commute with exclusive-or and conjunction.
Both are true bit by bit and decidable over all 4096 pairs. -/

set_option maxRecDepth 40000 in
theorem num_bxor : ∀ u v : SS.BitString 6,
    num (SS.bxor u v) = num u ^^^ num v := by decide

set_option maxRecDepth 40000 in
theorem num_band : ∀ u v : SS.BitString 6,
    num (fun i => u i && v i) = num u &&& num v := by decide

/-- `nbit` of the stabilizer mask encodes back to it. -/
theorem num_gbits : num gbits = Orbit21Coef.gmask := by decide

/-! ## The coefficient, on Paulis -/

/-- The certificate's coefficient, read through the mask encoding. -/
def cf (P : SS.PauliString 6) : ℝ :=
  ((Orbit21Coef.coef (num P.x) (num P.z) : Int) : ℝ)

/-- The label is one the fibers force to contribute nothing. -/
def isForced (P : SS.PauliString 6) : Prop :=
  Orbit21Coef.forced (num P.x) = true

instance : DecidablePred isForced := fun _ => by unfold isForced; infer_instance

/-- The mask-level identities of `Orbit21Coef` transported to `PauliString`.

`num` and `nbit` are inverse on all 64 strings and `num` lands below 64, so the
decided statement applies to every Pauli. -/
theorem cf_group_sum (P : SS.PauliString 6) :
    cf P + cf (sigG P) + cf (sigD P) + cf (sigG (sigD P)) = 0 ∨ isForced P := by
  classical
  have hx := num_lt P.x
  have hz := num_lt P.z
  have h := Orbit21Coef.coef_group_sum (num P.x) hx (num P.z) hz
  have hnx : nbit (num P.x) = P.x := nbit_num P.x
  have hnz : nbit (num P.z) = P.z := nbit_num P.z
  have hG : num (sigG P).z = num P.z ^^^ Orbit21Coef.gmask := by
    show num (SS.bxor P.z gbits) = _
    rw [num_bxor, num_gbits]
  have hD : num (sigD P).z = num P.z ^^^ (num P.x &&& Orbit21Coef.gmask) := by
    show num (SS.bxor P.z (fun i => P.x i && gbits i)) = _
    rw [num_bxor, num_band, num_gbits]
  have hGD : num (sigG (sigD P)).z
      = (num P.z ^^^ (num P.x &&& Orbit21Coef.gmask)) ^^^ Orbit21Coef.gmask := by
    show num (SS.bxor (sigD P).z gbits) = _
    rw [num_bxor, num_gbits, hD]
  rcases h with h0 | hf
  · left
    unfold cf
    rw [show (sigG P).x = P.x from rfl, show (sigD P).x = P.x from rfl,
      show (sigG (sigD P)).x = P.x from rfl, hG, hD, hGD]
    have := h0
    simp only [Orbit21Coef.shiftG, Orbit21Coef.shiftD] at this
    exact_mod_cast congrArg (fun t : Int => (t : ℝ)) this
  · right
    exact hf

end SixQubit.Orbit21Bridge
