import DyadicLifts.Seed.Defs
import SS.PauliSites

/-!
# The seed's Knill--Laflamme checks, one support position at a time

GENERATED FILE -- do not edit by hand; regenerate with `gen_checks.py`.

`KLmatK_of_sites` reduces the Knill--Laflamme conditions for all Paulis of
weight at most two to three statements: one at the identity, one per single
site, and one per ordered pair of sites.  Each is decided by the kernel on the
integer mirror of the code.

The split into one declaration per position is not cosmetic.  The kernel holds a
single reduction cache for the whole of a declaration and frees it only when
that declaration is complete, so proving every position inside one `decide`
accumulates the intermediate terms of all of them -- measured at about 4.5 GB
per minute, which exhausts memory long before the nine-qubit rung finishes.  One
declaration per position bounds the live cache by the cost of a single position.

The assembly lemmas at the end perform no computation: they case on the index
and hand each goal the corresponding declaration, positionally, so that no
`exact` is ever attempted against a goal it does not match.

No `sorry`, no `native_decide`.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

open DyadicLifts SS SS.ZSqrt235i

namespace BD16Kernel

/-! ## Rung 0: 7 qubits -/

/-- The identity Pauli. -/
theorem k7_id : klAtZ S7Z ψ0Z ψ1Z (fun _ => SQ.I) = true := by
  decide +kernel

theorem k7_o0 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨0, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o1 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨1, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o2 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨2, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o3 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨3, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o4 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨4, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o5 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨5, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

theorem k7_o6 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite (⟨6, by omega⟩ : Fin 7) A) = true := by
  decide +kernel

/-- Every weight-one Pauli. -/
theorem k7_one : ∀ (i : Fin 7) (A : SQ), A ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (oneSite i A) = true := by
  intro i A hA
  fin_cases i
  exacts [k7_o0 A hA, k7_o1 A hA, k7_o2 A hA, k7_o3 A hA, k7_o4 A hA, k7_o5 A hA, k7_o6 A hA]

theorem k7_p0_1 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨1, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p0_2 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨2, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p0_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨3, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p0_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨4, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p0_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p0_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨0, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p1_2 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨1, by omega⟩ : Fin 7) (⟨2, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p1_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨1, by omega⟩ : Fin 7) (⟨3, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p1_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨1, by omega⟩ : Fin 7) (⟨4, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p1_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨1, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p1_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨1, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p2_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨2, by omega⟩ : Fin 7) (⟨3, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p2_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨2, by omega⟩ : Fin 7) (⟨4, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p2_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨2, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p2_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨2, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p3_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨3, by omega⟩ : Fin 7) (⟨4, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p3_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨3, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p3_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨3, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p4_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨4, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p4_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨4, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

theorem k7_p5_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite (⟨5, by omega⟩ : Fin 7) (⟨6, by omega⟩ : Fin 7) A B) = true := by
  decide +kernel

/-- Every weight-two Pauli.  The cells with `i ≥ j` are discharged from
the ordering hypothesis. -/
theorem k7_two : ∀ (i j : Fin 7) (A B : SQ), i < j → A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S7Z ψ0Z ψ1Z (twoSite i j A B) = true := by
  intro i j A B hij hA hB
  fin_cases i <;> fin_cases j
  exacts [absurd hij (by decide),
    k7_p0_1 A B hA hB,
    k7_p0_2 A B hA hB,
    k7_p0_3 A B hA hB,
    k7_p0_4 A B hA hB,
    k7_p0_5 A B hA hB,
    k7_p0_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    k7_p1_2 A B hA hB,
    k7_p1_3 A B hA hB,
    k7_p1_4 A B hA hB,
    k7_p1_5 A B hA hB,
    k7_p1_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k7_p2_3 A B hA hB,
    k7_p2_4 A B hA hB,
    k7_p2_5 A B hA hB,
    k7_p2_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k7_p3_4 A B hA hB,
    k7_p3_5 A B hA hB,
    k7_p3_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k7_p4_5 A B hA hB,
    k7_p4_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k7_p5_6 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide)]

/-! ## Rung 1: 9 qubits -/

/-- The identity Pauli. -/
theorem k9_id : klAtZ S9Z ψ0Z1 ψ1Z1 (fun _ => SQ.I) = true := by
  decide +kernel

theorem k9_o0 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨0, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o1 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨1, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o2 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨2, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o3 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨3, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o4 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨4, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o5 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨5, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o6 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨6, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o7 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨7, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

theorem k9_o8 : ∀ A : SQ, A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite (⟨8, by omega⟩ : Fin 9) A) = true := by
  decide +kernel

/-- Every weight-one Pauli. -/
theorem k9_one : ∀ (i : Fin 9) (A : SQ), A ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (oneSite i A) = true := by
  intro i A hA
  fin_cases i
  exacts [k9_o0 A hA, k9_o1 A hA, k9_o2 A hA, k9_o3 A hA, k9_o4 A hA, k9_o5 A hA, k9_o6 A hA, k9_o7 A hA, k9_o8 A hA]

theorem k9_p0_1 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨1, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_2 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨2, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨3, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨4, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨5, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p0_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨0, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_2 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨2, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨3, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨4, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨5, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p1_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨1, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_3 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨3, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨4, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨5, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p2_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨2, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p3_4 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨3, by omega⟩ : Fin 9) (⟨4, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p3_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨3, by omega⟩ : Fin 9) (⟨5, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p3_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨3, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p3_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨3, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p3_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨3, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p4_5 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨4, by omega⟩ : Fin 9) (⟨5, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p4_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨4, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p4_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨4, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p4_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨4, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p5_6 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨5, by omega⟩ : Fin 9) (⟨6, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p5_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨5, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p5_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨5, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p6_7 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨6, by omega⟩ : Fin 9) (⟨7, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p6_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨6, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

theorem k9_p7_8 : ∀ A B : SQ, A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite (⟨7, by omega⟩ : Fin 9) (⟨8, by omega⟩ : Fin 9) A B) = true := by
  decide +kernel

/-- Every weight-two Pauli.  The cells with `i ≥ j` are discharged from
the ordering hypothesis. -/
theorem k9_two : ∀ (i j : Fin 9) (A B : SQ), i < j → A ≠ SQ.I → B ≠ SQ.I →
    klAtZ S9Z ψ0Z1 ψ1Z1 (twoSite i j A B) = true := by
  intro i j A B hij hA hB
  fin_cases i <;> fin_cases j
  exacts [absurd hij (by decide),
    k9_p0_1 A B hA hB,
    k9_p0_2 A B hA hB,
    k9_p0_3 A B hA hB,
    k9_p0_4 A B hA hB,
    k9_p0_5 A B hA hB,
    k9_p0_6 A B hA hB,
    k9_p0_7 A B hA hB,
    k9_p0_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p1_2 A B hA hB,
    k9_p1_3 A B hA hB,
    k9_p1_4 A B hA hB,
    k9_p1_5 A B hA hB,
    k9_p1_6 A B hA hB,
    k9_p1_7 A B hA hB,
    k9_p1_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p2_3 A B hA hB,
    k9_p2_4 A B hA hB,
    k9_p2_5 A B hA hB,
    k9_p2_6 A B hA hB,
    k9_p2_7 A B hA hB,
    k9_p2_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p3_4 A B hA hB,
    k9_p3_5 A B hA hB,
    k9_p3_6 A B hA hB,
    k9_p3_7 A B hA hB,
    k9_p3_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p4_5 A B hA hB,
    k9_p4_6 A B hA hB,
    k9_p4_7 A B hA hB,
    k9_p4_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p5_6 A B hA hB,
    k9_p5_7 A B hA hB,
    k9_p5_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p6_7 A B hA hB,
    k9_p6_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    k9_p7_8 A B hA hB,
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide),
    absurd hij (by decide)]

end BD16Kernel
