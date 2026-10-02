import QECC.IntrinsicSSLP
import QECC.NormalFormTransport
import QECC.PauliTransport

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- The two physical normalizations used by SSLP preserve the full Pauli
distance condition. -/
theorem hasDistanceAtLeast_xor_permutation {d : ℕ}
    (hd : C.HasDistanceAtLeast d) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) :
    ((C.reindex (xorEquiv t)).reindex
      (coordinateEquiv sigma)).HasDistanceAtLeast d :=
  (C.reindex (xorEquiv t)).hasDistanceAtLeast_reindex_coordinate
    (C.hasDistanceAtLeast_reindex_xor hd t) sigma

/-- Every active sector contains a computational-basis string in its fiber
with a nonzero amplitude in some code vector. -/
theorem exists_support_string_of_activeResidue (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) :
    ∃ x : BitString n, subsetSum a x = b.1 := by
  classical
  obtain ⟨psi, hpsi, hpsi_ne⟩ :=
    (Submodule.ne_bot_iff (C.phaseSector a b.1)).1 b.2
  have hfun : ∃ x, psi x ≠ 0 := Function.ne_iff.mp hpsi_ne
  obtain ⟨x, hx⟩ := hfun
  refine ⟨x, ?_⟩
  by_contra hsum
  exact hx (hpsi.2 x hsum)

/-- **Canonical transport part of the SSLP normal form.**

Choose a basis string in the anchor sector, conjugate by its local `X`
pattern, and then permute coordinates.  The anchor fiber becomes the zero
fiber, every other label is translated by the anchor residue, the coefficient
vector keeps exact order `q`, and its canonical representatives become
nondecreasing. -/
theorem exists_xor_permutation_normalization
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a) :
    ∃ (t : BitString n) (sigma : Equiv.Perm (Fin n)),
      subsetSum R.a t = b0.1 ∧
      let aX := xorCoefficient t R.a
      let aCanonical := permuteCoefficient sigma aX
      Monotone (fun j => (aCanonical j).val) ∧
      addOrderOf aCanonical = R.q ∧
      ((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).Preserves
        (phaseHom n R.q
          (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical) ∧
      (∀ b : ZMod R.q,
        coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber R.a b) =
          subsetSumFiber aCanonical (b - b0.1)) := by
  let hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  obtain ⟨t, ht⟩ := C.exists_support_string_of_activeResidue R.a b0
  let aX := xorCoefficient t R.a
  obtain ⟨sigma, hmono⟩ := exists_permuteCoefficient_monotone_val aX
  let aCanonical := permuteCoefficient sigma aX
  have hXpres : (C.reindex (xorEquiv t)).Preserves
      (phaseHom n R.q hq aX) := by
    simpa [ReducedDiagonalRepresentative.phase, aX] using
      C.reindex_xor_preserves_phaseHom hq R.a t hpres
  have hCanonicalPres :
      ((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).Preserves
        (phaseHom n R.q hq aCanonical) := by
    simpa [aCanonical] using
      (C.reindex (xorEquiv t)).reindex_coordinate_preserves_phaseHom
        hq sigma aX hXpres
  have hprimitiveX : addOrderOf aX = R.q := by
    exact xorCoefficient_primitive t R.a R.primitive
  have hprimitiveCanonical : addOrderOf aCanonical = R.q := by
    exact permuteCoefficient_primitive sigma aX hprimitiveX
  refine ⟨t, sigma, ht, hmono, hprimitiveCanonical, hCanonicalPres, ?_⟩
  intro b
  rw [image_subsetSumFiber_xorEquiv, ht,
    image_subsetSumFiber_coordinateEquiv]

/-- The transported coefficient vector in the preceding theorem is again a
reduced representative and therefore satisfies the canonical common-gcd-one
condition from the paper. -/
theorem canonical_commonGCD_eq_one
    (R : ReducedDiagonalRepresentative n) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) :
    let R' : ReducedDiagonalRepresentative n :=
      { q := R.q
        q_ge_two := R.q_ge_two
        a := permuteCoefficient sigma (xorCoefficient t R.a)
        primitive := permuteCoefficient_primitive sigma _
          (xorCoefficient_primitive t R.a R.primitive) }
    R'.commonGCD = 1 := by
  dsimp
  exact ReducedDiagonalRepresentative.commonGCD_eq_one _

end CodeProjector

end

end QECC
