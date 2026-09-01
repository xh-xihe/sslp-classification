import MainTheory.FiniteGateAsPhase
import MainTheory.LabelledGates
import MainTheory.IntrinsicTransport

/-!
# Recovering a class from a coprime power of it

The entrance's normalization multiplies the angle vector by a unit of `ZMod q`
(`SixQubitSemanticEntrance.normalizedFiniteAngle`), so the bounded gate it hands
back represents `g ^ c` for some `c` coprime to the order, not `g` itself.

That is not an obstruction.  A coprime power generates the same cyclic subgroup,
so `g` is in turn a power of `g ^ c`, and a power of a labelled gate is again a
labelled gate: `FiniteGateAsPhase.phaseOfAngle_natMul` scales the angle vector
instead of leaving the bounded label set.  This file records both halves.
-/

namespace MainTheory.CoprimePowerRecovery

open MainTheory.ClassificationLevels
open MainTheory.FiniteGateAsPhase

/-- **A group element is a power of any coprime power of itself.**

If `g ^ k = 1` and `c` is coprime to `k`, then some `d` satisfies `(g ^ c) ^ d = g`.
This is the arithmetic that turns a bounded representative of `g ^ c` into one
of `g`. -/
theorem exists_pow_eq_self {G : Type*} [Group G] (g : G) (k : ℕ)
    (hk : 0 < k) (hgk : g ^ k = 1) (c : ℕ) (hc : Nat.Coprime c k) :
    ∃ d : ℕ, (g ^ c) ^ d = g := by
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨v, hv⟩ := ((ZMod.isUnit_iff_coprime c k).2 hc).exists_right_inv
  refine ⟨v.val, ?_⟩
  have hcast : ((c * v.val : ℕ) : ZMod k) = ((1 : ℕ) : ZMod k) := by
    push_cast
    simpa [ZMod.natCast_val, ZMod.cast_id] using hv
  have hmod : c * v.val % k = 1 % k :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
  rw [← pow_mul, pow_eq_pow_mod (c * v.val) hgk, hmod,
    ← pow_eq_pow_mod 1 hgk, pow_one]

/-- A power of a bounded labelled gate is again a bounded labelled gate. -/
theorem exists_label_of_pow (m : ℕ) (hm : m ≤ 8) (zeta : ℂ)
    (hz : zeta ^ (m + 1) = 1) (a : Fin 6 → ZMod (m + 1)) (c : ℕ) :
    ∃ lbl : ProjectiveGroupFinite.BoundedPhaseLabel 6 9,
      BoundedRepresentation.gateOfLabel lbl
        = (fun j => (phaseOfAngle zeta hz a j) ^ c) := by
  obtain ⟨lbl, hlbl⟩ :=
    exists_label_of_phaseOfAngle m hm zeta hz (fun j => (c : ZMod (m + 1)) * a j)
  exact ⟨lbl, hlbl.trans (phaseOfAngle_natMul zeta hz a c)⟩

end MainTheory.CoprimePowerRecovery
