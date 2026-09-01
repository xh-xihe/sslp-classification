import MainTheory.BoundedClassPower
import MainTheory.NormalizationIsShift

/-!
# Undoing the entrance's normalization on the local phase

`SixQubitSemanticEntrance.normalizedFiniteAngle G T` applies two operations to
the generator's angle vector: the local-`X` flip `Normalize.flip _ T.x0`, and
multiplication by the unit `T.unit` of `ZMod q`.

This file undoes both at the level of local phases.  Conjugating the
normalized phase back by the same `T.x0` returns the *original* phase raised to
the `T.unit`-th power -- the flip is an involution, and the unit survives as an
exponent.  Together with `BoundedClassPower.BoundedClass.of_pow_coprime`, whose
coprimality hypothesis is exactly the statement that `T.unit` is a unit, this
is what lets a bounded representative on the normalized code be read as a
bounded representative on the original one.
-/

namespace MainTheory.UndoNormalization

variable {n d : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.FiniteGateAsPhase
open MainTheory.LocalPhaseConjugation

variable {q : ℕ} [NeZero q]

/-- The natural number representing a unit of `ZMod q`. -/
def unitNat (c : (ZMod q)ˣ) : ℕ := (c : ZMod q).val

theorem natCast_unitNat (c : (ZMod q)ˣ) :
    ((unitNat c : ℕ) : ZMod q) = (c : ZMod q) := by
  simp [unitNat, ZMod.natCast_val, ZMod.cast_id]

/-- The representative of a unit is coprime to the modulus.  This is the
hypothesis consumed by `BoundedClass.of_pow_coprime`. -/
theorem coprime_unitNat (c : (ZMod q)ˣ) : Nat.Coprime (unitNat c) q := by
  refine (ZMod.isUnit_iff_coprime _ q).1 ?_
  rw [natCast_unitNat]
  exact c.isUnit

/-- **Conjugating the normalized phase back gives a power of the original.**

The local-`X` flip is undone by itself; the normalizing unit remains as an
exponent. -/
theorem flipPhase_phaseOfAngle_normalized (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (x0 : SS.BitString n) (c : (ZMod q)ˣ) :
    flipPhase
        (phaseOfAngle zeta hz
          (fun j => (c : ZMod q) * MainTheory.Normalize.flip a x0 j)) x0
      = (phaseOfAngle zeta hz a) ^ (unitNat c) := by
  have hunit :
      (fun j => (c : ZMod q) * MainTheory.Normalize.flip a x0 j)
        = fun j => ((unitNat c : ℕ) : ZMod q)
            * MainTheory.Normalize.flip a x0 j := by
    rw [natCast_unitNat]
  rw [hunit, phaseOfAngle_natMul]
  have hpi :
      (fun j => (phaseOfAngle zeta hz (MainTheory.Normalize.flip a x0) j)
          ^ unitNat c)
        = (phaseOfAngle zeta hz (MainTheory.Normalize.flip a x0))
            ^ (unitNat c) := by
    funext j; simp [Pi.pow_apply]
  rw [hpi, MainTheory.IntrinsicTransport.flipPhase_pow, flipPhase_phaseOfAngle,
    MainTheory.Normalize.flip_flip]

end MainTheory.UndoNormalization
