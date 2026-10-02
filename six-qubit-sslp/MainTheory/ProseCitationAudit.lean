import MainTheory.CitedFamilyFullKL
import MainTheory.Orbit21WalshRank
import MainTheory.QECCSmithBridge

/-!
# Review citations outside the main audit closure

The axiom gate in `tools/verify.py` takes, as roots, every declaration that a
covered ledger entry or a covered assertion of a prose-review record cites. It
imports only the modules its audit files import. The modules below are built,
but no other audit file imports them, so the theorems the review records cite
from them would be unreachable and the gate would stop with "Missing kernel
declaration". This file brings them into the closure.

- `CitedFamilyFullKL`, `Orbit21WalshRank`: cited by
  `results/prose-review-20260908.json`.
- `QECCSmithBridge`: identifies QECC's cokernel-exponent `finalSmithInvariant`
  and `smithBeta` with MainTheory's Smith last factor and `betaOf`; cited by
  the 20260929 ledger.

A clean report for each reads `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms MainTheory.CitedFamilyFullKL.hasDistance
#print axioms MainTheory.Orbit21WalshRank.kernel_dimension
#print axioms MainTheory.Orbit21WalshRank.rank_six
#print axioms MainTheory.QECCSmithBridge.finalSmithInvariant_eq_inverseDenominator
#print axioms MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor
#print axioms MainTheory.QECCSmithBridge.nonempty_smithWitness
#print axioms MainTheory.QECCSmithBridge.smithBeta_betaExact
#print axioms MainTheory.QECCSmithBridge.smithBeta_eq_betaOf
