import MainTheory.CitedFamilyFullKL
import MainTheory.Orbit21WalshRank

/-!
# Prose-review citations outside the main audit closure

The axiom gate in `tools/verify.py` takes, as roots, every declaration that a
covered assertion of a prose-review record cites. It imports only the modules
its audit files import. The two modules below are built, but no audit file
imported them, so the theorems that `results/prose-review-20260908.json` cites
from them were unreachable and the gate stopped with "Missing kernel
declaration". This file brings them into the closure.

A clean report for each reads `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms MainTheory.CitedFamilyFullKL.hasDistance
#print axioms MainTheory.Orbit21WalshRank.kernel_dimension
#print axioms MainTheory.Orbit21WalshRank.rank_six
