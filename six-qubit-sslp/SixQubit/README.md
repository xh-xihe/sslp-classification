# Six-qubit classification

The entry point is [SixQubit.lean](../SixQubit.lean). This library contains
orbit-specific no-go proofs, exact realizations, enumerator arguments and the
finite data used by the physical bridges in `MainTheory/`.

The classification has 66 moment orbits: 51 excluded and 15 realized. Thirteen
nonempty enumerator images are settled, including orbits 2 and 3; the full
images of orbits 1 and 4 remain open. These are moment-orbit statements, not
a claim that the 15 records are disjoint local-unitary code classes.

`Generated/` stores certificate transcriptions with exact manifests where
applicable. Start with [proof entry points](../docs/proof-index.md) and
[modules by topic](../docs/proof-modules.md). The complete actual-encoder
orbit-2/3 image statements live in `MainTheory/`.

[Audit.lean](Audit.lean) and the other audit entry points are included in the
public proof checks described in [reproduce](../docs/reproduce.md).
