# Shared Pauli and Knill--Laflamme infrastructure

[SS.lean](../SS.lean) is the shared entry point. The library provides physical
bitstring/state conventions, Pauli errors, KL detection and enumerator identities
used by the orbit and general-theory libraries.

The full library participates in the serial build and source checks. See
[architecture](../docs/architecture.md), [proof modules](../docs/proof-modules.md)
and [reproduction](../docs/reproduce.md) for its consumers and commands.
