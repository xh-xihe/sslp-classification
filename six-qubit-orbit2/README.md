# Kernel-checked orbit-2 enumerator theorem

This directory is a self-contained certification of the six-qubit orbit-2
weight-enumerator image. Its Lean package is independent of the repository's
`lean/` dyadic-ladder package and does not require `six-qubit-sslp/`.

For an isometric encoder with logical `IIZZZZ` and full Knill--Laflamme
detection of every Pauli error of weight at most two, Lean proves

```text
A = (1, alpha, 1-alpha, 0, 11+4*alpha, 16-alpha, 3-3*alpha), 0 <= alpha <= 1.
```

Every parameter is attained, including both endpoints, and the distance is
exactly three. This determines the enumerator image, not a classification of
projectors up to local unitaries.

The end-to-end theorem is
[`Orbit2.orbit2_exact_enumerator_image`](lean/Orbit2/Complete.lean).
The encoder assumptions are defined in
[`Orbit2/Encoder.lean`](lean/Orbit2/Encoder.lean).
The proof includes the physical reductions, matrix-to-quartic expansion,
monomial and block regrouping, exact rational Gram certificates, coercivity,
and attainment. No analytic or certificate hypothesis remains in the final
theorem. Its axiom footprint is exactly `propext`, `Classical.choice`, and
`Quot.sound`; no admitted proofs or native computation oracle are used.

## Build and audit

Lean and Mathlib are pinned to v4.27.0. From this directory:

```bash
cd lean
lake update
lake exe cache get
python3 check.py --jobs 2
```

`check.py` checks all 357 modules in dependency order, runs the axiom audits in
`Orbit2.lean`, and rejects admitted proofs or unexpected axiom dependencies.
The bounded worker count limits concurrent finite certificate checks.
`lake build` is also supported; use `check.py` for the audited build.

With an existing compatible Mathlib project, run instead:

```bash
python3 check.py --mathlib-project /absolute/path/to/mathlib-project --jobs 2
```

The reference project is read-only; build artifacts stay in the ignored local
`.lake/` directory. `--incremental` reuses previously checked unchanged modules.

See [lean/README.txt](lean/README.txt) for the proof breakdown and certificate
regeneration commands, and [lean/verification_log.txt](lean/verification_log.txt)
for the completed original dependency check and axiom audit.
[lean/relocation_verification_log.txt](lean/relocation_verification_log.txt)
records the relocation check using unchanged cached modules and a freshly
compiled entry point with the full axiom audit.

## Certificate and exposition

The original exposition, verifier, and certificate data are included alongside
`lean/`. Generated Lean sources suffice for the Lean proof; Python and JSON
are untrusted certificate-production tools, not proof assumptions.

```bash
python3 orbit2_exact_certificate.py
python3 audit_certificate.py
sha256sum -c SHA256SUMS
```

`SHA256SUMS` covers the original exposition/certificate package. The Lean
sources and certification documentation are versioned by Git. The original
`README.txt` describes that exposition package; this file describes the
completed Lean certification.
