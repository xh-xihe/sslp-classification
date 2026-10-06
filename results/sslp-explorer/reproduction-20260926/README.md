# Reviewer reproduction validation — 2026-09-26

The published class 36 verification bundle passed a fresh Linux reproduction
under WSL2 Ubuntu on the existing Windows computer. All 11 local proof modules
were rebuilt with zero prior local artifacts or stamps; all seven certificate
roots passed. Kernel verification took 105.531 seconds. Transitive axioms were
exactly `Classical.choice`, `Quot.sound` and `propext`.

This is cross-platform validation on the same physical computer, not validation
on a second machine. The isolated environment used a fresh official Lean 4.27.0
installation, a fresh Python 3.12 virtual environment, nine dependency source
checkouts at the manifest's exact commits, and the official mathlib cache.
Mathlib itself was not rebuilt from source. No Windows compiled dependencies
were reused. Windows, the editor and the local companion remained in place.

The input hash and all 11 proof-source hashes match the published Windows
evidence. Generated certificate text also matches after newline normalization;
its raw file hash can differ between Windows and Linux. See
[cross-platform-summary.json](cross-platform-summary.json),
[linux-reproduction.json](linux-reproduction.json) and
[linux-kernel.log](linux-kernel.log). The summary hashes all nine archived
Linux records. The first native-filesystem attempt completed successfully but
its temporary files were unavailable after WSL exited; the final run repeated
the rebuild and archived these records before exiting.

## Product changes and validation

- Added a standalone reviewer kit containing the unchanged verification ZIP,
  a standard-library reproduction launcher, instructions and SHA-256 checksums.
  The launcher checks extraction integrity, fetches pinned dependencies,
  diagnoses prerequisites and runs a fresh input-bound Lean check.
- Real Linux setup exposed a missing release-tag issue in shallow dependency
  fetching. The launcher now fetches pinned version tags and checks that they
  resolve to the manifest commit before downloading the official cache.
- Fixed failed Lean jobs losing their report when successful-bundle export
  rejected the failed evidence. A real Windows negative control (one amplitude
  sign flip) completed with exact KL and kernel checks failed, retained its
  report and published no successful verification ZIP. See
  [negative-job.json](negative-job.json), [negative-report.json](negative-report.json)
  and [negative-evidence.json](negative-evidence.json).
- Validation passed: 56 Python tests, 23 JavaScript tests, TypeScript checking,
  production build, all three data/export consistency checks and download-byte
  checks. Browser automation was unavailable; the user's usability feedback is
  recorded separately from automated verification.
- Site version 6 was published successfully with owner-only access. See
  [publication.json](publication.json) for the commit, deployment and hashes.

Site: <https://sslp-explorer-class36.xh-xihe.chatgpt.site>

Original verification ZIP SHA-256:
`88623d7bc2b7824adab97c24dafacbb7acd5c2b28d4e9e444d09e0812c6a8d92`

Reviewer kit SHA-256:
`da5a728c38de62073642ac36c5d7cd30ba64b7d2ac25202e53d1a0eb80abd252`

## Scope

The certificate covers the supplied canonical class 36 pair, normalization,
orthogonality, distance at least three and physical phase action on logical
superpositions under the stated fifth-root assumption. This increment adds no
manuscript-wide formalization, classification-exhaustiveness proof, minimal
gate-order proof or gate-level encoder proof. Independent-machine validation
and browser interaction QA remain open.
