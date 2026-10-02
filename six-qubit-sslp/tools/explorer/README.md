# SSLP Workbench: local compute and certification

The local Python API and CLI support both supplied research codes and the
canonical class-36 instance from the 20260924 manuscript. The browser workbench
provides interactive exact diagnostics, input-derived Lean verification and
certificate downloads. Its loopback companion runs jobs on the user's computer.
General LP tooling, shared remote execution and a gate-level encoder remain work.

The local model-backed assistant is available through `tools/sslp_agent.py`:
default Ollama/Qwen3, optional compatible providers, registered exact tools,
and an explicitly enabled input-bound Lean tool. See [AGENT.md](AGENT.md).
Start `python tools/sslp_service.py` and open `http://127.0.0.1:8766/connect`.
The hosted workbench then uses this visitor's computer for model/Lean tasks.

For a fresh setup outside the research repository, use the reviewer kit and
[reproduction guide](REPRODUCE.md). The standalone `tools/sslp_reproduce.py`
supports hash-checked extraction, pinned dependency fetching, environment
diagnostics and fresh verification reports. It does not install system tools
or assume that a new directory means a different physical machine.

## Run

From the repository root, with the pinned Lean environment available:

```text
python tools/paper_claims.py check --paper-version 20260924
python tools/paper_migration.py --paper-version 20260924 --previous-version 20260908
python tools/sslp_explorer.py verify results/sslp-explorer/class36-20260924.json --lean --output tmp/sslp-explorer/my-run
python tools/sslp_explorer.py bundle tmp/sslp-explorer/my-run --output tmp/sslp-explorer/my-bundle
python tools/sslp_explorer.py check-bundle tmp/sslp-explorer/my-bundle
```

Use a fresh output directory for each run. Omit `--lean` for the explicitly
labelled exact-Python diagnostic. `bundle` creates both a directory and a ZIP.
Bundle integrity checking does not rerun Lean; execute its README instructions
to obtain fresh evidence. Dependency setup and validation can dominate a small
certificate's runtime. `--timeout` applies to that certificate invocation.

## Shared API and data contracts

| Function | Input | Output |
| --- | --- | --- |
| `explorer.class36.example()` | none | `sslp.code-instance.v1` |
| `explorer.class36.validate(data)` | code instance | validated exact amplitude maps, or error |
| `explorer.class36.exact_checks(data)` | code instance | `sslp.exact-check.v1` |
| `explorer.research.validate(data)` | `sslp.research-code.v1` | validated exact amplitude maps, or error |
| `explorer.research.exact_checks(data)` | research code | `sslp.exact-check.v1` |
| `sslp_explorer.verify_case(data, output, lean=True)` | code instance, fresh directory | `sslp.evidence.v1` and artifacts |
| `sslp_explorer.export_bundle(run, output)` | completed run, fresh directory | ZIP with `sslp.bundle.v1` manifest |

### Supplied research codes

The `sslp.research-code.v1` adapter accepts exactly `schema`, `n`, `k`,
`distance`, `denominator`, `q`, `angles` and `words`. Its current bounds are
1 <= n <= 6, 1 <= K <= min(4, 2^n), 1 <= d <= min(3, n+1),
1 <= denominator <= 1,000,000 and 2 <= q <= 64. Angle exponents are integers
from 0 through q-1. Each word has 1 through 2^n unique basis-string entries;
each entry has `bits` and eight integer `coordinates`, bounded by +/-1,000,000.
These are input limits, not a promise that every input completes within the
job budget. Floating-point values and imported proof-status fields are rejected.

The coordinate basis is `(1, sqrt(2), sqrt(3), sqrt(6), i, i*sqrt(2),
i*sqrt(3), i*sqrt(6))`, with common scale `1/sqrt(denominator)`.
The leftmost character of a basis string is qubit 1 and integer-mask bit 0.
Full K-by-K Gram and Pauli compression matrices are checked; gate residues
are computed from each word's actual nonzero support.

For example, from the repository root:

```text
python tools/sslp_explorer.py verify artifacts/workbench-acceptance-20260929/01-pass-four-qubit.json --lean --output tmp/research-four-qubit
python tools/sslp_explorer.py bundle tmp/research-four-qubit --output tmp/research-four-qubit-bundle
python tools/sslp_explorer.py check-bundle tmp/research-four-qubit-bundle
```

The generated Lean source depends on `SS.ExactAmplitude` and `SS.ExactCode`,
without a canonical-code equality requirement. Finite integer obligations
are proved with kernel `decide` and transported to the existing complex
Hilbert-space semantics. Its three audited roots establish:

- Normalization and orthogonality of the supplied codewords.
- `SS.HasDistance states d`: scalar Pauli compression for every weight below d.
- The supplied diagonal physical phase layer's action on every logical
  superposition, under the explicit assumption `zeta^q = 1`.

The gate test requires each supplied basis word to have a single support
residue. Failure does not exclude a different logical basis or a non-diagonal
logical action. K=1 certifies a rank-one KL statement; it does not establish
nontrivial logical information or an unrestricted Singleton bound. These
certificates do not prove exact distance, minimal gate order, encoder synthesis,
classification exhaustiveness or the full manuscript.

Direct checks and assistant tools accept this schema. After updating the
companion, restart it and reconnect; `/v1/status` advertises the available
research-code capabilities. In the workbench, import a code, open **Assistant**,
then select **Run Lean verification**. Only a successful job offers
**Download verification bundle**. A completed task is not necessarily a passed
proof; inspect **Kernel check passed** and the input hash.

### Legacy canonical adapter

The `sslp.code-instance.v1` adapter supports six qubits, two logical words, distance lower bound three
and q=5. Bits are labelled left to right as qubits 1–6, with the leftmost bit
occupying integer-mask bit 0. Each amplitude has eight integer coordinates
in `(1, sqrt(2), sqrt(3), sqrt(6), i, i*sqrt(2), i*sqrt(3), i*sqrt(6))`,
multiplied by `1/(2*sqrt(30))`. Floating-point previews are separate fields.

The gate includes its angle vector and both logical residues. The canonical
gauge `(1,1,1,1,2,3)` uses residues `(0,4)`; the table representative
`(1,1,1,2,2,4)` is separate metadata. Explicit logical phase conventions matter.

The exact report contains both normalizations and orthogonality, 21 moment
comparisons, the full 154 Hermitian Pauli compressed matrices, fibers and
support checks. Coordinates of compressed matrices and probabilities are
divided by 120. It includes a symbolic six-gate transversal layer and an
abstract encoding isometry; no synthesized encoder is claimed.

## Legacy Lean certificate and shared provenance

For the legacy schema, the generated certificate uses the supplied coordinates.
It proves they equal the canonical Lean pair, obtains normalization,
orthogonality and `SS.HasDistance ... 3`, and proves the physical product
of single-qubit phase gates acts correctly on every logical superposition,
assuming `zeta^5 = 1`. The certificate checks its seven proof roots against
the project's allowed transitive axioms.

This legacy proof adapter is specific to the documented canonical basis.
A different valid code, or a different logical phase convention, may pass
the exact diagnostic and fail that adapter. A failed certificate is not a
nonexistence proof. Physical/logical minimal order, the classification and
the whole manuscript are outside this case certificate's scope.

Each kernel job validates the entire local dependency closure and external
artifact context before and after Lean, using the established build-driver
hashing and cache rules. It records source, tool, configuration, input and
certificate hashes. Successful old logs are never used to mark a new input
as checked. Bundles contain local proof sources and dependency pins, but no
private manuscript text or imported compiled dependencies.

## Manuscript migration

The historical default of `tools/paper_claims.py` remains 20260908; callers
must select 20260924 explicitly. Cross-version snapshotting never transfers
reviews. The migration report proposes matches by labels or statement hashes,
including moves between main and supplementary. Matching text is still
subject to definition, hypothesis and context review. Unlabelled duplicate
statements remain ambiguous. Named locators are stable; unlabelled content
keys change when the statement changes. Prose requires separate review.

The full acceptance entry point now accepts an explicit version:
`python tools/verify.py --paper-version 20260924`. Its historical default remains
20260908. Release-bound ledgers, orbit data, named-result reports, prose and
errata records are checked together; logs are under `tmp/verification/20260924`.
The new release remains incomplete. Its first 19 priority named statements
have review records, but the remaining displays and prose are not covered.
See `notes/paper-acceptance-20260924.md` for commands and scope.

Changes to either manuscript invalidate semantic reviews, including unchanged
statements that could depend on changed context. Refreshing a ledger is not a
replacement for re-review. Published example bundles retain their own pinned
tool snapshots; changing the repository's acceptance tools does not extend an
old example certificate to the new manuscript release.
