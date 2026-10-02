# SSLP Explorer implementation progress — 2026-09-24

This records the first executable slice of the product plan. It is not a
declaration that the 20260924 manuscripts are fully kernel certified.

## Implemented

1. Version selection in `tools/paper_claims.py`, with the historical 20260908
   default preserved. Cross-version refresh cannot inherit coverage. Created
   `results/paper-claims-20260924.json` with 1,652 initially unreviewed entries.
2. `tools/paper_migration.py` and the JSON/Markdown migration reports. The
   reports propose 1,450 identical-statement correspondences, 45 changed
   correspondences, six ambiguous matches and 151 entries without a match.
   Sixty entries have a candidate in the other document. These are review
   candidates, not counts of proved/unproved theorems. Among theorem, lemma,
   proposition, corollary and definition environments: 104 identical,
   12 changed and seven without a candidate.
3. The `tools/explorer` Python API and `tools/sslp_explorer.py` CLI, with
   versioned input, result and evidence contracts. The class-36 JSON supplies
   exact amplitudes, bit order, logical basis, gauge, angles and source hashes.
4. Exact normalization, orthogonality, all 154 weight-at-most-two Pauli
   compressed matrices, 21 moment comparisons and support/fiber checks.
   Floating-point amplitudes are explicitly display-only data. The returned
   circuit describes the six physical phase gates and an abstract encoder.
5. A generated, input-bound Lean certificate: exact equality to the existing
   canonical pair; normalized orthogonal logical words; distance at least
   three; and the physical product of phase gates on every logical
   superposition, assuming `zeta^5=1`. Seven theorem roots are audited against
   the allowed axioms. A new certificate cannot pass merely by importing the
   old code theorem while supplying different amplitudes.
6. Portable bundles with local Lean sources, pinned dependency configuration,
   exact input, generated certificate, logs, evidence and integrity manifest.
   Bundles omit private manuscript text and imported compiled libraries.
7. `apps/sslp-explorer`: the first interactive class-36 workbench. Logical
   input and phase controls, D/D^4, six-gate playback, intermediate leakage,
   all 64 support points and subset sums, exact browser KL computation,
   sign-perturbation diagnostics, experiment export and verification downloads.
   The browser never claims to execute Lean. Historical evidence remains
   visibly scoped to the canonical input. Encoding is still abstract.
8. `tools/export_explorer_site.py` validates the complete bundle and current
   input/proof/tool/manuscript bindings before exporting the Site snapshot.
   Git attributes preserve exact download bytes across platforms.
9. A focused formula review in `sslp-class36-formula-review-20260924.md`, with
   an independent symbolic expansion of all 24 displayed amplitudes. It does
   not automatically promote the new manuscript acceptance ledger.

## Validation so far

- 17 new tests passed, including independent complex-matrix comparison of all
  154 Pauli rows, relative phases, wrong gate parameters, bit-order/input
  validation, migration ambiguity and evidence tampering.
- Existing certification-tool tests: 23 passed, eight opt-in Lean tests
  skipped. Separate actual Lean controls were run for this new case.
- The initial case kernel run passed with seven roots and exactly the permitted
  axiom union `Classical.choice`, `Quot.sound`, `propext`. Its 11 local imports
  were validated by content hashes against their build stamps.
- A deliberately sign-flipped amplitude was rejected by actual Lean: the
  equality check was false and the incomplete proof's `sorryAx` was rejected.
- The bundle integrity check and its exact checker passed from the exported
  directory. In a separate directory all 11 local Lean modules were rebuilt
  from source and the certificate passed (242.484 seconds). Third-party
  dependencies were shared through a junction and content-validated before
  and after. This is same-machine isolated reconstruction, not an independent
  machine/dependency rebuild.
- The updated adapter's kernel run passed in 82.282 seconds with 11
  content-validated cached modules. The isolated rebuild used the preceding
  input-validation snapshot; its exact input, generated certificate and all
  proof source hashes equal those of the updated run. These timings are local
  observations, including dependency validation, not service guarantees.
- Final bundle: `tmp/sslp-explorer/class36-bundle-v2.zip`, 71,100 bytes, 30 files,
  no private manuscripts. Its 29 payload-file hashes passed the integrity check.
  Reproduce it with the commands in `tools/explorer/README.md`.
- Persistent evidence: `results/sslp-explorer/validation-20260924.json`,
  `class36-kernel-evidence-20260924.json` and
  `class36-certificate-20260924.lean` in the same results directory.

## Next implementation work

### Guided research-workbench update (local date 2026-09-24)

The same owner-private Site now has four linked chapters: subset-sum support,
probability moments, coherent phase completion, and proof traceability.
Users can edit six gate numerators modulo five and independently apply exact
quarter turns to all 24 nonzero amplitudes. The circuit, selected-state
amplitudes, support witnesses, KL checker and exported code share this input.
Changing a gate or amplitude invalidates the current computation display.

The probability page exposes a one-dimensional, group-uniform slice, with
22 exact moment equations and an affine-constraint solver deriving t=3/5.
It shows each selected moment's contributing bitstrings and rational weights.
The slice is explicitly separate from the actual amplitude editor and is not
presented as a full LP solver or newly kernel-certified slice theorem.

KL matrix cells now expose every support transition and exact complex term.
Five equation cards connect manuscript labels and hypotheses to seven actual
certificate roots, with source-line excerpts tied to the certificate hash.
Experiment parameter import/export, actual CLI input export, diagnostic report
download, and eight in-memory comparison records are implemented. Import
validation discards status claims and accepts only the bounded v2 schema.

Validation: 18 JS tests and TypeScript checking passed; five independent
Python fixtures compare all 154 matrices each, including a sign flip, logical
basis phase, mixed quarter phases and a changed gate. Every displayed Pauli
term sums to the corresponding independent matrix entry. Probability-slice
normalization, the exact solver, gate preservation, import rejection,
download hashes and all seven source locations were checked. The paper
transcription test and both export-integrity checks passed. The production
build and local HTTP metadata/download checks passed. No browser was available
for visual or click testing; no fresh Lean run was claimed for this update.

Publication details: `results/sslp-explorer/research-workbench-validation-20260924.json`.
The Site source commit is `7e92812abf02db8c05a883627eb8f3f0917c6da2`.
Version 3 was confirmed successfully published by the Sites deployment service.
An authenticated HTTP smoke check of the private publication returned HTTP 401,
including after refreshing the connector-supplied temporary authorization.
No access policy was weakened. Deployed browser behavior therefore remains
unverified; the successful local HTTP checks are recorded separately.
No parent-repository commit/push or manuscript edits were made.

### Focused interface redesign (Site version 4)

In response to feedback about color and clutter, the workspace now uses white,
charcoal and restrained blue accents. A single four-tab navigation replaces
the permanent sidebar and repeated introductory panels. Experiment import,
export and session history moved into a native modal dialog. The circuit is
the primary surface, with physical gate controls alongside it. Logical-state
controls, support amplitudes, the 22 moment constraints, matrix contributions,
and verification downloads are available on demand. The support explorer
initially shows 24 nonzero entries with an explicit option to show all 64 states.
KL matrices appear only after a valid run. Proof statements use compact rows.

The mathematical engine, fixtures and downloadable certificate bytes are
unchanged. All 18 JS tests, TypeScript, production build, the manuscript
transcription test, both export checks, local metadata/download checks and
archive validation passed. The browser runtime again reported no browser;
visual and click validation remain outstanding. No new Lean execution or
whole-manuscript certification is claimed by this interface update.

Source commit: `55d97638dbdf560f182fe983b1187dbec5174a8a`.
Version 4 was confirmed successfully published at the same owner-private URL.
Access policy was preserved. Validation and deployment details are recorded in
`results/sslp-explorer/workspace-redesign-validation-20260924.json`.

### Local open-model assistant backend — 2026-09-25

Implemented `tools/sslp_agent.py` with default local Ollama/Qwen3 14B, an
explicit alternative model selection, and a Chat Completions-compatible
adapter. The optional closed-provider configuration is disabled until its
endpoint/model and environment-key reference are configured. There is no
automatic provider fallback and no closed-model invocation in this milestone.

The registered tools read the actual case, provide bounded scope references,
create a separate candidate with changed gate/quarter phases, check all 154
KL matrices, inspect an exact compression, and optionally invoke the existing
input-bound Lean certificate checker once. Model narratives, tool records and
executor-owned verification statuses are separate. Candidate changes do not
overwrite the original input or transfer proof status. No arbitrary shell,
file path or generated Lean source can be executed by the model.

Live Qwen3 14B validation on the existing 16 GB RTX 4060 Ti:

- The model invoked actual tools to check the canonical case (154/154) and
  a single-amplitude sign flip (134/154; 20 failures), returning the exact
  failing matrix. This run took about 21 seconds and did not run Lean.
- A second task invoked real Lean verification: all seven roots passed and
  the transitive axioms were exactly Classical.choice, Quot.sound and propext.
  The assistant task took about 162 seconds, including about 131 seconds in
  the verifier. Eleven dependency modules were content-validated and reused;
  this is a fresh local certificate check, not an independent-machine rebuild.
- The compatible adapter was also exercised against the local model endpoint:
  a real tool call and answer roundtrip succeeded. This validates the common
  protocol path, not compatibility with every closed vendor API.

Seventeen new protocol/boundary tests and eighteen existing backend/manuscript
tests passed. Both site-data export integrity checks passed. Saved exact
reports were recomputed against their actual inputs. The new kernel job was
exported as a portable bundle and its integrity check passed.

Records and fresh bundle: `results/sslp-explorer/model-backend-20260925/`.
Usage and limits: `tools/explorer/AGENT.md`. This is a local backend/CLI;
the hosted Site was not changed. HTTP jobs, whole-job resource isolation and
cancellation, and connection to the private web workbench remain next steps.
Model prose is not fully evaluated: the first answer omitted inline tool
citations, and one Chinese answer mistranslated mathematical gate order as
gate sequence. Structured tool evidence remains authoritative. The next
evaluation pass should cover citation compliance and mathematical terminology.

### Remaining work

The first private web preview is implemented. Publication and validation
details are recorded in `results/sslp-explorer/web-validation-20260924.json`.
The Site has its own nested Git repository and dedicated Sites remote; no
parent Lean-repository commit or GitHub push was made in this UI milestone.
Do not add that nested checkout as an accidental gitlink in the parent.

Web validation: TypeScript checking and production build passed. Seven JS
tests passed, including all 154 exact coordinate comparisons, input
perturbation, phase action, leakage and download byte integrity. The separate
symbolic manuscript transcription test passed. Local HTTP returned 200,
metadata used the assigned Site origin, and the served ZIP matched its hash.
Dependency audit reported zero vulnerabilities after compatible updates.
The browser runtime reported no available browser, so no browser visual or
click-based validation was performed. No fresh Lean job was run for the UI;
it uses the existing unchanged, input-bound certificate record above.

1. Review the 20260924 statement candidates, prioritizing the seven unmatched
   named entries and 12 changed named statements. Review surrounding prose,
   definitions and the disposition of the recorded errata separately. The
   seven unmatched locators are:
   - `main.tex:cor:six-C5-minimum-length`
   - `supplementary.tex:q2fam:thm:inclusions`
   - `supplementary.tex:thm:main-result-I`
   - `supplementary.tex:thm:main-result-II`
   - `supplementary.tex:thm:main-result-III`
   - `supplementary.tex:thm:main-result-IV`
   - `supplementary.tex:cor:main-order-five-minimum-length`
2. Migrate the complete acceptance suite, named-results map and prose/errata
   records to explicit release/version selection. The old default acceptance
   suite remains historical and is not evidence for the new manuscripts.
3. Add an isolated Lean job service with limits and input-bound evidence,
   connect it to the workbench, and validate on an independent machine.
   The current web preview runs exact JS diagnostics and supplies local
   verification downloads; it has no hosted Lean job executor yet.
4. Add exact LP adaptation, enumerator display, class 7 and the exclusion
   example. Their results must have distinct proof scopes.
5. Add a gate-level encoder, certify its encoding map and logical phase
   convention, then implement the Appendix F fitting workflow and Agent tools.

The current case certificate does not prove minimal gate order, global
classification, a gate-level encoder or manuscript-wide coverage. Independent
machine validation with independently obtained dependencies remains a release
task; same-machine source reconstruction with checked dependency reuse is
reported as such.

Run instructions and API contracts: `tools/explorer/README.md`.

## 2026-09-25: local task service and workbench connection

The local Qwen/Lean backend now has a loopback HTTP companion, with pairing,
fixed input snapshots, a serial queue, persisted task records, status polling,
cancellation, whole-task timeout, Windows worker-tree limits and allowlisted
artifact downloads. The workbench's separate **研究助手** dialog connects to
that API. Models default to local Qwen; the disabled closed-provider slot
remains available for explicit operator configuration and user selection.

The service uses port 8766 because the existing NV-ODMR application occupies
8765. That application was left running. Start instructions and exact limits
are in `tools/explorer/AGENT.md`. Connection codes stay in page memory and
rotate with the service; they are not vendor API keys.

Validation records: `results/sslp-explorer/job-service-20260925/README.md`.
Real Qwen negative-case execution, direct Lean execution and active Lean
cancellation passed. Regression totals are 46 Python and 23 JavaScript tests.
The initial five-round assistant run exhausted its budget; six rounds permit
the five tool calls plus a final cited explanation, while remaining bounded.

This completes the local companion portion of task 3 above. Shared remote
compute, browser interaction QA and independent-machine validation remain.
The Site still uses the visitor's computer for live jobs; publishing the UI
does not deploy Lean or a GPU to Sites. No additional manuscript-wide
formalization or acceptance claim follows from this product increment.

## 2026-09-26: portable reviewer kit and fresh Linux reproduction

Site version 6 adds a reviewer kit with the unchanged class 36 verification
ZIP, a standalone Python launcher, instructions and checksums. The launcher
verifies safe extraction and file integrity, fetches exact dependency commits,
checks prerequisites and records fresh input-bound Lean verification. A real
Linux setup exposed missing release tags in shallow dependency checkouts;
pinned version tags are now fetched and checked against their manifest commits.

The final WSL2 Ubuntu run used a fresh Lean 4.27.0 installation, Python virtual
environment and dependency checkouts with official mathlib caches. It rebuilt
all 11 project proof modules from zero local artifacts/stamps and checked all
seven certificate roots in 105.531 seconds. Input, proof sources and normalized
certificate text match the Windows evidence. The transitive axioms are exactly
Classical.choice, Quot.sound and propext. This is the same physical Windows
computer running an isolated Linux test; independent-machine validation remains
open. Mathlib was obtained from its official cache, not rebuilt from source.
The first successful native run lost temporary records after WSL exit; the
final run repeated verification and archived its records before exiting.

A real Windows negative Lean job also confirmed a reporting fix: failed proofs
retain report/evidence artifacts and do not produce a successful verification
ZIP. Regression totals are now 56 Python and 23 JavaScript tests; TypeScript,
production build, three export checks and local download integrity checks pass.
The user reported usable page functions. Automated browser interaction remains
unverified because no browser runtime was available.

Records: `results/sslp-explorer/reproduction-20260926/README.md`.
Reproduction instructions: `tools/explorer/REPRODUCE.md`.
The Linux environment test is finished. The Windows application and local
companion remain the user's normal workflow. No manuscripts or certificate-bound
proof sources were changed, and no whole-manuscript certification claim follows
from this product increment. The parent repository was not committed or pushed;
the nested Site repository was published with owner-only access.

## 2026-09-26: version-bound manuscript acceptance and priority review

`tools/verify.py --paper-version 20260924` now selects the release's claims,
orbit manifest, named-results document, prose and errata records consistently.
The audit includes both covered claim declarations and covered prose roots.
Name checks use the selected ledger; logs are separated by release. The
historical default remains 20260908. Shared no-go/moment data must match the
selected manifest exactly. Changes to either manuscript invalidate semantic
reviews, including unchanged statements whose context could have changed.

The first 19 priority named statements were read with their surrounding
definitions and the relevant Lean statements: 12 reviewed correspondences,
7 partial. The Singleton display is separately partial. The whole ledger is
12 covered, 8 partial and 1632 unreviewed; full prose review remains pending.
This was a single-agent semantic review, not the historical two-agent method.

The four new supplementary main-result statements and the family-inclusion
statement have existing proofs. Partial obligations include the arbitrary-
subspace converse bridge, combined binary-pivot witness correspondence,
updated classification definitions, the expanded orbit-45 statement and both
minimum-length corollaries. The old existence-status erratum for classes 1--4
is fixed in the new text; the other three historical issues remain recorded.
Existing unitary diagonalization foundations can support the minimum-length
work, but single-subsystem detection must not be substituted for distance-three
KL when completing its transport and ancilla-padding arguments.

Actual Windows checks passed: 14,088 dependency modules content-validated with
zero rebuilds; 1,452 kernel audit roots with only the standard three axioms;
all 66 current table rows and three rejected numeric-column mutations. The
partial acceptance run deliberately reports failure on claims, prose and
errata completeness. Unit tests: 35 acceptance/release passes and eight opt-in
skips, plus 56 Explorer passes; four migration tests rerun after context-change
invalidation. No Lean proof source or TeX was changed. No Site or GitHub push
was made in this increment.

Usage and proof queue: `notes/paper-acceptance-20260924.md`.
Archived evidence: `results/paper-acceptance-20260924/README.md`.
