# Research workbench handoff — 2026-09-28

User direction: build a practical research workbench, not a paper-specific demo. Product UI
must be English; conversation with the user remains Chinese. Keep native Windows execution.

Implemented and privately published in `apps/sslp-explorer` (independent Site repository):

- Project sidebar and Code / Circuit / Checks / Compare / Notebook / Certificates tools.
- General sparse exact input: n=1–6, K=1–4, target d<=3, phase modulus 2–64,
  eight integer coordinates in Z[sqrt(2),sqrt(3),i], common scale 1/sqrt(denominator).
- Exact normalization and KL matrices, term inspection, diagonal-action support test,
  phase-layer playback, logical-state preview, support and encoding-matrix inspection.
- D1 project persistence keyed by platform user ID, explicit save, revision conflicts,
  notes and up to 20 input snapshots; comparison recomputes from saved inputs.
- Project/code/report export, legacy code-instance and experiment imports. Imported proof
  statuses and credentials are stripped. Session storage is temporary draft recovery only.
- English local assistant UI, current-input adapter binding, preserved model/exact/Lean jobs.
  Parent `tools/sslp_service.py` connection page and assistant prompt are now English.
- Canonical evidence downloads are unchanged and retain their verified hashes.

Current Lean adapter is still the canonical six-qubit construction. Generic exact checks
are not generic Lean certification. No manuscript or proof source was changed in this turn.
K=1 KL behavior and the Singleton qualification are explicitly distinguished in results.

Validation: TypeScript and production Worker build passed; 30 frontend mathematical/input
tests passed, including independent Python fixtures and a tensor-Pauli oracle. 28 Python
assistant/job tests passed. Local Worker API integration passed authentication, ownership,
schema rejection, save/reload, conflict handling and forged-proof-status stripping.
The local HTML returned 200 with English metadata. Browser automation could not initialize
(`Invalid browser service environment`), so visual and click-through QA remain unverified.

Final Site source commit: `6283a2f359525279de04afbbe2611f89b11a9a51`.
Project: `appgprj_6ab5a69b70a0819191ccacb377d3ca8c`.
Version: `appgprj_6ab5a69b70a0819191ccacb377d3ca8c~appgver_0aaf6d8f7b748191adf068859a06d82b`.
Deployment: `appgdep_6abaea1a002c81918361a569b17b0d66`, succeeded.
URL: https://sslp-explorer-class36.xh-xihe.chatgpt.site
Owner-only audience retained. Parent GitHub repository was not pushed.

Windows notes: Node is `tmp/web-runtime/node-v24.21.0-win-x64/node.exe`.
The Sites build helper has a Windows npm-shim problem; native `npm run build` succeeded.
The Sites workflow saved/pushed source but its Bash packager failed on Windows paths.
Used the bundled `prepare-site-build.cjs` with a checked fresh staging path and native
Windows `tar.exe`, preserving manifest and generated Drizzle migration. No Linux switch.
Final archive: `tmp/sslp-workbench-20260928-final.tar.gz`.
The owned local Worker preview on port 5174 was stopped after testing.

## Assistant acceptance follow-up — 2026-10-01

The user reported that the first nine manual acceptance items passed. Their
assistant requests `2f31bf7c34434a8f9004ef7e2eed07e8` and
`7d747779450f4f6d8d307f49982edbe8` timed out after 120 seconds on the first
model call, before any tool ran. Ollama logs show other long chat-completion
requests occupying the shared server; the workbench request was waiting for
model availability. The 600-second companion budget is separate from the
120-second per-provider-request timeout. No model/hardware change was needed.

Native Windows / Qwen3 14B checks exposed additional model argument errors:
the old tool description elicited quarter_turns=1 and zero gate angles for a
request to negate an amplitude while preserving the gate. Candidate creation
now preserves gate exponents and requested residues by default; optional
replacement angles remain available. Descriptions explicitly distinguish i
from -1. Matrix inspection can select the first failed Pauli without guessed
masks, and supplies exact matrix strings plus computed KL defects. A bounded
single explanation revision requests missing citations/no-Lean disclosure.
This does not establish arbitrary model prose correctness.

Timeout errors now give the per-request limit and actionable Ollama guidance.
Failed model attempts record their round and elapsed time, and reports say
whether actual verification records were retained. No automatic provider
fallback, model unload, daemon restart, or extension of execution limits was
introduced. New workers load these changes without restarting the companion.
No hosted frontend, manuscript, Lean source or parent GitHub push changed.

Validation: 33 assistant/worker/API/process-boundary regression tests passed.
Final live tests used the same companion HTTP API as the workbench, the user's
exact input hash `668c069a091e54e008405755efdcd651fc66db8fcb20a462b5f39cca55506059`,
and prompt version `sslp.assistant.class36.v5-en`:

- Job `11dbd1cf882143b694d029c7ca7ab071`: 17.625 seconds; actual get_case and
  check_exact; normalization/orthogonality, 154/154 KL checks, requested gate
  support pass; actual citations and no Lean claim.
- Job `09449356b416429bae10b2f5d45ade09`: 28.984 seconds; original 154/154,
  candidate 136/154. Candidate compared field-by-field against the submitted
  input: only psi_0's 000000 amplitude was negated (and candidate ID updated).
  Gate and normalization preserved. Actual inspection returns X1X6 with matrix
  [[0,1/5],[1/5,0]], violating the zero-off-diagonal condition. The final model
  explanation accurately describes this failure and explicitly says Lean not
  run. Both final explanations were inspected; this is not a formal proof of
  model prose or a reliability guarantee for future requests.

Raw final requests, reports, candidate, jobs and structured-check summary:
`artifacts/workbench-acceptance-20260929/assistant-rerun-20261001/verified-153857/`.
Earlier diagnostic reports remain in the parent directory and tmp; some contain
known model mistakes and must not be treated as the final acceptance results.
The user can reopen Assistant to refresh history and inspect the two new jobs;
old failed jobs remain unchanged. No browser click-through QA was claimed.

## Input-derived research certificates - 2026-10-01

The user accepted the existing functional workbench and authorized the next
sequence: archive that baseline, implement generic certification, connect new
inputs and certificate replay, then generalize the assistant. This milestone
implements that sequence within the bounded explicit-code representation.
The earlier canonical-only limitation above is now historical.

Before changes, `artifacts/workbench-release-20261001/` captured the accepted
frontend commit, backend/proof sources and acceptance evidence with SHA-256
hashes. Acceptance is attributed to the user's report; unreported browser and
device details were not invented.

New `SS/ExactAmplitude.lean` and `SS/ExactCode.lean` connect exact integer
amplitudes to actual complex states, inner products, Pauli distance and phase
action. `tools/explorer/research.py` generates a certificate from the submitted
coordinates, with no canonical-code equality requirement. Finite obligations
use kernel `decide`; the three roots are normalization/orthogonality, the
requested distance lower bound, and the diagonal physical phase layer on
arbitrary logical superpositions under `zeta^q = 1`. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed by the transitive axiom audit.

Input bounds: n=1 through 6, K=1 through min(4,2^n), d=1 through min(3,n+1),
q=2 through 64, denominator=1 through 1,000,000, and eight integer amplitude
coordinates bounded by +/-1,000,000 with common scale 1/sqrt(denominator).
This is a bounded adapter for new explicit codes, not arbitrary Lean source
execution. Gate support checks are sufficient for a diagonal action in the
supplied logical basis. K=1 retains its rank-one KL qualification. Exact
distance, minimal order, synthesized encoders, classification completeness
and full-manuscript certification remain outside these case certificates.
Manuscripts and unrelated pending formalization changes were not edited.

The local API, direct exact/Lean jobs, portable bundles and Qwen assistant now
accept `sslp.research-code.v1`. Tool parameters and explanations use the
actual n, K, d, denominator and gate. Candidates preserve the original input
and gate unless an explicit edit requests otherwise. Existing canonical
inputs, saved projects and job history remain usable. The updated companion
advertises capabilities; the workbench falls back to the legacy adapter when
connected to an older companion.

Verification and evidence in `artifacts/research-kernel-20261001/`:

- `four-qubit-pass/evidence.json`: kernel passed, all three roots audited;
  102.765 seconds including dependency checks and builds.
- `four-qubit-reject/evidence.json`: exact KL failed (9/13), and Lean rejected
  the false finite KL obligation. No successful certificate was exported.
- `live-lean-job.json` and `live-lean-report.json`: the four-qubit sign-flip
  candidate passed through the real companion API; job
  `f76d6b63ff274ee49f0ea1acf9746c55` produced a downloadable verification ZIP.
- `additional-kernel-checks.json` and corresponding sources/logs: generic
  six-qubit, K=3 complex and K=1 rank-one inputs all passed actual Lean
  checks and root axiom audits. These are kernel smoke checks, distinct from
  the complete dependency-fingerprinted verification reports.
- `four-qubit-bundle.zip` passed integrity checking. Its extracted source
  rebuilt all 12 local modules and passed in
  `four-qubit-bundle/replay-run/evidence.json` (178.078 seconds). This was a
  separate directory on the same Windows machine, using a junction to the
  pinned external dependencies with content validation. It was not a second
  machine test. The earlier `fresh-run` setup failure remains recorded; the
  successful `replay-run` is the final replay evidence.
- `assistant-report.json`: actual Qwen3 14B job
  `c694feff6c494f3b8a07fea3ab877f04` read the four-qubit input, negated only
  psi_0's 0000 amplitude and compared both inputs using exact tools. Both
  passed 13/13 KL checks, and the model accurately reported no failure and
  no Lean invocation. The candidate was compared field-by-field with the
  submitted input. This one inspected run is not a guarantee of model prose.
- 62 Python regression tests and 30 frontend tests passed. TypeScript and
  the native Windows production build passed. Local production HTML returned
  HTTP 200. Browser automation returned no available browser, so this update
  has API/build/kernel validation but no new visual or click-through QA.

Privately published with owner-only audience retained:

- URL: https://sslp-explorer-class36.xh-xihe.chatgpt.site
- Frontend source commit: `123948bbb0715168aebe196b2d82dcd742e7fba3`.
- Version: `appgprj_6ab5a69b70a0819191ccacb377d3ca8c~appgver_ce80fbb691588191b6bfabd1aa9a9315`.
- Deployment: `appgdep_6abed5efd0d4819189d42f8b577ff8dc`, succeeded.
- Build archive: `tmp/sslp-workbench-research-20261001.tar.gz`.

The companion was upgraded with historical jobs preserved. Refresh the hosted
page, open `http://127.0.0.1:8766/connect`, and copy the new connection code
into Assistant in the existing workbench tab. Import the four-qubit acceptance
JSON, select **Run Lean verification**, inspect **Kernel check passed**, and
download the verification bundle. Direct checks do not call a model. Parent
GitHub changes were not pushed. Execution remained native Windows.

## UI and visualization upgrade - completed 2026-10-02

The user requested a complete visual and interaction upgrade, with the current
agent configuration archived first. `artifacts/workbench-ui-baseline-20261001/`
contains the prior frontend source ZIP and an agent/settings source ZIP.
`manifest.json` records the frontend commit, default provider configuration,
public runtime provider settings, execution limits and file/archive SHA-256
hashes. Credentials and job-history contents were excluded. Baseline hashes
were rechecked after the UI implementation; backend agent sources and model
configuration remained identical.

The English workbench now has Pearl and Midnight themes, an overview of the
current input, searchable tools (Ctrl K), save/run shortcuts, focus mode,
collapsible project navigation and inspector, and a mobile project drawer.
The sidebar displays real input snapshots. Theme preferences are local display
settings; account project and temporary draft formats remain compatible.

New input-derived visualizations include selectable probability bars, complex
amplitude planes, support residues, a gate-by-gate phase trajectory, and a
selectable Pauli check map with operator filtering. Circuit playback supports
pause, reset and stepping, and shows the current encoded state, probability
and numerical code-space leakage. Approximate displays never establish exact
or kernel status. Zero-amplitude phase is labelled undefined, and the phase
trajectory uses the existing leftmost-bit/qubit-one convention.

Compute and assistant now uses separate request/evidence columns, distinct
direct exact/Lean actions, model presets, actual job phase and elapsed time,
input-hash binding, compact verification records and expandable tool traces.
The main inspector only displays a kernel record when its input hash matches
the current research input. Unapplied JSON definitions cannot be submitted
through the companion. Certificates lead with fresh input-bound verification;
the canonical example is clearly archived reference material. Notebook tools
include an experiment template and character count. Reduced-motion preferences,
keyboard focus indicators and a skip link are supported.

Validation: 33 frontend tests passed, including complex radical/phase previews,
unscaled invalid norms, leftmost-bit phase trajectories and agreement with
exact canonical norms. TypeScript and the native Windows production build
passed. Thirty static React render checks covered six updated modules for
four-qubit positive/negative, six-qubit, rank-one and complex K=3 inputs, with
no nonfinite display values. Production HTML and seven assets returned HTTP
200; hosting and migration content matched the source build.

Sites generated a new production screenshot. The Pearl desktop screenshot was
downloaded and visually reviewed: the shell, title, actions, tool navigation,
overview metrics and current-input inspector rendered correctly. The service
screenshot has no signed-in account identity, so its project-service sign-in
notice is expected. Browser inventory was empty, so no new click-through,
Midnight screenshot or mobile visual acceptance was claimed. Static render
checks are not browser interaction tests.

Published source: `f317bd21f1931bc289e233522720094b128f9137`.
Version: `appgprj_6ab5a69b70a0819191ccacb377d3ca8c~appgver_7304925701248191982cbc4e2589fd49`.
Deployment: `appgdep_6abf39bea4688191aceb4662b78797ac`, succeeded.
URL: https://sslp-explorer-class36.xh-xihe.chatgpt.site
Owner-only audience was verified after publication. The initial archive used
an unsupported entrypoint layout and was rejected before saving. The corrected
`tmp/sslp-workbench-ui-20261001-site.tar.gz` follows the established dist/
archive layout, includes hosting/migrations, and was published successfully.

Evidence: `artifacts/workbench-ui-upgrade-20261001/`, including the deployment
record, production HTTP/assets check, static module renders and deployed
screenshot. The owned preview was stopped. The existing native Windows
companion remained running; no model or companion restart was performed.
Page refresh requires re-pairing because compute credentials remain in page
memory. No manuscript, Lean theorem, parent GitHub push or project database
migration changed in this UI task.
