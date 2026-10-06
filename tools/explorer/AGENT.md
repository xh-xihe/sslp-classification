# Local model-backed SSLP assistant

The first assistant backend is executable through `tools/sslp_agent.py`.
It defaults to the locally installed Qwen3 14B served by Ollama and also has a
Chat Completions-compatible adapter. A closed-provider configuration slot is
disabled until an operator supplies the endpoint/model and enables it. No
closed-model credentials are included, and no automatic fallback occurs.

The hosted workbench can connect to this local Python backend through the
loopback companion service. Models and Lean run on the visitor's computer;
this is not a shared remote GPU or Lean deployment. Model download and
inference-server lifecycle remain separate operator actions.

The assistant accepts both `sslp.research-code.v1` and the legacy
`sslp.code-instance.v1`. Research-code tools use the actual input's qubit
count, logical dimension, target distance, amplitude denominator and gate
modulus. The current supported bounds and proof scope are in [README.md](README.md).
Updating the companion and reconnecting enables these capabilities in the
workbench; older companions retain their legacy adapter.

## Connect the workbench

From the repository root, start `python tools/sslp_service.py`, then open
`http://127.0.0.1:8766/connect`. Its connection button opens the private
workbench and removes the connection key from the URL fragment before using
the API. To retain an experiment in an existing tab, copy the connection code
into **Assistant** in that tab. The key stays in page memory, not browser
storage, and rotates whenever the companion restarts. Refreshing the page
requires pairing again. Previously saved tasks remain in the service history.

The browser may request local-network permission. If it refuses the connection,
use the same workbench at `http://localhost:5173` and start the service with
`--site http://localhost:5173`. Do not disable browser protections. For a
custom `--port`, use the connection page's button; code-only manual pairing
uses the default port 8766.

The panel supports model tasks, direct exact checks, direct Lean verification,
status polling, cancellation, recent tasks, input-bound reports and downloads.
Six model rounds and ten tool calls are available per assistant task. Lean is
available to the assistant only when its checkbox is enabled; direct Lean
verification does not depend on a model decision. Submitted inputs are fixed
snapshots: subsequent page edits do not alter running tasks or their evidence.

The default provider remains local Qwen; a configured closed provider must be
selected explicitly. Merely connecting the page does not contact a model.
The service has no endpoint for changing credentials or executing arbitrary
commands or Lean source.

## Companion API and execution limits

- Loopback IPv4 only. Requests require a per-service Bearer key, exact Host,
  and one of the explicit production/local workbench origins. The local
  `/connect` pairing page is deliberately not CORS-readable. No public tunnel
  or site-wide authentication bypass is created.
- `GET /v1/status`; `POST /v1/jobs`; `GET /v1/jobs/<id>`;
  `GET /v1/jobs/<id>/result`; `POST /v1/jobs/<id>/cancel` with `{}`;
  `GET /v1/jobs/<id>/artifacts/<name>`. JSON requests are limited to 2 MB;
  artifact names come from a fixed allowlist.
- Job kinds are `agent`, `exact`, `lean`; all require an exact `input` code
  object. Only `agent` accepts `question`, `provider`, and `allow_lean`.
- One running job, at most four unfinished jobs, 600-second execution budget
  including dependency validation, model calls and packaging. Queue waiting
  does not consume that budget. At most 1000 job records are retained; the
  operator must archive records or choose a new jobs directory at that limit.
- Each task has an independent directory in `tmp/sslp-service/jobs`. Windows
  Job Objects cap the worker tree at 16 processes and 6144 MiB committed
  memory, and terminate its descendants on cancellation/timeout. The worker
  waits for assignment before starting work. POSIX uses process groups and a
  per-process address-space limit; this is not an aggregate POSIX memory cap.
- These are trusted local workers with process limits, **not** a filesystem
  or hostile-code sandbox. The separately running Ollama daemon and its GPU
  memory are outside worker limits; the service closes its model request but
  does not stop the shared daemon. Output size is monitored with a 64 MiB
  threshold; this is not an OS disk quota.
- Cancellation publishes no completed artifacts. `completed` means execution
  returned a report, not that any mathematical claim passed. `timeout`,
  `cancelled`, `failed`, and `interrupted` are not mathematical counterexamples.
  Unfinished records after restart become `interrupted` and are not rerun.
- If the Lean invocation returns a failed or timed-out proof within the task
  budget, its report and raw evidence remain available. Only a successful
  verification is exported as a successful-example ZIP; bundle refusal never
  hides the rejected proof's report.
- Normal cancellation removes a build lock only if its owner is this terminated
  worker. After an abrupt service/OS crash, an old verifier lock may need the
  existing verifier's recovery procedure. Never remove a live verifier's lock.

Changing `--timeout`, `--memory-mib`, `--config`, or `--jobs-dir` requires a
service restart. Only one service can own a given jobs directory.

## Start a task

From the repository root, while Ollama is running:

```text
python tools/sslp_agent.py providers
python tools/sslp_agent.py probe
python tools/sslp_agent.py run --question "Check the current code with the exact tool. Is this a Lean certificate?" --output tmp/agent-example-1
```

Use a new output directory each time. For Chinese or multiline questions,
`--question-file question.txt` reads UTF-8. To test a workbench experiment,
download **Export code JSON** and pass that file via `--input`; parameter-only
`sslp.experiment.v2` files are not code instances.

An explicit model switch applies to the entire task:

```text
python tools/sslp_agent.py --provider local-fast run --question "Read the verification scope." --output tmp/agent-example-2
```

To enable one actual Lean verification in a task:

```text
python tools/sslp_agent.py run --allow-lean --question "Use check_lean on current and report its actual scope and axioms." --output tmp/agent-example-3
```

`--allow-lean` makes the tool available; the model must actually call it. The
reported tool trace and `verification[].kernel.status` show whether it ran.
For guaranteed direct verification independent of a model decision, use the
existing `tools/sslp_explorer.py verify ... --lean` command instead.

## Model configuration

Copy `models.example.json` to a private local configuration and pass
`--config PATH`. The default provider must be enabled and `open_weights`.
Operators classify providers in this configuration; this label is not a
license audit. Choose a closed model explicitly with `--provider` after
enabling its configuration.

- `adapter: ollama` uses `/api/chat`, records `/api/version` and the installed
  model digest from `/api/tags`, and requests non-streamed tool calling with
  thinking disabled. The selected model/server must support those features.
- `adapter: chat_completions` uses `/models` and `/chat/completions` relative
  to `base_url` (normally ending in `/v1`). It implements the common message,
  tool-call ID, usage and token-limit fields, not every vendor extension.
  Endpoints without model listing or with a different protocol need another
  adapter. A generic compatible adapter is not a claim that every closed API
  has been integrated or tested.
- `api_key_env` names an environment variable read only by the backend.
  Literal keys, credential-bearing URLs and unknown config fields are rejected.
  Non-loopback endpoints require HTTPS. Redirects and ambient HTTP proxies are
  not used; configure the intended endpoint explicitly.
- `revision` optionally pins an Ollama model digest. Without a pin, the
  available digest is recorded at task start. Remote compatible APIs may not
  expose an immutable weight revision; the report does not invent one.
- Timeouts, context size and output-token bounds are explicit per provider.
  Actual tool-calling quality must be evaluated for each selected model.

The default Qwen3 14B model request has a 120-second response timeout,
separate from the companion's 600-second whole-job limit. Ollama can queue
this request behind another application's generation or model load. `probe`
checks that the model is installed and listed; it does not test generation
latency or reserve a model slot. If a request times out, let other requests
on the same Ollama server finish and submit a new job. Direct exact and Lean
checks remain available without waiting for the model. No automatic retry,
model switch, daemon restart or unloading of another application's model occurs.
Reports record failed model attempts and their round and elapsed time, separately
from verification records. A job marked `completed` can contain `provider_error`;
it is not an acceptance pass.

No API keys are sent to the frontend, included in model prompts, or saved in
reports. Selecting a remote endpoint sends the task question, selected code
data and tool outputs there; use a local provider when those must stay local.
Manuscript files and arbitrary filesystem content are not retrieval tools.

## Registered tools and evidence

| Tool | Result |
| --- | --- |
| `get_case` | Actual current code coordinates, gate and conventions |
| `get_reference` | Bounded, source-labelled explanations of KL/conventions/scope |
| `make_candidate` | A copy with optional replacement gate exponents and bounded quarter-turn changes; omit `angles` to keep the gate |
| `check_exact` | Normalization, all Pauli compressions below the input's target distance, and gate-support check |
| `inspect_pauli` | A selected exact compression with the input's denominator; omit both masks to inspect the first failure |
| `check_lean` | Optional input-derived research certificate or legacy canonical certificate, at most once |

The original input never changes. Each candidate starts from it; repeated
candidate creation replaces the candidate slot, not the original. Earlier
results remain indexed by their actual input hash. There is no arbitrary
shell, filesystem path, generated-source execution, or model-defined tool.
For an amplitude sign flip use `quarter_turns: 2` (multiplication by -1).
`quarter_turns: 1` multiplies by i. Gate angles and requested logical residues
remain unchanged unless the gate exponents are changed. Inspect the actual
candidate and tool arguments when evaluating whether the model followed a
research question; valid tool arguments alone do not establish that it did.
Matrix inspection and first-failure summaries include exact entry strings
and independently computed KL defects (nonzero off-diagonal entries or unequal
diagonal entries). The denominator is a shared representation scale, not an
additional KL condition. These diagnostics remain exact arithmetic, not Lean.

Exact checks separate KL validity from the gate's requested support residues.
A changed gate can fail the latter while all KL matrices still pass. The
research adapter checks diagonal phase action in the supplied logical basis;
its support test is sufficient, not a test of every possible logical action.
Failure on a different basis does not prove mathematical nonexistence. The
legacy adapter still requires its registered canonical basis. A sign flip
can preserve KL, as it does for the four-qubit acceptance input; the assistant
must inspect the actual result instead of assuming failure.

`run.json` separates `answer` (untrusted model explanation), the complete tool
trace, model invocation metadata, and an executor-owned verification index.
Every computed input has its own exact report. A candidate is written to
`candidate.json`; a real kernel job writes `lean-job/` with the input-bound
certificate, log and evidence. Existing bundle commands can package that job.

The report's `status: answered` means the model returned text. It does **not**
mean the text is correct, the requested task was fulfilled, or a proof passed.
`answer.citations` checks whether `[tool:tN]` references identify successful
tools in this run. Missing, failed or nonexistent references are shown in the
panel. This checks reference existence only: prose and its mathematical
interpretation still require evaluation. Model text cannot set structured
evidence status. No model response certifies the entire manuscript.
If citations are missing/invalid or the no-Lean statement is omitted, the
assistant requests at most one explanation revision within the existing round
budget. `explanation_feedback` records that request. Unresolved citation defects
remain visible; this is not semantic validation of the revised explanation.

## Budgets and current limits

Defaults: six model rounds, ten tool calls, one explicitly enabled Lean job.
The CLI accepts bounded `--max-rounds`, `--max-tools`, and `--lean-timeout`.
The Lean timeout applies to the certificate invocation; dependency validation
and prerequisite compilation are not covered by that timeout. This is the
existing local CLI behavior. The companion service adds the whole-job budget,
queue and process-tree controls described above; these do not turn it into a
remote multiuser execution service.

A truncated model response executes no proposed tools. An unavailable model
ends the task without switching provider. Completed tool evidence survives
round exhaustion or a later model error. No generation determinism is claimed
from temperature zero or a recorded model digest.

Run regression tests with:

```text
python -m unittest tools.tests.test_explorer_research tools.tests.test_explorer_reproduce tools.tests.test_explorer_jobs tools.tests.test_explorer_agent tools.tests.test_explorer tools.tests.test_explorer_manuscript -v
```

Next: validate the browser connection interactively and on an independent
machine, then design a separate authenticated multiuser service if reviewers
need shared remote compute. Broader proof search and model-generated Lean
execution remain outside this first assistant.
