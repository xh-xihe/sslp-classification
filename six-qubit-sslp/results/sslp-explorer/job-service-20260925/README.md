# Local companion service validation — 2026-09-25

The HTTP service ran at IPv4 loopback port 8766. Requests carried a temporary
service key held only in memory; no key is included in this directory. This
is same-machine service/API validation, not browser interaction or independent
machine validation.

- `exact-report.json`: real worker process, canonical input, exact KL passed,
  all 154 Pauli compressions passed; Lean not run.
- `agent-report.json`: first five-round Qwen3 14B run executed the requested
  tools but exhausted its round budget before producing prose. This record is
  retained. Execution completion does not imply the assistant answered.
- `six-round-agent/agent-report.json`: after increasing the bounded default
  to six rounds, Qwen returned an explanation citing actual successful tools
  t2–t5. Original input passed; flipping only word 0, `000000`, by two quarter
  turns produced 18 failing Pauli compressions. First failure: X1 X6
  (`x_mask=33`, `z_mask=0`), off-diagonal coordinate `[24,0,0,0,0,0,0,0]/120`.
  The explanation correctly states that Lean did not run for this task.
  Citation checking validates existence, not the semantics of arbitrary prose.
- `lean-report.json`: independent direct task submitted over HTTP. A fresh
  input-bound certificate invocation passed all seven roots; axioms were
  `Classical.choice`, `Quot.sound`, and `propext`. Verifier time 82.484 seconds,
  whole task about 83.1 seconds; 11 content-validated local modules reused,
  zero rebuilt. No cold rebuild or independent dependency acquisition claimed.
- `verification.zip`: downloaded through the authenticated artifact endpoint,
  SHA-256 `a9e70ed2ba77e1a411a0c8e889f4eab974a3aed717a453717bc9871393cd0124`.
  The bundled manifest/source/input bindings were checked before service export.
- `lean-cancel.json`: cancelled a real Lean task after it acquired its build
  lock. The worker tree stopped, its own lock was removed, and no completed
  artifacts were published for that cancelled task.

Regression validation: 46 Python tests passed (including real HTTP, queue,
timeout, restart, Windows descendant termination and memory-limit tests);
23 JavaScript tests passed, including Python/JS canonical input-hash agreement.
Type checking and the production build passed. Existing proof/data export
integrity checks passed. Local HTTP returned 200 and included the assistant
dialog; downloadable certificate bytes matched disk. No in-app browser was
available, so no visual/click/local-network-permission QA was performed.

Scope remains the class-36 adapter: supplied canonical amplitudes,
normalization, orthogonality, distance at least three, and the physical phase
layer on every logical superposition assuming zeta^5=1. This does not certify
the whole manuscript, classification, minimal order or a gate-level encoder.
