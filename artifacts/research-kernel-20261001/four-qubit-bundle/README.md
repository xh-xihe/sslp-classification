# SSLP input-bound local verification bundle

This bundle covers one concrete code instance. It does not certify the entire
manuscript, classification, or a gate-level encoder. Private manuscript text
is omitted; the input records source hashes and formula locators.

Install Python >= 3.10, the pinned Lean toolchain via elan, and the Python
dependency (`python -m pip install -r requirements.txt`). Fetch the exact
dependencies from lake-manifest.json; `lake exe cache get` can obtain the
mathlib artifacts. The checker verifies clean dependency revisions and hashes
the installed artifacts. It builds missing local modules serially.

From this directory run:

```text
python tools/sslp_explorer.py check-bundle .
python tools/sslp_explorer.py verify case.json --lean --output fresh-run
```

The first command checks integrity only. The second executes the exact
checks and a fresh input-bound Lean certificate, and audits its transitive
axioms. Review fresh-run/evidence.json and fresh-run/lean.log. Dependency
artifacts can be reused only after content validation. The timeout option
limits the final certificate invocation, not dependency preparation/builds.

Encoding is represented as an abstract isometry. The displayed transversal
phase layer is a symbolic circuit description. Status fields state the exact
scope of the checked gate action. The original run log is historical evidence;
it is not a fresh check on your machine. A changed manifest is not authenticated
by its own hashes; obtain the bundle from the intended publisher.
