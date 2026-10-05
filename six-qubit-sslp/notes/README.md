# Working notes

Current status and navigation live in [`docs/status.md`](../docs/status.md)
and [`docs/proof-index.md`](../docs/proof-index.md). The dated notes below
preserve their original progress reports and are not the current status authority.

Condensed notes kept during the formalization, one fact per file. They are
working notes, not polished documentation — the process document in
`formalization/` is the reference. They are preserved because each records
something that was expensive to learn and is not recoverable from the Lean
sources.

| Note | What it pins down |
|---|---|
| `sslp-nogo-mechanism-ladder.md` | historical first-batch work log; its dated Done/Remaining counts are superseded by the 51-orbit note |
| `sslp-orbit-delta-identification.md` | historical: `d_LP` was once used to pin `delta`. The authoritative rule is `delta = q/m` with additive order `m`; see `tools/manifest.json` |
| `kl-dressings-undercount.md` | the tooling bug that gated three orbits; the count `154 = 1 + 6*3 + 15*9` is the invariant that catches it |
| `sslp-orbit25-recipe.md` | historical construction checkpoint for orbit 25; the current proof is complete |
| `sslp-orbit26-hexagon.md` | historical work log for orbit 26's group structure and cross-anchor repair; the current proof is complete |
| `sslp-orbit29-pair-coords.md` | historical construction checkpoint for the now-complete pair-coordinate proof |
| `sslp-orbit31-structure.md` | chronological work log for the now-complete 4×4-table proof; old progress counts are historical |
| `sslp-orbit31-indexmap.md` | the authoritative index map — the manuscript's `B_{i,e} = (u_i, ē)` reverses column order versus sorted indexing |
| `sslp-orbit33-block-recipe.md` | the certified block-reflection route |
| `sslp-51-orbits-complete.md` | final state of the 51 no-go certifications, plus a dated positive-orbit addendum; the four transcription checks and why 14/15/24 cannot take the orbit-13 shortcut |
| `sslp-29-orbits-complete.md` | superseded pre-repair snapshot of the old 29-orbit milestone; use the 51-orbit note for current status |

The index-map note is worth singling out. Getting that map backwards makes a
correct column relation appear to fail, which reads as a mathematical obstruction
rather than a bookkeeping error, and cost real time.
