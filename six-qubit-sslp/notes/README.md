# Working notes

Condensed notes kept during the formalization, one fact per file. They are
working notes, not polished documentation — the process document in
`formalization/` is the reference. They are preserved because each records
something that was expensive to learn and is not recoverable from the Lean
sources.

| Note | What it pins down |
|---|---|
| `sslp-nogo-mechanism-ladder.md` | the mechanisms that close the routine orbits, and the bigrading reason the ladder stops |
| `sslp-orbit-delta-identification.md` | historical: `d_LP` was once used to pin `delta`. The authoritative rule is `delta = q/m` with additive order `m`; see `tools/manifest.json` |
| `kl-dressings-undercount.md` | the tooling bug that gated three orbits; the count `154 = 1 + 6*3 + 15*9` is the invariant that catches it |
| `sslp-orbit25-recipe.md` | the first orbit needing diagonal conditions |
| `sslp-orbit26-hexagon.md` | orbit 26's group structure and the cross-anchor repair |
| `sslp-orbit29-pair-coords.md` | pair-sum/difference coordinates decouple the moment system |
| `sslp-orbit31-structure.md` | the 4×4 table, the kernel-vector identity |
| `sslp-orbit31-indexmap.md` | the authoritative index map — the manuscript's `B_{i,e} = (u_i, ē)` reverses column order versus sorted indexing |
| `sslp-orbit33-block-recipe.md` | the certified block-reflection route |
| `sslp-51-orbits-complete.md` | final state of the full 51-orbit certification; the two checks that matter more than compilation, and why 14/15/24 cannot take the orbit-13 shortcut |
| `sslp-29-orbits-complete.md` | final state and what was verified by hand |

The index-map note is worth singling out. Getting that map backwards makes a
correct column relation appear to fail, which reads as a mathematical obstruction
rather than a bookkeeping error, and cost real time.
