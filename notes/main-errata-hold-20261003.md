# Main-text errata held for author discussion

Author instruction, 2026-10-03: retain `documents/20261003/main.tex` as the
authoritative main text without edits while the authors discuss the following
items with Bei Zeng. Correct the supplementary material and continue the Lean
bridges and orbit 2/3 certification independently.

Frozen main-text SHA-256:
`fb694c01b1144ce99d9a6d602c1a2629269bdd4c906a95fe9654f43f54a70958`.

| Location | Archived issue | Proposed correction; not applied |
| --- | --- | --- |
| Lines 274–277 | The Singleton bound is false for rank-one codes under the stated KL-distance convention. The existing Lean counterexample has n=3, K=1, d=3. | Restrict this statement to K≥2. |
| Lines 172–176 | The introductory finiteness statement omits the hypotheses used in the theorem. Distance-one examples can have a continuous diagonal logical group. | Specify a fixed product basis and detection of single-site Z errors, for example d≥2. |
| Lines 269–272 | Probability moments account for diagonal Z errors. Logical diagonal matrix elements of X/Y errors also depend on amplitude phases. | Restrict the probability-moment explanation to Z errors and retain full KL conditions for the other errors. |
| Lines 1825–1827 | The prose minimizes physical order over all representatives, whereas eq:qmin minimizes over reduced diagonal representatives. | Use the same restricted class of representatives as the definition. |
| Lines 684–686 | Rational replacement changes the homogeneous direction while preserving the matrix image; the prose says the homogeneous component is unchanged. | Say that the matrix image is preserved and the difference lies in the kernel. |

These holds do not authorize changing the main text or declaring its unqualified
statements proved. The supplementary material may advance beyond the frozen
main-text enumeration status; any such difference must be recorded explicitly.

Detailed evidence: [20261003 review](manuscript-review-20261003.md).
