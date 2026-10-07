# Current manuscript correspondence

[Home](../README.md) · [Documentation](README.md) · [Reproduce](reproduce.md) · [Status](status.md)

The authoritative inputs are the frozen `20261003/main.tex` and current
`20261003/supplementary.tex`. Their exact hashes are recorded in
[repository-status.json](../results/repository-status.json).

| Scope | Disposition |
| --- | --- |
| SI original mathematical assertions | 1,622 reviewed kernel correspondences; no pending assertion |
| SI scope remarks | Three reviewed explanatory remarks; no additional theorem claimed |
| Remaining SI running text | All 1,622 blocks read in their full proof contexts |
| Main original mathematics | Correspondence reviewed; five author-held issues prevent complete certification of the frozen wording |
| Open enumerator questions | Orbits 1 and 4 remain explicitly open |
| Global conjecture and cited background | Retain their stated research or bibliographic scope |

The [claim ledger](../results/paper-claims-20261003.json) identifies every
display and named result. The [prose record](../results/prose-review-20261003.json)
binds exact paragraph contexts. Its tracked rows connect separately reviewed
equations and theorems; they do not assert a new theorem solely because a
nearby declaration exists. Actual type inspection, the whole source build
and the transitive standard-axiom audit are separate acceptance evidence.

The last three completed mathematical bridges are
[Orbit5SchmidtCompletion](../MainTheory/Orbit5SchmidtCompletion.lean),
[Orbit14OrthogonalFrames](../MainTheory/Orbit14OrthogonalFrames.lean) and
[SplitFamilyTableCertification](../MainTheory/SplitFamilyTableCertification.lean).
They address singular Schmidt branches, actual positive slice frames and all
four literal split-family logical records, including their physical KL conditions.

Two SI qualifications were checked explicitly: the orbit-31 support mask is
nonempty, and the orbit-17 graph retains weighted degree one quarter at every
vertex. Every displayed assertion kept its exact bytes and location. The main
source remains unchanged.

The [held main issues](../notes/main-errata-hold-20261003.md) are unrestricted
rank-one Singleton scope, missing finiteness hypotheses, probability moments
versus phase-dependent KL constraints, the class of physical representatives
being minimized, and homogeneous rational replacement. Corrected theorems and
counterexamples do not certify a false or broader frozen sentence.

The frozen main also retains historical editorial annotations: eleven settled
images, four then-open images, and an earlier publication URL. The current SI
and canonical repository settle thirteen images, with only orbits 1 and 4 open.
Those editorial differences are recorded rather than silently changing the main.

For accepted proof snapshots and their canonical branch publication, use
[current status](status.md). With the exact private manuscripts available,
`python tools/verification/check_si_correspondence.py` checks complete current
SI correspondence. The combined main/SI release gate remains incomplete while
the five main issues are frozen.
