"""Create a review revision without changing either authoritative manuscript.

The original source is retained verbatim. latexdiff supplies the marked version.
This script changes exposition and status bookkeeping, not the held main text.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "documents/20261003"
DEST = SOURCE / "revisions/si-review-20261003"
BASELINE_HASH = "7b15965e38cce05c0b1d3ae0ccccc0642d5c2db74d06f7453d4dd8fac5459ede"
MAIN_HASH = "fb694c01b1144ce99d9a6d602c1a2629269bdd4c906a95fe9654f43f54a70958"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert digest(SOURCE / "supplementary.tex") == BASELINE_HASH
    assert digest(SOURCE / "main.tex") == MAIN_HASH
    DEST.mkdir(parents=True, exist_ok=True)
    baseline = DEST / "baseline"
    baseline.mkdir(exist_ok=True)
    for filename in ("main.tex", "supplementary.tex", "references.bib"):
        shutil.copy2(SOURCE / filename, baseline / filename)
    text = (SOURCE / "supplementary.tex").read_text(encoding="utf-8")
    edits = []

    def replace(old, new, description):
        nonlocal text
        assert text.count(old) == 1, (description, text.count(old))
        start = text.index(old)
        edits.append({"description": description, "old": old, "new": new})
        text = text[:start] + new + text[start + len(old):]

    replace(
        "The main text is retained at its 20261003 author-approved version; these two\n"
        "refinements extend its eleven-image status. Complete enumeration tables and\n"
        "reproducibility conventions are included at the end.",
        "Result~III of the main text determines eleven complete enumerator images.\n"
        "The two additional images established here do not enlarge their union.\n"
        "Enumeration tables and verification instructions are collected at\n"
        "the end.",
        "Separate main-text status from supplementary refinements in the abstract.")

    replace("\\usepackage{xcolor}\n", "\\usepackage{xcolor}\n\\usepackage{xurl}\n\\usepackage{needspace}\n\\setlength{\\emergencystretch}{3em}\n",
            "Allow long certificate paths to wrap without protruding into the margin.")
    replace("\\texttt{proved\\_class3\\_linear\\_consequences}",
            "\\path{proved_class3_linear_consequences}",
            "Allow the long scalar-certificate JSON key to wrap.")

    anchor = "We consider exact \\(((6,2,3))\\) codes with a selected nontrivial projective\n"
    overview = r"""\subsection*{Setting and proof outline}
The finite classification below concerns six physical qubits, logical
rank two, distance at least three, and a selected nontrivial diagonal
projective logical action. The general structural results in the main
text supply the controlled-lift reduction; the finite tables apply that
reduction in this setting. The bound \(q\le9\) applies to the selected
controlled representative. We retain its physical order \(q\) and
targeted logical order \(m\) as labels of the finite classification.

\begin{center}
\small
\begin{tabular}{@{}p{0.36\linewidth}p{0.56\linewidth}@{}}
\toprule
Result & Proof entry\\
\midrule
Controlled representatives and order cutoff &
Section~\ref{sec:enumeration-setup}; apply the main-text bound to the
selected representative.\\
The 66 labeled moment orbits &
Theorem~\ref{thm:six-66-orbits}, Section~\ref{six:sec:protocol}, and
Table~\ref{tab:66orbits}.\\
51 exclusions and 15 realizations &
Theorem~\ref{thm:main-result-II}; normalized encoders satisfying full KL.\\
The main-text eleven-image result &
Theorem~\ref{thm:main-result-III}; complete nonempty enumerator images.\\
Two additional enumerator converses &
Theorems~\ref{o2gc:thm-image}, \ref{o3gc:main}, and
Corollary~\ref{cor:supp-result-III-refinement}; orbits 2 and 3.\\
Order-five uniqueness &
Theorem~\ref{thm:main-result-IV}; the stronger rigidity result for orbit 36.\\
\bottomrule
\end{tabular}
\end{center}
The classification has 66 labeled moment orbits: 51 are excluded and
15 admit codes. The proofs determine 13 of the nonempty enumerator
images. These counts refer to moment orbits and enumerator images;
classification of the code families up to local unitaries is a further
question.

\subsection*{Shared bit, Pauli, and normalization conventions}
The general physical sites are \(1,\ldots,6\), with integer encoding
\(x\mapsto\sum_{j=1}^6x_j2^{j-1}\). A displayed tuple lists sites in
increasing order. The orbit-3 section relabels these sites as \(0,\ldots,5\),
with site 0 the least significant bit.

Amplitude equations may use \(X^uZ^v\). Exact Hermitian-Pauli
certificates use
\(P_{u,v}=i^{\operatorname{popcount}(u\mathbin{\&}v)}X^uZ^v\).
They differ only by a nonzero phase, so vanishing and scalar-compression
KL conditions are equivalent. For a rank-two projector on six qubits,
\[
 A_w=\tfrac14\sum_{\wt(E)=w}|\operatorname{Tr}(PE)|^2,
 \qquad B_w=\tfrac12\sum_{\wt(E)=w}\operatorname{Tr}(PEPE),
 \qquad B(X,Y)=\tfrac1{32}A(X+3Y,X-Y).
\]
For \(K=2,n=6\), these are the normalization factors used throughout.
The orbit-2 four-qubit Pauli coordinates follow \(I<X<Y<Z\).
Convert machine encodings to this order before forming monomial indices.
The quadratic and cubic monomials in both certificates are ordinary
products. Multiplicities are carried by the ordered sums.

"""
    replace(anchor, overview + anchor, "Add proof index and shared conventions.")

    replace(
        "moment orbit.}\n\\label{tab:66orbits}",
        "moment orbit. The statuses include the supplementary orbit-2/3\n"
        "converses; the main-text eleven-image statement is restated separately\n"
        "in Theorem~\\ref{thm:main-result-III}.}\n\\label{tab:66orbits}",
        "Clarify the table's supplementary and certification scope.")

    replace(
        "Consequently the complete six-qubit classification now covers\n"
        "\\(64\\) of the \\(66\\) moment-orbit images.",
        "Consequently the enumerator-image determination, including empty\n"
        "images, covers \\(64\\) of the \\(66\\) labeled moment orbits.",
        "Distinguish image determination from full code classification.")

    begin = text.index("% BEGIN integrated orbit 2 proof;")
    end = text.index("\\section{Exact weight-enumerator image of orbit 2}", begin)
    replace(text[begin:end], "% Integrated orbit-2 proof; portable fragment documented in its package.\n\n",
            "Remove obsolete orbit-2 integration comments.")
    begin = text.index("% BEGIN integrated orbit 3 proof;")
    end = text.index("\\section{Exact weight-enumerator image of primitive order-two orbit 3}", begin)
    replace(text[begin:end], "% Integrated orbit-3 proof; sites 0,...,5 relabel sites 1,...,6.\n\n",
            "Remove obsolete orbit-3 integration comments.")

    anchor = "\\subsection{Flatness of the inactive pair and the active reflection}\n"
    roadmap = r"""\paragraph{Proof dependencies.}
The KL equations determine the spectator marginals and a common
antiunitary. These give the Pauli coordinates of the partial isometry
\(T\), to which the quartic identity applies.
\begin{center}
\small
\begin{tabular}{@{}p{0.20\linewidth}p{0.35\linewidth}p{0.35\linewidth}@{}}
\toprule
Step & Input & Output and reference\\
\midrule
Complementary purities & Full KL and the selected parity action &
Flat inactive pair and product marginals;
Lemma~\ref{o2gc:lem-flatness}.\\
Common antiunitary & Product marginals and mixed KL &
The common \(J_0\);
Lemma~\ref{o2gc:lem-commonJ}.\\
Partial isometry & The common spectator basis for \(Q_0,Q_1\) &
The restricted complex Pauli coordinates of \(T\);
Section~\ref{o2gc:subsec-T}.\\
Quartic identity & Every \(T\) in that coordinate space &
The full \(528\times528\) coefficient matrix and 36 zero coordinates;
Lemma~\ref{o2gc:lem-matrix}.\\
Exact positivity & Each of the 111 remaining rational blocks &
Coercivity on 492 coordinates, then \(A_3=0\);
Proposition~\ref{o2gc:prop-rigidity}.\\
\bottomrule
\end{tabular}
\end{center}
"""
    replace(anchor, roadmap + anchor, "Add orbit-2 dependency table.")

    old_start = "The exact characteristic polynomials of all blocks are summarized\n"
    start = text.index(old_start)
    end = text.index("The supplied standard-library verifier establishes positivity without", start)
    replace(text[start:end],
        "Table~\\ref{o2gc:tab-blocks} lists the characteristic polynomials.\n"
        "The rational \\(LDL^T\\) factorizations below establish positivity\n"
        "directly. The spectral-table verification is recorded in\n"
        "Section~\\ref{sec:kernel-certification-scope}.\n\n",
        "Use direct rational LDL as the formal positivity argument.")

    anchor = "\\subsection{Universal identities and the exact scalar reduction}\n"
    roadmap = r"""\paragraph{From an encoder to the finite certificate.}
The quadratic zeros hold for every encoder satisfying
\eqref{o3gc:encoder}. Averaging code-preserving transformations then
gives a positive moment invariant under the permutations and Hadamard
transformations used in the certificate.
\begin{center}
\small
\begin{tabular}{@{}p{0.27\linewidth}p{0.63\linewidth}@{}}
\toprule
Stage & Mathematical meaning and proof entry\\
\midrule
Scalar data & 42 Pauli categories, 24 with even transverse weight;
squared Pauli-coefficient sums;
Section~\ref{o3gc:scalar}.\\
Scalar duals & 43 equations, 84 nonnegative rows, and six rational duals;
five category zeros and \(A_1+A_2+A_3=1\);
Lemma~\ref{o3gc:scalarlemma}.\\
Physical zeros & A zero nonnegative category sum forces each physical
coefficient to vanish; full KL and spin saturation give the remaining
quadratic zeros; Section~\ref{o3gc:amplitudes}.\\
Positive moment & Actual cubic products are averaged; phase, XOR,
and permutation reductions give the coordinates. Hadamard rows follow
from invariance of the average; Section~\ref{o3gc:averaging}.\\
Certificate application & The 211 rows vanish on that actual moment;
the target equals \(N^3A_3\), and the square is nonnegative. The rational
identity then forces \(A_3=0\); Sections~\ref{o3gc:rows}--\ref{o3gc:certificate}.\\
\bottomrule
\end{tabular}
\end{center}
The counts describe different objects:
\begin{center}
\small
\begin{tabular}{@{}rl@{}}
\toprule
Count & Object\\
\midrule
715 & sorted cubic triples in the XOR-zero basis\\
116 & phase blocks of that basis\\
269 & real entry orbits after simultaneous active permutations and transpose\\
36 & nonzero cubic terms in the positive square\\
211 & constraint rows used in the rational identity\\
120 & physical Pauli labels in the target sum\\
\bottomrule
\end{tabular}
\end{center}
"""
    replace(anchor, roadmap + anchor, "Add orbit-3 semantic roadmap and dimension glossary.")

    start = text.index("To integrate the fragment, place it beside \\path{supplementary.tex} and add")
    end = text.index("% END integrated orbit 3 proof", start)
    replace(text[start:end],
        "The verifiers check the scalar duals and the degree-six coefficient\n"
        "identity. Sections~\\ref{o3gc:scalar}--\\ref{o3gc:rows} derive their\n"
        "inputs from the encoder equations and the averaged cubic moment.\n\n",
        "Replace fragment integration and audit commentary with proof references.")

    start = text.index("\\begin{remark}[Scope of the converse]")
    end = text.index("\\end{remark}", start) + len("\\end{remark}")
    replace(text[start:end], r"""\begin{remark}[Polynomial form of the reduction]
The reduction uses polynomial identities in the frame and Pauli
coordinates, so it applies to zero amplitudes and singular frames.
The common-antiunitary equations give the quartic identity that
determines \(\mathcal W_2\).
\end{remark}""", "Condense the orbit-2 converse remark to its mathematical content.")

    replace("matrix directly from the explicitly coded polynomial identity; it does\n"
            "not read the LaTeX files or trust a precomputed positive-semidefinite\n"
            "matrix. The JSON and log are supporting records rather than runtime\n"
            "dependencies.",
            "matrix from the quartic polynomial, then checks its rational\n"
            "factorizations. The JSON and log record the resulting blocks and pivots.",
            "Describe the orbit-2 verifier by its computation.")
    replace("Discovery of the multipliers can use numerical optimization; the proof\n"
            "does not. Its finite verification uses exact integer coefficient\n"
            "expansion and rational \\texttt{Fraction} arithmetic. The analytic\n"
            "encoder reduction is proved above, so this section does not depend\n"
            "on an unproved converse or on a regular-support assumption from an\n"
            "earlier problem note.",
            "Verification uses integer coefficient expansion and rational\n"
            "\\texttt{Fraction} arithmetic. The preceding lemmas derive the\n"
            "quartic identity from the encoder equations.",
            "Remove numerical-discovery and draft-history commentary from orbit 2.")
    replace("It does not trust a stored moment matrix, floating-point nullspace,\n"
            "numerical optimizer, or positivity tolerance. The positive term is\n"
            "explicitly the squared modulus of a cubic, so a separate numerical\n"
            "PSD check is unnecessary. This gives a finite rational verification\n"
            "of the stated linear-form identity.",
            "The positive term is the squared modulus of the cubic \\(p\\).\n"
            "The coefficient check proves the stated identity over \\(\\Q\\).",
            "Conclude the finite verification with its proved identity.")
    replace("All changes of variables and constraint multiples were polynomial\n"
            "and homogeneous. The sole physical normalization is \\(N>0\\);\n"
            "no coordinate chart, nonzero-amplitude hypothesis, spectator\n"
            "Schmidt division, or regular-support assumption is needed.",
            "The reductions are homogeneous polynomial identities and apply\n"
            "for \\(N>0\\), including zero amplitudes and singular spectator marginals.",
            "Retain the boundary coverage in one mathematical sentence.")
    start = text.index("This equality of images does not identify the underlying sets of")
    end = text.index("\\subsection{Exact certificate files and reproducibility}", start)
    replace(text[start:end], r"""The orbit-3 proof works directly with its encoder amplitudes and the
degree-six certificate. The orbit-2 proof uses the auxiliary partial
isometry and a quartic certificate. Their enumerator images coincide,
while the LU classification of the code families remains a further
question. The unresolved enumerator images among the four primitive
order-two records are those of orbits~1 and~4.

""", "Replace repeated orbit-2/3 exclusions with a direct comparison of the proofs.")

    replace("\\begin{theorem}[Main-text Result III and the orbit-2/3 refinements]",
            "\\begin{theorem}[Restatement of main-text Result III]",
            "Restore the main-text theorem as a true restatement.")
    replace(" \\mathcal W_2=\\mathcal W_3&=\\{\\mathcal L(\\alpha):0\\le\\alpha\\le1\\},\n"
            " \\label{eq:main-result-III-W23}\\\\\n", "",
            "Move the two additional images out of the restatement.")
    start = text.index("These formulas determine thirteen sets completely.")
    end = text.index("This determines neither all fifteen enumerator sets", start)
    replace(text[start:end], r"""These formulas determine eleven sets completely. The four nonempty
sets \(\mathcal W_1,\mathcal W_2,\mathcal W_3,\mathcal W_4\) are not
determined by this main-text result. Their additional supplementary
status is stated in Corollary~\ref{cor:supp-result-III-refinement}.
The union of the eleven completely determined sets is exactly
\begin{equation}
\begin{split}
 \bigcup_{r\in\{7,8,9,10,11,16,21,22,23,36,45\}}\mathcal W_r
 ={}&\{\mathcal L(\alpha):0\le\alpha\le1\}\\
 &{}\cup\{\mathcal M(t):\tfrac23\le t\le1\}
 \cup\{\mathcal R_5^A\}.
\end{split}
\label{eq:main-result-III-union}
\end{equation}
""", "Restore the eleven-image union and preserve its external label.")
    replace("This determines neither all fifteen enumerator sets in the nontrivial\n"
            "diagonal sector nor the enumerator set of all exact \\(((6,2,3))\\) codes.\n"
            "In particular, it does not prove the global weight-enumerator conjecture\n"
            "stated in Result~III of the main text.",
            "The global weight-enumerator conjecture in the main text also\n"
            "includes codes with trivial diagonal logical group.",
            "State the domain of the global conjecture without repeated disclaimers.")
    replace("Theorem~\\ref{o2gc:thm-image} and Theorem~\\ref{o3gc:main} determine\n"
            "\\(\\mathcal W_2\\) and \\(\\mathcal W_3\\) on all rank and boundary strata.\n\n"
            "For the remaining four classes, Theorem~\\ref{q2fam:thm:inclusions} proves",
            "For all four primitive order-two records,\n"
            "Theorem~\\ref{q2fam:thm:inclusions} establishes the inclusions",
            "Preserve the four-record construction inclusions.")
    replace("These constructions prove nonemptiness and the stated inclusions, but do\n"
            "not exclude additional enumerators in those four classes.",
            "These constructions prove nonemptiness and the stated inclusions.\n"
            "The additional converse arguments for orbits 2 and 3 are assembled\n"
            "in the following corollary; additional enumerators have not been\n"
            "excluded for orbits 1 and 4.",
            "Restrict the unresolved exclusion direction to orbits 1 and 4.")

    anchor = "\\subsection{Result IV:"
    start = text.index(anchor)
    # Insert before the entire next theorem heading, preserving its precise title.
    corollary = r"""The preceding theorem restates Result~III of the main text. The
following supplementary refinement uses the converse proofs for orbits
2 and 3.

\begin{corollary}[Supplementary refinement of Result III]
\label{cor:supp-result-III-refinement}
The two additional complete enumerator images are
\begin{equation}
 \mathcal W_2=\mathcal W_3
 =\{\mathcal L(\alpha):0\le\alpha\le1\}.
 \label{eq:main-result-III-W23}
\end{equation}
Thus thirteen nonempty images are determined, and only
\(\mathcal W_1,\mathcal W_4\) remain unresolved. Their determined union is
\begin{equation}
\begin{split}
 \bigcup_{r\in\{2,3,7,8,9,10,11,16,21,22,23,36,45\}}\mathcal W_r
 ={}&\{\mathcal L(\alpha):0\le\alpha\le1\}\\
 &{}\cup\{\mathcal M(t):\tfrac23\le t\le1\}
 \cup\{\mathcal R_5^A\}.
\end{split}
\label{eq:supp-result-III-union}
\end{equation}
The union equals \eqref{eq:main-result-III-union}. The interval
\(2/3\le t\le1\) is proved for this sector; the global conjecture uses
\(3/5\le t\le1\).
\end{corollary}

\begin{proof}
Theorems~\ref{o2gc:thm-image} and \ref{o3gc:main} prove
\eqref{eq:main-result-III-W23}.
Their common image already equals \(\mathcal W_7\), so adding these
two images leaves the previously determined union unchanged.
\end{proof}

"""
    replace(anchor, corollary + anchor, "State the supplementary thirteen-image refinement separately.")

    replace("The enumeration script requires Python~3, NumPy, SciPy, and SymPy.  The\n"
            "orbit-specific verifiers require Python~3 and SymPy.",
            "The enumeration script requires Python~3, NumPy, SciPy, and SymPy.\n"
            "The legacy orbit-specific scripts listed above require Python~3 and\n"
            "SymPy. The added orbit-2 and orbit-3 exact verifiers described below\n"
            "use only the standard library; the optional orbit-3 numerical controls\n"
            "separately require NumPy.",
            "Separate exact-verifier dependencies from legacy and numerical scripts.")

    anchor = "\\begin{thebibliography}{9}\n"
    appendix = r"""\subsection{Added certificate packages and repository entry points}
\label{sec:added-certificate-entry-points}
The portable package commands and their input/output roles are given in
Sections~\ref{o2gc:subsec-reproducibility} and \ref{o3gc:reproduction}.
The repository equivalents below are relative to the checkout root of
\href{https://github.com/xh-xihe/dyadic-lifts/tree/main}
{the \texttt{main} branch}. To identify a verification
run, record its commit identifier, manuscript hashes, and build record.

\begin{center}
\small
\begin{tabular}{@{}p{0.39\linewidth}p{0.53\linewidth}@{}}
\toprule
Portable file & Repository counterpart and role\\
\midrule
\path{orbit2_exact_certificate.py} &
\path{tools/certificates/orbit2_exact_certificate.py}; regenerates the
matrix and checks rational pivots.\\
\path{orbit2_certificate_blocks.json} &
\path{results/orbit2-kernel/gram-blocks.json}; reproducible output record.\\
\path{class3_scalar_obstruction.py} &
\path{tools/certificates/orbit3_scalar_certificate.py}; checks six scalar duals.\\
\path{orbit3_exact_sextic_certificate.py} &
\path{tools/certificates/orbit3_exact_sextic_certificate.py}; exact coefficient verifier.\\
\path{orbit3_sextic_certificate.json} &
\path{results/orbit3-kernel/certificate.json}; essential sextic-certificate input.\\
Lean finite-certificate sources &
\path{SixQubit/Generated/Orbit2Gram/All.lean} and
\path{SixQubit/Generated/Orbit3SexticIdentity.lean}.\\
Lean semantic bridges and audit &
\path{MainTheory/OrbitCertificationAudit.lean}; actual-encoder and intermediate statements.\\
\bottomrule
\end{tabular}
\end{center}
From a checkout, using the Lean version pinned in \path{lean-toolchain},
the two verification entry points are
\begin{verbatim}
python tools/rebuild_orbit_certificates.py
python tools/build_lean.py --module MainTheory \
    --module SixQubit.Audit --module QECC.Audit
\end{verbatim}
The first reproduces the finite rational records and generated-source
checks. The second kernel-checks the import closures and audits the
transitive axioms of the named roots. The sextic verifier reads
\path{results/orbit3-kernel/certificate.json}; its \texttt{--json}
option writes verification metadata.

\section{Lean declarations and verification records}
\label{sec:kernel-certification-scope}
The table lists the implemented proof steps and their Lean declarations.
The remaining steps are listed after the table.

\begin{longtable}{@{}p{0.21\linewidth}p{0.39\linewidth}p{0.30\linewidth}@{}}
\toprule
Paper component & Lean declaration & Conclusion\\
\midrule
\endfirsthead
\toprule
Paper component & Lean declaration & Conclusion\\
\midrule
\endhead
Orbit-2 positivity, Lemma~\ref{o2gc:lem-matrix} &
\path{SixQubit.Generated.Orbit2Gram.all_blocks_posDef} &
Positive definiteness of all 111 rational blocks on 492 complex
coordinates.\\
Orbit-2 complementary purities, Lemma~\ref{o2gc:lem-flatness} &
\path{MainTheory.Orbit2RemainingPurity.reference_active_pauli_mass};
\path{MainTheory.Orbit2RemainingPurity.four_oneSite_complementary_pauli_masses} &
Encoder Gram and complementary Pauli-mass equalities.\\
Orbit-2 full converse and attainment,
Theorem~\ref{o2gc:thm-image} &
\path{Orbit2.Encoder.enumerator};
\path{Orbit2.Encoder.exact_distance_three};
\path{Orbit2.orbit2_exact_enumerator_image} &
The complete enumerator image of normalized orbit-2 encoders,
attainment of the interval, and exact distance three.\\
Orbit-3 scalar reduction, Lemma~\ref{o3gc:scalarlemma} &
\path{SixQubit.Generated.Orbit3Scalar.zero_categories};
\path{MainTheory.Orbit3ScalarEqualities} (module) &
The six rational duals evaluated on the encoder's Pauli-category masses.\\
Orbit-3 positive moment, \eqref{o3gc:Y} &
\path{MainTheory.Orbit3CubicBasis.moment_posSemidef};
\path{MainTheory.Orbit3CoordinateRealization.tableMatrix_eq_scaled_moment};
\path{MainTheory.Orbit3CoordinateRealization.reduced_square_nonneg} &
The positive 715-triple moment, its 269 coordinates, and the
nonnegative cubic square.\\
Orbit-3 XOR-block reduction, \eqref{o3gc:Rrow} &
\path{MainTheory.Orbit3SamplingSpectatorX.sampling_translation_identity} &
Invariance under all 64 physical X translations for phase-stable
observables.\\
Orbit-3 physical zero rows, Section~\ref{o3gc:rows} &
\path{MainTheory.Orbit3SamplingRows.all_physical_rows_zero} &
Vanishing of all 211 physical row expressions on the sampled encoders.\\
Orbit-3 spin and Hadamard coefficient rows,
\eqref{o3gc:spinrow} and \eqref{o3gc:Hrow} &
\path{SixQubit.Generated.Orbit3CollectedSpinRows.all_spin_primitive_rows_zero};
\path{SixQubit.Generated.Orbit3CollectedHadamardRows.all_hadamard_primitive_rows_zero} &
The five spin and three Hadamard expressions equal their primitive
certificate rows, which vanish on the encoder moment.\\
Orbit-3 finite identity, Lemma~\ref{o3gc:certlemma} &
\path{SixQubit.Generated.Orbit3SexticIdentity.identity_on_moments} &
The identity for arbitrary vectors of 269 real coordinates.\\
Orbit-3 target recovery, \eqref{o3gc:homotarget} &
\path{MainTheory.Orbit3SamplingTarget.original_Aco_zero_of_target_zero} &
Vanishing of the sampled target implies the original encoder's
\(A_3=0\).\\
\bottomrule
\end{longtable}
The \texttt{Orbit2} declarations are supplied by
\path{six-qubit-orbit2/lean} at
\href{https://github.com/xh-xihe/dyadic-lifts/tree/f84bbd39451a3e0648fd1bd4ccf0ad38f558245a}
{commit \texttt{f84bbd3}}. Their input consists of orthonormal logical
words, full distance-three KL conditions, and the selected weight-four
logical involution. The encoder reduction, quartic identity, rational
block certificate, and interval attainment are proved in that package.
Independent verification rebuilt all 357 local modules and audited
44 declarations.

The Lean orbit-3 proof uses a finite average of code-preserving
transformations in place of the compact-group average in
Section~\ref{o3gc:averaging}. The remaining implementation work is the
\texttt{MainTheory} adapter to the orbit-2 package and, for orbit~3,
assembly of the KL-row and target identifications with the finite identity.

The listed declarations use \texttt{propext}, \texttt{Quot.sound}, and
\texttt{Classical.choice}. Build records bind source and dependency hashes
to compiled outputs. The proof-progress record is
\path{results/orbit-certification-20261003.json}.

\Needspace{6\baselineskip}
The auxiliary orbit-2 characteristic-polynomial table was checked
independently by \path{check_orbit2_charpolys.py}, with exact results in
\path{orbit2-charpolys.json} in the manuscript-review records. This is a
Python exact check of the spectral data. Lean proves positivity from
the rational \(LDL^T\) certificates.

"""
    replace(anchor, appendix + r"\Needspace{14\baselineskip}" + "\n" + anchor,
            "Add portable/repository mapping, Lean declarations, and bibliography pagination.")

    replace(
        "On the affine space determined by\n",
        "For an orbit-21 completion, normalization and the six-qubit\n"
        "MacWilliams identity give\n",
        "State the actual completion hypotheses of the orbit-21 certificate.")
    replace(
        "the complete KL identities\n",
        "The complete KL identities include\n",
        "Introduce the necessary complete KL equations directly.")
    replace(
        "and the two orbit-21 symmetries above, direct coefficient comparison gives\n",
        "Expanding the complete transforms leaves a residual quadratic trace\n"
        "expression. Its Walsh transform vanishes on pairs of strings in the\n"
        "prescribed fibers, giving\n",
        "Include the support-level Walsh step in the orbit-21 proof.")
    replace(
        "Identity~\\eqref{eq:o21-farkas} is an exact rational Farkas certificate.  It\n"
        "is obtained by expanding the complete transforms and reducing all \\(4096\\)\n"
        "Pauli labels under the two forced symmetries.  There are \\(512\\) nonzero\n"
        "unsigned coefficient classes, and coefficient comparison leaves only the\n"
        "residual coefficients \\(0,2,3,4\\).  No floating-point inequality enters the\n"
        "certificate.",
        "Identity~\\eqref{eq:o21-farkas} is an exact rational certificate.\n"
        "The two forced symmetries reduce the \\(4096\\) Pauli labels to \\(640\\)\n"
        "unsigned classes after anticommuting labels are removed. To eliminate\n"
        "the residual, expand each \\(a_E\\) as a squared projector trace.\n"
        "Every resulting term contains two strings and their common \\(X\\)-mask\n"
        "translation in one of the two prescribed fibers. The Walsh coefficient\n"
        "of each such pair is zero. The remaining terms are exactly the five\n"
        "nonnegative sums in Eq.~\\eqref{eq:o21-farkas}.",
        "Correct the unsigned-class count and describe the certified residual elimination.")

    revised = DEST / "supplementary-revised.tex"
    revised.write_text(text, encoding="utf-8", newline="\n")
    # Main stays byte-identical; it is included only for standalone compilation.
    shutil.copy2(SOURCE / "main.tex", DEST / "main.tex")
    shutil.copy2(SOURCE / "references.bib", DEST / "references.bib")
    ledger = {
        "schema": 1, "baseline_main_sha256": MAIN_HASH,
        "baseline_supplementary_sha256": BASELINE_HASH,
        "revised_supplementary_sha256": digest(revised),
        "authoritative_manuscripts_modified": False,
        "revision_round": 3,
        "style": "Direct mathematical exposition; concise hypotheses and proof references; implementation status collected in the final appendix.",
        "changes": edits,
    }
    (DEST / "revision-ledger.json").write_text(json.dumps(ledger, indent=2) + "\n", encoding="utf-8")
    preamble = DEST / "revision-markup-preamble.tex"
    preamble.write_text(r"""\RequirePackage[normalem]{ulem}
\RequirePackage{color}
\providecommand{\DIFadd}[1]{{\color{blue}#1}}
\providecommand{\DIFdel}[1]{{\color{red}\sout{#1}}}
\providecommand{\DIFaddbegin}{}
\providecommand{\DIFaddend}{}
\providecommand{\DIFdelbegin}{}
\providecommand{\DIFdelend}{}
\providecommand{\DIFmodbegin}{}
\providecommand{\DIFmodend}{}
\providecommand{\DIFaddFL}[1]{\DIFadd{#1}}
\providecommand{\DIFdelFL}[1]{\DIFdel{#1}}
\providecommand{\DIFaddbeginFL}{}
\providecommand{\DIFaddendFL}{}
\providecommand{\DIFdelbeginFL}{}
\providecommand{\DIFdelendFL}{}
\AddToHook{cmd/maketitle/after}{\noindent\fbox{\parbox{0.94\linewidth}{\small
Review revision of the 20261003 supplement.\quad
\textcolor{red}{\sout{Deleted text}}\quad
\textcolor{blue}{Added text}.\newline
The main text and original supplementary source are preserved.}}\par\medskip}
""", encoding="utf-8")
    marked = DEST / "supplementary-marked.tex"
    run = subprocess.run([
        "latexdiff", "--encoding=utf8", "--math-markup=coarse",
        "--preamble=" + str(preamble),
        str(baseline / "supplementary.tex"), str(revised),
    ], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    markup = run.stdout.decode("utf-8")
    # TeX eats spaces after control words: permit a line break between this
    # long deleted identifier and its unchanged identifier in the new format.
    markup = markup.replace(
        r"\DIFdelend \DIFaddbegin \path{proved_class3_linear_consequences}",
        r"\DIFdelend\allowbreak{} \DIFaddbegin \path{proved_class3_linear_consequences}")
    markup = markup.replace(
        r"\texttt{\DIFdel{proved\_class3\_linear\_consequences}}",
        r"\linebreak[4]\texttt{\DIFdel{proved\_class3\_linear\_consequences}}")
    # latexdiff leaves unsafe path commands outside DIFadd. Color those paths
    # only inside added regions; restore any deleted path it comments out.
    added = False
    def color_path(match):
        nonlocal added
        token = match.group(0)
        if token.startswith(r"\DIFaddbegin"):
            added = True
        elif token.startswith(r"\DIFaddend"):
            added = False
        elif token.startswith("%DIFDELCMD"):
            path = re.search(r"\\path\{([^}]+)\}", token).group(1)
            escaped = path.replace("_", r"\_")
            return r"\DIFdel{\texttt{" + escaped + "}}"
        elif added:
            return r"\textcolor{blue}{" + token + "}"
        return token
    markup = re.sub(
        r"\\DIFadd(?:begin|end)(?:FL)?|%DIFDELCMD < \\path\{[^}]+\}\s*%%%|\\path\{[^}]*\}",
        color_path, markup)
    marked.write_text(markup, encoding="utf-8", newline="\n")
    (DEST / "latexdiff.log").write_bytes(run.stderr)
    build = ROOT / "tmp/pdfs/supplementary-review-20261003"
    build.mkdir(parents=True, exist_ok=True)
    shutil.copy2(revised, build / "supplementary.tex")
    for filename in ("main.tex", "references.bib", "supplementary-marked.tex"):
        shutil.copy2(DEST / filename, build / filename)
    assert digest(SOURCE / "main.tex") == MAIN_HASH
    assert digest(SOURCE / "supplementary.tex") == BASELINE_HASH
    print(f"Created review source with {len(edits)} changes: {revised}")


if __name__ == "__main__":
    main()
