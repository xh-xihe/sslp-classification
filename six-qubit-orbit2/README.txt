ORBIT-2 ENUMERATOR SECTION AND EXACT CERTIFICATE
Prepared October 2, 2026

Result
------
For exact six-qubit distance-three codes with the chosen physical logical
involution IIZZZZ, the complete Shor-Laflamme A-enumerator image is
  (1, alpha, 1-alpha, 0, 11+4*alpha, 16-alpha, 3-3*alpha), 0 <= alpha <= 1.

The section gives the full analytic encoder reduction, the exact quartic
certificate, positivity checks, and construction of every point in the interval.
This is an enumerator theorem, not a complete LU classification.

Files
-----
orbit2_enumerator_section.tex
  Include-ready section for supplementary.tex. No preamble or document
  environment. Reuses the supplement's theorem environments and notation.
  All new labels begin with o2gc:.

orbit2_enumerator_section_preview.tex
  Standalone LaTeX document with the section embedded and the full preamble.
  Compile this file to read the proof without needing supplementary.tex.
  It has no external TeX inputs.

orbit2_exact_certificate.py
  Exact verifier using Python 3's standard library only. It reconstructs M
  from the coded quartic identity and checks every integer/rational block.
  It does not parse the TeX or read the precomputed JSON.
  Only its opening documentation was adapted from the original verifier;
  executable code is unchanged.

orbit2_certificate_blocks.json
  All 111 integer blocks, monomial indices and positive rational LDL pivots
  for M minus 4I.

orbit2_verification_log.txt
  Fresh successful output from the packaged verifier.

SHA256SUMS
  File hashes of both TeX files, verifier, JSON, log and this README.

Include or compile
------------------
To include the section, place it alongside supplementary.tex and add:
  \input{orbit2_enumerator_section.tex}

For independent reading, compile orbit2_enumerator_section_preview.tex with
your usual LaTeX editor or distribution. All required packages are listed in
its preamble. Both the preview and a test insertion into the full supplement
were checked with the native LaTeX compiler.

The preview embeds the section so the package requires no supplementary.tex.
If modifying the mathematics later, keep the two source copies synchronized.
Existing status/count paragraphs elsewhere in the supplement require separate
updating when integrating the new theorem.

Verify
------
From this package directory:
  python3 orbit2_exact_certificate.py

To regenerate the supporting JSON:
  python3 orbit2_exact_certificate.py --json regenerated_blocks.json

The regenerated JSON must agree with orbit2_certificate_blocks.json.
No NumPy, SciPy, SymPy, optimizer, or earlier project files are required.
The verifier checks all 36 zero coordinates, all off-block zeros, and all
111 positive blocks by exact rational elimination. Timing is not part of
the proof.

Certificate dimensions
----------------------
32 complex coefficients: 8 in T1 and 24 in T3.
528 holomorphic quadratic monomials.
36 zero coordinates and 492 positive coordinates in 111 blocks.
2,844 nonzero entries in the sparse integer coefficient matrix.
Sparse-M SHA-256:
64b192ccce90edf4b583285307f46265435a51b032f72e6493057138a1820b1d

File-integrity checks (optional)
-------------------------------
On macOS:
  shasum -a 256 -c SHA256SUMS
On Linux:
  sha256sum -c SHA256SUMS

The file hashes above differ from the sparse-M digest: they check the
distributed files rather than the mathematical matrix serialization.
