# Scratch

Exploratory files that are not part of any library target.

`lakefile.lean` globs every submodule of `MainTheory`, so a broken file there
fails the whole build even when nothing imports it. These two were in that
position: neither has an importer, and both had genuine errors.

  * `TestBV.lean` — experiments with `BitVec`, `bv_decide` and `#synth`.
    Referenced `Function.det`, which does not exist.
  * `TestRankCert.lean` — one rank-certificate instance whose `decide` fails.

They are kept rather than deleted because they record what was being tried.
Moving them here was the smallest change that restores a clean build; if either
is wanted back in the library, it needs its error fixed first.
