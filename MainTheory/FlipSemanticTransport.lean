import MainTheory.RankTwoGlobal
import MainTheory.IntrinsicTransport
import MainTheory.Normalize
import MainTheory.Cyclic

/-!
# Semantic transport through a local `X` string

`PermutationSemanticTransport` rebuilds a `FiniteGeneratorResolution` after a
qubit permutation and `UnitPowerSemanticTransport` after replacing the
generator by a coprime power.  This file supplies the third normalization the
paper uses, local `X` conjugation (`eq:X-conjugation`), which the repository
had only in pieces: `IntrinsicTransport.shiftFrame` for the frame,
`Normalize.flip` for the angle, `Normalize.weight_bxor` for the subset sum.

The content is one identity.  Flipping the angle and shifting the state
changes the gate's eigenvalue by the common scalar
`chi zeta (weight a x0)^{-1}` and nothing else, so the *ratio* of the two
logical eigenvalues -- the only thing the projective statements see -- is
untouched.

The target code is a parameter rather than a construction, because the
resolutions that matter are transported onto a code presented by a different
frame with the same span; `span_eq` is exactly the hypothesis that records
this.
-/

namespace MainTheory.FlipSemanticTransport

open MainTheory
open MainTheory.IntrinsicTransport

noncomputable section

variable {n q : ℕ} [NeZero q]

theorem chi_ne_zero (zeta : ℂ) (hz : IsPrimitiveRoot zeta q) (x : ZMod q) :
    Cyclic.chi zeta x ≠ 0 :=
  pow_ne_zero _ (hz.ne_zero (NeZero.ne q))

/-- **`eq:X-conjugation`, on an eigenvector.**

If `D(a;q)` scales `v` by `lam`, then the flipped gate scales the shifted state
by `lam` divided by the common scalar `chi zeta (weight a x0)`. -/
theorem gate_flip_shift (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (x0 : SS.BitString n) (v : SS.State n ℂ) (lam : ℂ)
    (heigen : Gate.gate zeta a v = fun s => lam * v s) :
    Gate.gate zeta (Normalize.flip a x0) (fun s => v (SS.bxor s x0))
      = fun s => (lam / Cyclic.chi zeta (SS.weight a x0)) * v (SS.bxor s x0) := by
  funext s
  have hw : SS.weight (Normalize.flip a x0) s
      = SS.weight a (SS.bxor s x0) - SS.weight a x0 := by
    exact eq_sub_of_add_eq (Normalize.weight_bxor a x0 s).symm
  have h1 := congrFun heigen (SS.bxor s x0)
  rw [Gate.gate, Cyclic.diag_eq_chi] at h1 ⊢
  have hc : Cyclic.chi zeta (SS.weight a x0) ≠ 0 := chi_ne_zero zeta hz _
  rw [hw, Cyclic.chi_sub zeta hz]
  field_simp
  linear_combination h1

/-- **Rebuild a finite-generator resolution after a local `X` conjugation.**

The target code is supplied together with the span hypothesis, because the
resolutions this is applied to land on a code presented by a different frame
with the same code space. -/
def flipFiniteGeneratorResolution {d d' : ℕ}
    {C : CodeSpec.ExactCode n 2 d} {C' : CodeSpec.ExactCode n 2 d'}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (x0 : SS.BitString n)
    (hspan : CodeSpec.codeSpan C'.frame
      = CodeSpec.codeSpan (shiftFrame G.eigenFrame x0)) :
    RankTwoGlobal.FiniteGeneratorResolution C' q where
  zeta := G.zeta
  primitiveRoot := G.primitiveRoot
  angle := Normalize.flip G.angle x0
  primitive := Normalize.primitive_flip G.angle x0 G.primitive
  eigenFrame := shiftFrame G.eigenFrame x0
  span_eq := hspan
  eigenvalue := fun k =>
    G.eigenvalue k / Cyclic.chi G.zeta (SS.weight G.angle x0)
  eigen := by
    intro k
    exact gate_flip_shift G.zeta G.primitiveRoot G.angle x0
      (G.eigenFrame.vec k) (G.eigenvalue k) (G.eigen k)
  projectively_nontrivial := by
    intro h
    apply G.projectively_nontrivial
    have hc : Cyclic.chi G.zeta (SS.weight G.angle x0) ≠ 0 :=
      chi_ne_zero G.zeta G.primitiveRoot _
    field_simp at h
    exact h

/-- The transported resolution has the same logical eigenvalue ratio: the
local `X` string contributes only a common scalar. -/
theorem flip_ratio {d d' : ℕ}
    {C : CodeSpec.ExactCode n 2 d} {C' : CodeSpec.ExactCode n 2 d'}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) (x0 : SS.BitString n)
    (hspan : CodeSpec.codeSpan C'.frame
      = CodeSpec.codeSpan (shiftFrame G.eigenFrame x0)) :
    (flipFiniteGeneratorResolution (C' := C') G x0 hspan).eigenvalue 1 /
        (flipFiniteGeneratorResolution (C' := C') G x0 hspan).eigenvalue 0 =
      G.eigenvalue 1 / G.eigenvalue 0 := by
  have hc : Cyclic.chi G.zeta (SS.weight G.angle x0) ≠ 0 :=
    chi_ne_zero G.zeta G.primitiveRoot _
  simp only [flipFiniteGeneratorResolution]
  field_simp

end

end MainTheory.FlipSemanticTransport
