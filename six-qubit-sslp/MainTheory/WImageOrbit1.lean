import MainTheory.WImages
import MainTheory.PermutationSemanticTransport
import SixQubit.Orbit9S2Transport

/-!
# `eq:four-open-M-inclusion`, the orbit-one half

`rem:four-open-orbits` records what is known about the four orbits whose
weight-enumerator images are open.  One of its two inclusions is reachable:

  `{M(t) : 2/3 <= t <= 1}` is contained in `W_1`.

Orbit 45's image is exactly that interval family
(`WImages.WImage_orbit45`), and orbit 1's fibres are a coordinate permutation
of orbit 45's *modulo two*.  Concretely, `permAngle sigma` applied to orbit
45's angle `(1,1,2,3,4,4)` is `(4,4,2,3,1,1)`, whose reduction mod two is
orbit 1's `(0,0,0,1,1,1)`; and reduction is a ring homomorphism, so it carries
orbit 45's residues `0` and `3` to orbit 1's `0` and `1`.  A code sitting in
orbit 45's two fibres therefore sits, after the permutation, in orbit 1's --
and the `A`-enumerator does not notice a permutation
(`SixQubit.CodeEquiv.Aco_permAct`).

The **other** inclusion of the same remark, `{M(t)}` contained in `W_4`, is
not reachable this way: orbit 4's angle is `(1,1,1,1,1,1)`, so its fibres are
the Hamming parity classes, parity is invariant under coordinate permutations
and shifted uniformly by a cube translation, and orbit 45 is this
development's only source of an enumerator with `A_3 != 0`, so no cube move
puts its support inside a parity class.  An exhaustive search over all 720
qubit permutations, all 64 cube shifts and the logical interchange confirms
it: of the realized orbits and the four open ones, the only fibre embedding
that exists at all is the one proved here.

That is a statement about this *route*, not about the inclusion.  An earlier
version of this paragraph said the `W_4` half was "believed unreachable
altogether", which is wrong: solving the Knill--Laflamme system numerically
inside orbit 4's two fibres reaches `M(t)` to machine precision across the
whole interval, so the inclusion is true and what is missing is an explicit
algebraic family, exactly as the paper's "explicit exact constructions"
suggests.  The same search reaches `L(alpha)` in all four open orbits.
-/

namespace MainTheory.WImageOrbit1

open MainTheory
open SixQubit.CodeEquiv

/-- Paper orbit 1's angle vector: `q = m = 2`, `a = (0,0,0,1,1,1)`. -/
def orbit1Av : Fin 6 → ZMod 2 := ![0, 0, 0, 1, 1, 1]

/-- The involution carrying orbit 45's separating coordinates onto orbit
1's. -/
def sigma : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- Reduction of residues modulo two. -/
abbrev red : ZMod 6 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- The subset-sum residue commutes with reduction, because it is a sum of
products and reduction is a ring homomorphism. -/
theorem weight_red (a : Fin 6 → ZMod 6) (s : SS.BitString 6) :
    SS.weight (fun j => red (a j)) s = red (SS.weight a s) := by
  unfold SS.weight
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul]
  congr 1
  cases s j <;> simp [SS.bit]

/-- Orbit 1's angle is orbit 45's, permuted and reduced. -/
theorem orbit1Av_eq :
    orbit1Av = fun j =>
      red (MainTheory.PermutationSemanticTransport.permAngle sigma
        SixQubit.Orbit45Support.av j) := by
  decide

/-- Hence orbit 1's residue at `s` is orbit 45's residue at the permuted
string, reduced. -/
theorem weight_orbit1Av (s : SS.BitString 6) :
    SS.weight orbit1Av s
      = red (SS.weight SixQubit.Orbit45Support.av (permStr sigma s)) := by
  rw [orbit1Av_eq, weight_red,
    MainTheory.PermutationSemanticTransport.weight_permStr]

/-- **`{M(t) : 2/3 <= t <= 1}` is contained in `W_1`.** -/
theorem FII_subset_WImage_orbit1 :
    MainTheory.WImages.FII '' Set.Icc (2 / 3 : ℝ) 1 ⊆
      Levels.WImage orbit1Av 0 1 := by
  rw [← MainTheory.WImages.WImage_orbit45]
  rintro A ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
  refine ⟨permAct sigma c, permAct sigma d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    refine hc (permStr sigma s) ?_
    intro h0
    exact hs (by rw [weight_orbit1Av, h0, map_zero])
  · intro s hs
    refine hd (permStr sigma s) ?_
    intro h3
    exact hs (by rw [weight_orbit1Av, h3]; decide)
  · rw [SixQubit.Orbit9Universal.innerC_permAct]; exact hnc
  · rw [SixQubit.Orbit9Universal.innerC_permAct]; exact hnd
  · have h := MainTheory.PermutationSemanticTransport.hasDistance_permAct
      sigma ![c, d] hdist
    have hfun : (fun k => permAct sigma (![c, d] k))
        = ![permAct sigma c, permAct sigma d] := by
      funext k
      fin_cases k <;> rfl
    rwa [hfun] at h
  · intro j
    have hfun : ![permAct sigma c, permAct sigma d]
        = fun k => permAct sigma (![c, d] k) := by
      funext k
      fin_cases k <;> rfl
    rw [hfun, Aco_permAct]
    exact hA j

end MainTheory.WImageOrbit1
