import MainTheory.OrderEightBSixMagnitudes
import MainTheory.AntisymmetricTriangleRatios

set_option autoImplicit false

namespace MainTheory.OrderEightBTriangleDisplays

open MainTheory.OrderEightBFlipDisplays MainTheory.OrderEightBSixMagnitudes
open MainTheory.OrderEightSupportDisplays MainTheory.MomentPolytope
open MainTheory.AntisymmetricTriangleRatios
open SixQubit.Orbit65 (S0 S1)

theorem ratio1 (c d : SS.State 6 ℂ) (hb : beta0 c ≠ 0) (hv : beta1 d ≠ 0) :
    star (beta0 c)*alpha1 d+star (alpha0 c)*beta1 d=0 ↔
    alpha1 d/beta1 d= -(star (alpha0 c)/star (beta0 c)) :=
  edge_ratio _ _ _ _ hb hv

theorem ratio2 (c d : SS.State 6 ℂ) (hg : gamma0 c ≠ 0) (hw : gamma1 d ≠ 0) :
    star (gamma0 c)*beta1 d+star (beta0 c)*gamma1 d=0 ↔
    beta1 d/gamma1 d= -(star (beta0 c)/star (gamma0 c)) :=
  edge_ratio _ _ _ _ hg hw

theorem plus (c d : SS.State 6 ℂ) (hb : beta0 c ≠ 0) (hv : beta1 d ≠ 0)
    (h1 : alpha1 d/beta1 d= -(star (alpha0 c)/star (beta0 c)))
    (h2 : beta1 d/gamma1 d= -(star (beta0 c)/star (gamma0 c))) :
    alpha1 d/gamma1 d=star (alpha0 c)/star (gamma0 c) :=
  positive _ _ _ _ _ _ hb hv h1 h2

theorem minus (c d : SS.State 6 ℂ) (hg : gamma0 c ≠ 0) (hw : gamma1 d ≠ 0) :
    star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d=0 ↔
    alpha1 d/gamma1 d= -(star (alpha0 c)/star (gamma0 c)) :=
  edge_ratio _ _ _ _ hg hw

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 8) (Fin 8) → ℝ)
    (H : Feasible bottomB topB p)
    (hc : ∀ i,Complex.normSq (c (bottomB i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (topB i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨ha,_,hb,hv,hg,hw⟩ := all_nonzero c d p H hc hd
  have h1 := (ratio1 c d hb hv).1 (edge1 c d hs0 hs1 hkl)
  have h2 := (ratio2 c d hg hw).1 (edge2 c d hs0 hs1 hkl)
  have hp := plus c d hb hv h1 h2
  have hm := (minus c d hg hw).1 (edge3 c d hs0 hs1 hkl)
  exact incompatible _ _ _ _ ha hg hp hm

end MainTheory.OrderEightBTriangleDisplays
