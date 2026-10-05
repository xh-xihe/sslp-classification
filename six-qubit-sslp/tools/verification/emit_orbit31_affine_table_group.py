"""Emit finite affine candidates; Lean checks each map and the group isomorphism."""
import argparse
from itertools import permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def vec(items):
    return '![' + ','.join(map(str, items)) + ']'


def generate():
    coordinates = [(0, 0), (0, 1), (1, 0), (1, 1)]
    matrices, inverses, translations = [], [], []
    for p in permutations(range(4)):
        b = coordinates[p[0]]
        columns = [tuple(x ^ y for x, y in zip(coordinates[p[k]], b)) for k in (2, 1)]
        m = [[columns[j][i] for j in range(2)] for i in range(2)]
        assert (m[0][0]*m[1][1]-m[0][1]*m[1][0]) % 2 == 1
        inv = [[m[1][1], m[0][1]], [m[1][0], m[0][0]]]
        matrices.append(vec(vec(row) for row in m))
        inverses.append(vec(vec(row) for row in inv))
        translations.append(vec(b))
    return f'''import MainTheory.Orbit31TableSymmetry

/-! The affine group on F2 squared, its actual four-point action, and its
group isomorphism with S4. The table actions exhaust S3 x AGL(2,2). -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit31AffineTableGroup
open MainTheory.Orbit31TableSymmetry
open MainTheory.Orbit31SignedSupport (A B)
noncomputable section

abbrev V := Fin 2 → ZMod 2
def coordinates : Fin 4 → V := ![![0,0],![0,1],![1,0],![1,1]]
def coordinateIndex (x : V) : Fin 4 := Fin.ofNat 4 (2*(x 0).val+(x 1).val)
theorem coordinates_left : ∀ j, coordinateIndex (coordinates j) = j := by decide +kernel
theorem coordinates_right : ∀ x, coordinates (coordinateIndex x) = x := by decide +kernel
def coordinateEquiv : Fin 4 ≃ V where
  toFun := coordinates
  invFun := coordinateIndex
  left_inv := coordinates_left
  right_inv := coordinates_right

def linearMatrices : Fin 24 → Matrix (Fin 2) (Fin 2) (ZMod 2) := {vec(matrices)}
def inverseMatrices : Fin 24 → Matrix (Fin 2) (Fin 2) (ZMod 2) := {vec(inverses)}
def translations : Fin 24 → V := {vec(translations)}
theorem inverse_left : ∀ r x, (inverseMatrices r).mulVec ((linearMatrices r).mulVec x) = x := by decide +kernel
theorem inverse_right : ∀ r x, (linearMatrices r).mulVec ((inverseMatrices r).mulVec x) = x := by decide +kernel

def linearPart (r : Fin 24) : V ≃ₗ[ZMod 2] V where
  toLinearMap := (linearMatrices r).mulVecLin
  invFun := (inverseMatrices r).mulVec
  left_inv := inverse_left r
  right_inv := inverse_right r

def affinePart (r : Fin 24) : V ≃ᵃ[ZMod 2] V :=
  (linearPart r).toAffineEquiv.trans (AffineEquiv.constVAdd (ZMod 2) V (translations r))
theorem affine_model : ∀ r j, affinePart r (coordinates j) =
    coordinates (colFunctions r j) := by decide +kernel

def affineAction : (V ≃ᵃ[ZMod 2] V) →* Equiv.Perm (Fin 4) where
  toFun e := (coordinateEquiv.trans e.toEquiv).trans coordinateEquiv.symm
  map_one' := by apply Equiv.ext; intro j; exact coordinateEquiv.symm_apply_apply j
  map_mul' e f := by
    apply Equiv.ext
    intro j
    change coordinateEquiv.symm (e (f (coordinateEquiv j))) =
      coordinateEquiv.symm (e (coordinateEquiv (coordinateEquiv.symm (f (coordinateEquiv j)))))
    rw [coordinateEquiv.apply_symm_apply]

theorem affineAction_injective : Function.Injective affineAction := by
  intro e f he
  apply AffineEquiv.ext
  intro x
  obtain ⟨j,rfl⟩ := coordinateEquiv.surjective x
  apply coordinateEquiv.symm.injective
  exact Equiv.congr_fun he j

theorem affineAction_surjective : Function.Surjective affineAction := by
  intro p
  obtain ⟨r,hr⟩ := all_col_permutations p
  refine ⟨affinePart r,?_⟩
  rw [← hr]
  apply Equiv.ext
  intro j
  change coordinateEquiv.symm (affinePart r (coordinates j)) = colFunctions r j
  rw [affine_model]
  exact coordinateEquiv.symm_apply_apply _

def aglTwoIsoSFour : (V ≃ᵃ[ZMod 2] V) ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective affineAction ⟨affineAction_injective,affineAction_surjective⟩
def productGroupIso :
    (Equiv.Perm (Fin 3) × (V ≃ᵃ[ZMod 2] V)) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4)) :=
  MulEquiv.prodCongr (MulEquiv.refl _) aglTwoIsoSFour

def arbitraryTable (r : Equiv.Perm (Fin 3)) (p : Equiv.Perm (Fin 4))
    (v : Fin 16) : Fin 16 :=
  if h : v.val < 4 then A (p ⟨v.val,h⟩)
  else B (r ⟨(v.val-4)/4,by omega⟩) (p ⟨(v.val-4)%4,by omega⟩)

theorem all_table_actions (r : Equiv.Perm (Fin 3)) (p : Equiv.Perm (Fin 4)) :
    ∃ g : Fin 144, tablePermutation g = arbitraryTable r p := by
  obtain ⟨i,hi⟩ := all_row_permutations r
  obtain ⟨j,hj⟩ := all_col_permutations p
  let g : Fin 144 := ⟨24*i.val+j.val,by omega⟩
  have hdiv : g.val/24 = i.val := by dsimp [g]; omega
  have hmod : g.val%24 = j.val := by dsimp [g]; omega
  refine ⟨g,?_⟩
  rw [← hi,← hj]
  funext v
  simp only [tablePermutation,modelTable,arbitraryTable,hdiv,hmod]
  rfl

end
end MainTheory.Orbit31AffineTableGroup
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'MainTheory/Orbit31AffineTableGroup.lean'
    text = generate()
    if args.check:
        if path.read_text(encoding='utf8') != text:
            raise SystemExit('affine table group source is stale')
    else:
        path.write_text(text, encoding='utf8', newline='\n')
    print('affine table group source checked' if args.check else 'affine table group source emitted')


if __name__ == '__main__':
    main()
