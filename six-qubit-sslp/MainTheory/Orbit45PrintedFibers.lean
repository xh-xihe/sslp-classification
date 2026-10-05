import MainTheory.Orbit21LiteralData
import SixQubit.Orbit45Support
import MainTheory.Generated.OrbitTableNumericData

/-! Literal left-to-right qubit order in the expanded orbit-45 proof. -/

namespace MainTheory.Orbit45PrintedFibers

open MainTheory.Orbit21LiteralData MainTheory.Generated.OrbitTableNumericData
open SixQubit.Orbit45Support

def bottom : Fin 10 → SS.BitString 6 :=
  fun r => bits (![0,9,10,23,28,39,44,49,50,59] r)

def top : Fin 10 → SS.BitString 6 :=
  fun r => bits (![4,13,14,19,24,35,40,53,54,63] r)

def libraryBottom : Fin 10 → SS.BitString 6 := ![x0,x2,x4,x6,x8,x9,x7,x5,x3,x1]
def libraryTop : Fin 10 → SS.BitString 6 := ![y0,y2,y4,y6,y8,y9,y7,y5,y3,y1]

theorem record : paperQ 44 = 6 ∧ paperM 44 = 2 ∧ av = ![1,1,2,3,4,4] :=
  ⟨rfl,rfl,rfl⟩

theorem bit_transport : bottom = libraryBottom ∧ top = libraryTop := by decide +kernel

theorem matching : ∀ r, top r = SS.bxor (bottom r) (SS.stdBasis 3) := by decide +kernel

theorem bottom_injective : Function.Injective bottom := by decide +kernel
theorem top_injective : Function.Injective top := by decide +kernel

theorem full_fibers : Finset.univ.image bottom = S0 ∧ Finset.univ.image top = S1 := by
  decide +kernel

theorem residues : (∀ r, SS.weight av (bottom r) = 0) ∧
    (∀ r, SS.weight av (top r) = 3) := by decide +kernel

theorem complement_matching : ∀ r : Fin 10, SS.bxor (fun _ => true) (bottom r) = top r.rev := by
  decide +kernel

theorem opposite_parity : ∀ r : Fin 10,
    SS.hammingWt (bottom r.rev) % 2 ≠ SS.hammingWt (bottom r) % 2 := by decide +kernel

theorem reverse_sign : ∀ r : Fin 10,
    (-1 : ℤ) ^ SS.hammingWt (bottom r.rev) = -((-1 : ℤ) ^ SS.hammingWt (bottom r)) := by
  decide +kernel

end MainTheory.Orbit45PrintedFibers
