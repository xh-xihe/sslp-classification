import SixQubit.Orbit36

namespace MainTheory.Orbit36MomentCharacters

open SixQubit.Orbit36

def vertices : Fin 12 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11]

def rowPairs : Fin 11 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def character (ij : Fin 6 × Fin 6) (x : SS.BitString 6) : ℚ :=
  if x ij.1 = x ij.2 then 1 else -1

def momentMinor : Matrix (Fin 12) (Fin 12) ℚ :=
  Fin.cases (fun _ => 1) (fun i j => character (rowPairs i) (vertices j))

theorem vertices_exact : Finset.univ.image vertices = S0 := by decide +kernel
theorem vertices_injective : Function.Injective vertices := by decide +kernel
theorem fiber_cards : S0.card = 12 ∧ S1.card = 12 := by decide +kernel

theorem character_complement (ij : Fin 6 × Fin 6) (x : SS.BitString 6) :
    character ij (SS.complement x) = character ij x := by
  cases h1 : x ij.1 <;> cases h2 : x ij.2 <;> simp [character, SS.complement, h1, h2]

theorem constant_row : momentMinor 0 = fun _ => 1 := rfl
theorem pair_rows (i : Fin 11) :
    momentMinor i.succ = fun j => character (rowPairs i) (vertices j) := rfl

end MainTheory.Orbit36MomentCharacters
