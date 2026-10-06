import SixQubit.Orbit7FullTangent

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit7MatchingDisplays

open SixQubit.Orbit7Universal

abbrev Edge := Fin 5 × Fin 5

def matchings : Fin 5 → Fin 3 → Edge × Edge :=
  ![![((1,2),(3,4)),((1,3),(2,4)),((1,4),(2,3))],
    ![((0,2),(3,4)),((0,3),(2,4)),((0,4),(2,3))],
    ![((0,1),(3,4)),((0,3),(1,4)),((0,4),(1,3))],
    ![((0,1),(2,4)),((0,2),(1,4)),((0,4),(1,2))],
    ![((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]]

def nonincidentExplicit : Fin 5 → Finset Edge :=
  ![{(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)},
    {(0,2),(0,3),(0,4),(2,3),(2,4),(3,4)},
    {(0,1),(0,3),(0,4),(1,3),(1,4),(3,4)},
    {(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)},
    {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}]

theorem nonincidentPairs_explicit : ∀ v, nonincidentPairs v = nonincidentExplicit v := by decide +kernel

theorem hafnian_sum (x : Edge → ℂ) (i : Fin 5) :
    Hafnian5 x i = ∑ k : Fin 3, x (matchings i k).1 * x (matchings i k).2 := by
  fin_cases i <;> simp [Hafnian5,matchings,Fin.sum_univ_succ] <;> ring

theorem polar_sum (x y : Edge → ℂ) (i : Fin 5) :
    PolarHafnian5 x y i = ∑ k : Fin 3,
      (x (matchings i k).1 * y (matchings i k).2 +
        x (matchings i k).2 * y (matchings i k).1) := by
  fin_cases i <;> simp [PolarHafnian5,matchings,Fin.sum_univ_succ] <;> ring

noncomputable def matchingMatrix (A B : Edge → Spinor) (i : Fin 5) : Mat2 := fun p q =>
  ∑ k : Fin 3, (B (matchings i k).2 p * star (A (matchings i k).1 q) +
    B (matchings i k).1 p * star (A (matchings i k).2 q))

theorem oneflip_expansion (c d : SS.State 6 ℂ) (i : Fin 5) :
    oneFlipMat c d i = matchingMatrix (fun e => spinor c (aBase e.1 e.2))
      (fun e => spinor d (bBase e.1 e.2)) i := by
  funext p q
  simp only [oneFlipMat,nonincidentPairs_explicit]
  fin_cases i
  · simp [nonincidentExplicit]
    rw [
      show SS.bxor (bBase 1 2) (vmask 0) = aBase 3 4 by decide,
      show SS.bxor (bBase 1 3) (vmask 0) = aBase 2 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 0) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 0) = aBase 1 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 0) = aBase 1 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 0) = aBase 1 2 by decide]
    simp [matchingMatrix,matchings,Fin.sum_univ_succ]
    ring
  · simp [nonincidentExplicit]
    rw [
      show SS.bxor (bBase 0 2) (vmask 1) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 1) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 1) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 1) = aBase 0 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 1) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 1) = aBase 0 2 by decide]
    simp [matchingMatrix,matchings,Fin.sum_univ_succ]
    ring
  · simp [nonincidentExplicit]
    rw [
      show SS.bxor (bBase 0 1) (vmask 2) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 2) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 2) = aBase 1 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 2) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 2) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 2) = aBase 0 1 by decide]
    simp [matchingMatrix,matchings,Fin.sum_univ_succ]
    ring
  · simp [nonincidentExplicit]
    rw [
      show SS.bxor (bBase 0 1) (vmask 3) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 2) (vmask 3) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 3) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 3) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 3) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 4) (vmask 3) = aBase 0 1 by decide]
    simp [matchingMatrix,matchings,Fin.sum_univ_succ]
    ring
  · simp [nonincidentExplicit]
    rw [
      show SS.bxor (bBase 0 1) (vmask 4) = aBase 2 3 by decide,
      show SS.bxor (bBase 0 2) (vmask 4) = aBase 1 3 by decide,
      show SS.bxor (bBase 0 3) (vmask 4) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 4) = aBase 0 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 4) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 3) (vmask 4) = aBase 0 1 by decide]
    simp [matchingMatrix,matchings,Fin.sum_univ_succ]
    ring

end MainTheory.Orbit7MatchingDisplays
