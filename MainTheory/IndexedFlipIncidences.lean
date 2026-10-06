import MainTheory.FlipCharacterObstruction

set_option autoImplicit false
namespace MainTheory.IndexedFlipIncidences
open MainTheory.FlipCharacter

theorem condition {n r : ℕ} (x : Fin r → SS.BitString n)
    (S0 S1 : Finset (SS.BitString n))
    (h0 : Finset.univ.image x=S0)
    (h1 : ∀ j,SS.complement (x j) ∈ S1)
    (u : SS.BitString n) (j : Fin r) :
    SS.complement (x j) ∈ incidenceSet S0 S1 u ↔
      ∃ i,x i=SS.bxor (SS.complement (x j)) u := by
  classical
  simp only [incidenceSet,Finset.mem_filter,h1,true_and,← h0,
    Finset.mem_image,Finset.mem_univ,true_and]

theorem monomial {n r : ℕ} (x : Fin r → SS.BitString n)
    (c d : SS.State n ℂ) (u : SS.BitString n) (i j : Fin r)
    (h : x i=SS.bxor (SS.complement (x j)) u) :
    incidenceMonomial c d u (SS.complement (x j))=star (c (x i))*d (SS.complement (x j)) := by
  simp only [incidenceMonomial,← h]

end MainTheory.IndexedFlipIncidences
