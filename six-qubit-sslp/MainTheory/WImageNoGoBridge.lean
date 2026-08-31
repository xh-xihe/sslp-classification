import MainTheory.Levels

/-!
# Generic bridge from a code-level no-go theorem to an empty W-image

The 51 orbit modules state their final obstruction using explicit finite
fibres.  `MainTheory.Levels.WImage` states support using residue equations.
This theorem is the reusable, proof-relevant conversion between the two.
-/

namespace MainTheory.WImageNoGoBridge

/-- If the two explicit finite sets are exactly the advertised residue fibres
and every normalized distance-three pair on those sets is impossible, then the
paper-facing weight-enumerator image is empty. -/
theorem WImage_eq_empty_of_noCode {q : Nat} [NeZero q]
    (av : Fin 6 → ZMod q) (r0 r1 : ZMod q)
    (S0 S1 : Finset (SS.BitString 6))
    (hS0 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r0) = S0)
    (hS1 : (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = r1) = S1)
    (noCode : ∀ c d : SS.State 6 ℂ,
      (∀ x, x ∉ S0 → c x = 0) →
      (∀ y, y ∉ S1 → d y = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c, d] 3 → False) :
    MainTheory.Levels.WImage av r0 r1 = ∅ := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, _⟩
    exfalso
    apply noCode c d
    · intro x hx
      apply hc x
      intro hweight
      apply hx
      rw [← hS0]
      simp [hweight]
    · intro y hy
      apply hd y
      intro hweight
      apply hy
      rw [← hS1]
      simp [hweight]
    · exact hnc
    · exact hnd
    · exact hdist
  · simp

end MainTheory.WImageNoGoBridge
