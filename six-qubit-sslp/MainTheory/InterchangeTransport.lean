import MainTheory.RankTwoGlobal

/-!
# Semantic transport through logical-state interchange

`thm:rank-two-sslp` lists its normalizations: local `X` conjugation, permutation
of the physical qubits, a global scalar, **logical-state interchange**, and
replacement of the generator by a coprime power.  The first, second and last
have semantic transports (`FlipSemanticTransport`,
`PermutationSemanticTransport`, `UnitPowerSemanticTransport`).  Interchange did
not: it was treated as absorbed into the existential quantifier over
eigenframes, which is true but is not a statement.

An independent audit had listed it as missing, and it stayed missing because
"the Lean route does not need it" is a judgement about the proof, not about
what the theorem says.  This file makes it a theorem: swapping the two logical
words of a finite generator resolution gives another finite generator
resolution on the same code, with the same modulus and the same angle.

The eigenvalue ratio inverts, which is what one expects -- interchanging the
logical basis inverts the logical phase -- and the projective order is
unchanged.
-/

namespace MainTheory.InterchangeTransport

open MainTheory

noncomputable section

variable {n d q : ℕ} [NeZero q]

/-- Reindexing a frame by an equivalence does not change its span. -/
theorem codeSpan_reindex {K : ℕ} (F : CodeSpec.OrthonormalFrame n K)
    (e : Fin K ≃ Fin K) (G : CodeSpec.OrthonormalFrame n K)
    (hG : G.vec = fun k => F.vec (e k)) :
    CodeSpec.codeSpan G = CodeSpec.codeSpan F := by
  unfold CodeSpec.codeSpan
  congr 1
  rw [hG]
  exact e.surjective.range_comp F.vec

/-- The two logical words, interchanged. -/
def swapFrame (F : CodeSpec.OrthonormalFrame n 2) :
    CodeSpec.OrthonormalFrame n 2 where
  vec := fun k => F.vec (Equiv.swap 0 1 k)
  orthonormal := by
    intro i j
    rw [F.orthonormal]
    by_cases h : i = j
    · subst h; simp
    · have : Equiv.swap (0 : Fin 2) 1 i ≠ Equiv.swap (0 : Fin 2) 1 j := by
        intro hEq
        exact h ((Equiv.swap (0 : Fin 2) 1).injective hEq)
      simp [h, this]

@[simp] theorem swapFrame_vec (F : CodeSpec.OrthonormalFrame n 2)
    (k : Fin 2) : (swapFrame F).vec k = F.vec (Equiv.swap 0 1 k) := rfl

/-- **Logical-state interchange transports a finite generator resolution.**

Same code, same modulus, same angle vector; only the labelling of the two
logical words changes. -/
def swapFiniteGeneratorResolution {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    RankTwoGlobal.FiniteGeneratorResolution C q where
  zeta := G.zeta
  primitiveRoot := G.primitiveRoot
  angle := G.angle
  primitive := G.primitive
  eigenFrame := swapFrame G.eigenFrame
  span_eq := by
    rw [codeSpan_reindex G.eigenFrame (Equiv.swap 0 1) (swapFrame G.eigenFrame)
      rfl]
    exact G.span_eq
  eigenvalue := fun k => G.eigenvalue (Equiv.swap 0 1 k)
  eigen := fun k => G.eigen (Equiv.swap 0 1 k)
  projectively_nontrivial := by
    have h := G.projectively_nontrivial
    simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h.symm

/-- **The interchange inverts the logical phase ratio**, and nothing else. -/
theorem swap_ratio {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    (swapFiniteGeneratorResolution G).eigenvalue 1
        / (swapFiniteGeneratorResolution G).eigenvalue 0
      = G.eigenvalue 0 / G.eigenvalue 1 := by
  simp [swapFiniteGeneratorResolution, Equiv.swap_apply_left,
    Equiv.swap_apply_right]

/-- The interchange leaves the angle vector and the modulus alone, so the
physical operation `D(a;q)` is literally the same gate. -/
@[simp] theorem swap_angle {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    (swapFiniteGeneratorResolution G).angle = G.angle := rfl

end

end MainTheory.InterchangeTransport
