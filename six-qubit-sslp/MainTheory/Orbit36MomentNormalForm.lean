import MainTheory.Orbit36MomentLP

namespace MainTheory.Orbit36MomentNormalForm

open MainTheory.Orbit36MomentLP MainTheory.Orbit36MomentCharacters

def vertexProbability (p : Sum (Fin 12) (Fin 12) → ℝ) (i : Fin 4) : ℝ :=
  p (.inl ⟨i.val + 2, by omega⟩)
def edgeProbability (p : Sum (Fin 12) (Fin 12) → ℝ) (i : Fin 6) : ℝ :=
  p (.inl ⟨i.val + 6, by omega⟩)
def edges : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def degree (p : Sum (Fin 12) (Fin 12) → ℝ) (i : Fin 4) : ℝ :=
  ∑ e, if (edges e).1 = i ∨ (edges e).2 = i then edgeProbability p e else 0
def vertexMass (p : Sum (Fin 12) (Fin 12) → ℝ) : ℝ := ∑ i, vertexProbability p i
def edgeMass (p : Sum (Fin 12) (Fin 12) → ℝ) : ℝ := ∑ i, edgeProbability p i

structure NormalForm (p : Sum (Fin 12) (Fin 12) → ℝ) : Prop where
  equal_probabilities : ∀ i, p (.inl i) = p (.inr i)
  anchor_u : p (.inl 0) = 1/10
  anchor_v : p (.inl 1) = 1/10
  vertex_mass : vertexMass p = 2/5
  edge_mass : edgeMass p = 2/5
  degrees : ∀ i, vertexProbability p i = degree p i - 1/10

theorem normal_form (p : Sum (Fin 12) (Fin 12) → ℝ) (hp : Feasible p) : NormalForm p := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hu,hv,hP,hW,hD0,hD1,hD2,hD3⟩ :=
    (real_moment_system p hp).facts
  constructor
  · intro i
    fin_cases i <;> assumption
  · exact hu
  · exact hv
  · simpa [vertexMass, vertexProbability, Fin.sum_univ_succ, add_assoc] using hP
  · simpa [edgeMass, edgeProbability, Fin.sum_univ_succ, add_assoc] using hW
  · intro i
    fin_cases i <;>
      simp [vertexProbability, degree, edgeProbability, edges, Fin.sum_univ_succ] <;> linarith

theorem balance_equations (p : Sum (Fin 12) (Fin 12) → ℝ) (hp : Feasible p) :
    p (.inl 1) + vertexMass p = 1/2 ∧
    p (.inl 1) + edgeMass p = 1/2 ∧
    (∀ i, vertexMass p - vertexProbability p i + degree p i = 1/2) ∧
    p (.inl 0) + p (.inl 1) + vertexMass p + edgeMass p = 1 := by
  obtain ⟨_,hu,hv,hP,hW,hD⟩ := normal_form p hp
  refine ⟨?_,?_,?_,?_⟩
  · linarith
  · linarith
  · intro i
    have h := hD i
    linarith
  · linarith

theorem balanced_characters (p : Sum (Fin 12) (Fin 12) → ℝ) (hp : Feasible p) :
    ∀ j : Fin 6, ∑ i, p (.inl i) * (if vertices i j then (-1 : ℝ) else 1) = 0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hu,hv,hP,hW,hD0,hD1,hD2,hD3⟩ :=
    (real_moment_system p hp).facts
  intro j
  fin_cases j <;>
    simp [vertices, SixQubit.Orbit36.y0, SixQubit.Orbit36.y1, SixQubit.Orbit36.y2,
      SixQubit.Orbit36.y3, SixQubit.Orbit36.y4, SixQubit.Orbit36.y5, SixQubit.Orbit36.y6,
      SixQubit.Orbit36.y7, SixQubit.Orbit36.y8, SixQubit.Orbit36.y9,
      SixQubit.Orbit36.y10, SixQubit.Orbit36.y11, SixQubit.Orbit36.bs,
      Fin.sum_univ_succ] <;> linarith

end MainTheory.Orbit36MomentNormalForm
