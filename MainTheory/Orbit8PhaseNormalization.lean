import MainTheory.Orbit8ShellDisplays
import MainTheory.CodeSpec

set_option autoImplicit false

namespace MainTheory.Orbit8PhaseNormalization

open SixQubit.Orbit8Universal

theorem rephase_distance {n K d : ℕ} (f : Fin K → SS.State n ℂ)
    (z : Fin K → ℂ) (hz : ∀ i,star (z i)*z i=1) (hd : SS.HasDistance f d) :
    SS.HasDistance (fun i => z i • f i) d := by
  intro P hP
  obtain ⟨a,ha⟩ := hd P hP
  refine ⟨a,?_⟩
  intro i j
  rw [MainTheory.CodeSpec.pauliAct_smul,MainTheory.CodeSpec.innerC_smul_left,
    MainTheory.CodeSpec.innerC_smul_right,ha]
  by_cases hij : i=j
  · subst j
    simp only [← mul_assoc,hz,one_mul]
  · simp [hij]

noncomputable def b : ℝ := (Real.sqrt 6)⁻¹

theorem b_pos : 0 < b := by unfold b; positivity
theorem b_square : b^2=(1/6 : ℝ) := by
  unfold b
  rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

noncomputable def phase (c : SS.State 6 ℂ) : ℂ := (b : ℂ)/ball c

theorem phase_unit (c : SS.State 6 ℂ) (hb : Complex.normSq (ball c)=1/6) :
    star (phase c)*phase c=1 := by
  rw [SixQubit.star_mul_self]
  have h : Complex.normSq (phase c)=1 := by
    rw [phase,Complex.normSq_div,Complex.normSq_ofReal,hb,← pow_two,b_square]
    norm_num
  rw [h]
  norm_num

theorem normalized_ball (c : SS.State 6 ℂ) (hc : ball c ≠ 0) :
    ball (phase c • c)=(b : ℂ) := by
  change ((b : ℂ)/ball c)*ball c=(b : ℂ)
  exact div_mul_cancel₀ _ hc

theorem normalized_pair (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ball (phase c • c)=(b : ℂ) ∧
    (∀ x,SS.weight av x ≠ 0 → (phase c • c) x=0) ∧
    SS.innerC (phase c • c) (phase c • c)=1 ∧
    SS.HasDistance ![phase c • c,d] 3 := by
  obtain ⟨hb,_,hb0⟩ := rigid_coordinate_norms c d hc hd hnc hnd hcode
  have hz := phase_unit c hb
  refine ⟨normalized_ball c hb0,?_,?_,?_⟩
  · intro x hx
    simp [hc x hx]
  · rw [MainTheory.CodeSpec.innerC_smul_left,MainTheory.CodeSpec.innerC_smul_right,hnc]
    simpa using hz
  · have h := rephase_distance ![c,d] (![phase c,1] : Fin 2 → ℂ)
      (by intro i; fin_cases i; exact hz; simp) hcode
    have he : (fun i : Fin 2 => (![phase c,1] : Fin 2 → ℂ) i • (![c,d] i))=
        ![phase c • c,d] := by ext i x; fin_cases i <;> simp
    rwa [he] at h

end MainTheory.Orbit8PhaseNormalization
