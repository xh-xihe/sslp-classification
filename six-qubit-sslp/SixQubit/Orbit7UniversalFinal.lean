import SixQubit.Orbit7FullSupportTarget
import SixQubit.Orbit7Collinear
import SixQubit.Orbit7TargetEnumerator
import SixQubit.Orbit7DirectMarginal

/-!
# Orbit 7: universal original-gauge certification and interval attainment

This is the top-level composition layer.  The converse starts with arbitrary
amplitudes on the two complete orbit-7 fibres, exact normalization of both
logical words, and genuine distance three.  It first works in the uniform
five-active-coordinate gauge and then transports both complete enumerators
and the literal amplitude-level marginal `Tr(P/2)` back to the manifest
representative `(0,1,1,1,2,2)`.
-/

namespace SixQubit.Orbit7Universal

open SixQubit
open SS.MacWilliams
open SixQubit.Orbit7Family
open SixQubit.Orbit7DirectMarginal

noncomputable section

/-- Internal uniform-gauge certificate.  Keeping the literal algebraic
`HasPairRankTwo` witness here is what makes the subsequent original-gauge
transport a theorem about the physical partial trace. -/
private def UniformCertificate (c d : SS.State 6 ℂ) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
    IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧ HasPairRankTwo c d

/-- The complete uniform-gauge conclusion, including the literal finite-sum
pair marginal rather than only its algebraic block normal form. -/
def UniformConclusion (c d : SS.State 6 ℂ) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
    IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧
    ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2

/-- The manifest-representative conclusion, again stated with the direct
amplitude-level partial trace. -/
def OriginalConclusion (c d : SS.State 6 ℂ) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
    IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧
    ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2

private theorem direct_rank_of_pair_rank
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hrank : HasPairRankTwo c d) :
    ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2 := by
  rcases hrank with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [direct_uniform_eq_pairMarginal c d hc hd hcode s]
  exact hs

private theorem uniformCertificate_of_target
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (htarget : TargetStar c d) :
    UniformCertificate c d := by
  rcases target_enumerator c d hc hd hnc hnd hcode htarget with
    ⟨a, ha0, ha1, hA, hB⟩
  have hrank := pairRankTwo_of_targetStar
    c d hc hd hnc hnd hcode htarget
  exact ⟨a, ha0, ha1, hA, hB, hrank⟩

private theorem uniformCertificate_of_collinear
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : extremeDet c d = 0) :
    UniformCertificate c d := by
  rcases collinear_enumerator c d hc hd hnc hnd hcode hcol with
    ⟨a, ha0, ha1, hA, hB⟩
  have hrank := collinear_has_pair_rank_two
    c d hc hd hnc hnd hcode hcol
  exact ⟨a, ha0, ha1, hA, hB, hrank⟩

/-- Internal branch composition.  `boundary_reduction` first removes every
non-full support pattern.  On full support, the extreme spinors are either
collinear (the endpoint theorem) or independent (the full tangent and
exceptional-projector theorem). -/
private theorem uniform_certificate
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    UniformCertificate c d := by
  rcases boundary_reduction c d hc hd hnc hnd hcode with htarget | hfull
  · exact uniformCertificate_of_target c d hc hd hnc hnd hcode htarget
  · by_cases hcol : extremeDet c d = 0
    · exact uniformCertificate_of_collinear c d hc hd hnc hnd hcode hcol
    · have htarget := full_support_independent_target
        c d hc hd hnc hnd hcode hfull hcol
      exact uniformCertificate_of_target c d hc hd hnc hnd hcode htarget

/-- **Universal uniform-gauge converse.**  No support pattern, tangent,
chart, nonzero anchor, or rank premise is assumed.  The rank conclusion is
for the direct amplitude-level two-qubit partial trace. -/
theorem uniform_universal_converse
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧
      ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2 := by
  rcases uniform_certificate c d hc hd hnc hnd hcode with
    ⟨a, ha0, ha1, hA, hB, hrank⟩
  exact ⟨a, ha0, ha1, hA, hB,
    direct_rank_of_pair_rank c d hc hd hcode hrank⟩

private theorem original_familyA_of_uniform
    (c d : SS.State 6 ℂ) (a : ℝ)
    (hA : IsFamilyA (SixQubit.Orbit7Gauge.uniformCode c d) a) :
    IsFamilyA ![c,d] a := by
  dsimp only [IsFamilyA] at hA ⊢
  simpa only [SixQubit.Orbit7Gauge.Aco_invariant] using hA

private theorem original_familyB_of_uniform
    (c d : SS.State 6 ℂ) (a : ℝ)
    (hB : IsFamilyB (SixQubit.Orbit7Gauge.uniformCode c d) a) :
    IsFamilyB ![c,d] a := by
  dsimp only [IsFamilyB] at hB ⊢
  simpa only [SixQubit.Orbit7Gauge.Bco_invariant] using hB

/-- **Universal converse in the manifest orbit-7 gauge.**  The support
hypotheses are the complete original fibres of `(0,1,1,1,2,2)`.  The fixed
cube translation and logical swap are eliminated in the conclusion: both
enumerators and the rank-two direct marginal refer to the original code
`![c,d]` itself. -/
theorem original_universal_converse
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧
      ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2 := by
  have hcert := uniform_certificate
    (SixQubit.Orbit7Gauge.bottom d) (SixQubit.Orbit7Gauge.top c)
    (SixQubit.Orbit7Gauge.bottom_full_fiber d hd)
    (SixQubit.Orbit7Gauge.top_full_fiber c hc)
    (SixQubit.Orbit7Gauge.bottom_normalized d hnd)
    (SixQubit.Orbit7Gauge.top_normalized c hnc)
    (by simpa [SixQubit.Orbit7Gauge.uniformCode] using
      SixQubit.Orbit7Gauge.hasDistance c d hcode)
  rcases hcert with ⟨a, ha0, ha1, hA, hB, hrank⟩
  have hAu : IsFamilyA (SixQubit.Orbit7Gauge.uniformCode c d) a := by
    simpa [SixQubit.Orbit7Gauge.uniformCode] using hA
  have hBu : IsFamilyB (SixQubit.Orbit7Gauge.uniformCode c d) a := by
    simpa [SixQubit.Orbit7Gauge.uniformCode] using hB
  exact ⟨a, ha0, ha1,
    original_familyA_of_uniform c d a hAu,
    original_familyB_of_uniform c d a hBu,
    direct_original_normalized_hasPairRankTwo_of_uniform
      c d hc hd hnc hnd hcode hrank⟩

/-- **Pointwise attainment of the entire closed interval.**  Besides the
explicit circle family, this wrapper records normalization, genuine KL,
both complete fibres, both exact enumerators, and the direct rank-two
two-qubit marginal. -/
theorem interval_attainment (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧
      SixQubit.Orbit7Family.alpha C S = a ∧
      (∀ k, SS.innerC (SixQubit.Orbit7Family.code C S k)
        (SixQubit.Orbit7Family.code C S k) = 1) ∧
      SS.HasDistance (SixQubit.Orbit7Family.code C S) 3 ∧
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 →
        SixQubit.Orbit7Family.w0 C S x = 0) ∧
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 →
        SixQubit.Orbit7Family.w1 C S x = 0) ∧
      IsFamilyA (SixQubit.Orbit7Family.code C S) a ∧
      IsFamilyB (SixQubit.Orbit7Family.code C S) a ∧
      ∃ s : Fin 5,
        (directPairMarginal (SixQubit.Orbit7Family.code C S) s).rank = 2 := by
  obtain ⟨C, S, hCS, hα, hcode, h0, h1, hA, hB⟩ :=
    SixQubit.Orbit7Family.attain a ha0 ha1
  have hnorm := SixQubit.Orbit7Family.normalized C S hCS
  have hconv := original_universal_converse
    (SixQubit.Orbit7Family.w0 C S) (SixQubit.Orbit7Family.w1 C S)
    h0 h1 (hnorm 0) (hnorm 1)
    (by simpa [SixQubit.Orbit7Family.code] using hcode)
  rcases hconv with ⟨_a', _ha0', _ha1', _hA', _hB', hrank⟩
  refine ⟨C, S, hCS, hα, hnorm, hcode, h0, h1, hA, hB, ?_⟩
  simpa [SixQubit.Orbit7Family.code] using hrank

/-- A single theorem exposing both the universal original-gauge converse and
pointwise attainment of every parameter in `[0,1]`. -/
theorem fully_certified :
    (∀ (c d : SS.State 6 ℂ),
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 → c x = 0) →
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 → d x = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c,d] 3 →
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
        IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a ∧
        ∃ s : Fin 5, (directPairMarginal ![c,d] s).rank = 2) ∧
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ∃ C S : ℝ, C^2 + S^2 = 1 ∧
        SixQubit.Orbit7Family.alpha C S = a ∧
        (∀ k, SS.innerC (SixQubit.Orbit7Family.code C S k)
          (SixQubit.Orbit7Family.code C S k) = 1) ∧
        SS.HasDistance (SixQubit.Orbit7Family.code C S) 3 ∧
        (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 →
          SixQubit.Orbit7Family.w0 C S x = 0) ∧
        (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 →
          SixQubit.Orbit7Family.w1 C S x = 0) ∧
        IsFamilyA (SixQubit.Orbit7Family.code C S) a ∧
        IsFamilyB (SixQubit.Orbit7Family.code C S) a ∧
        ∃ s : Fin 5,
          (directPairMarginal (SixQubit.Orbit7Family.code C S) s).rank = 2) := by
  constructor
  · intro c d hc hd hnc hnd hcode
    exact original_universal_converse c d hc hd hnc hnd hcode
  · intro a ha0 ha1
    exact interval_attainment a ha0 ha1

end

end SixQubit.Orbit7Universal
