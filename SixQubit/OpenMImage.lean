import SixQubit.Generated.OpenMParity.Support
import SixQubit.OpenMModel
import SixQubit.ParityMomentEnumerator
import MainTheory.WImages

/-!
# The full M interval in the six-qubit parity orbit

The generated states come from an explicit SO(5) shell frame and local
Cliffords. Their coefficients, normalization, full distance-three KL system,
and low-weight trace polynomials are independently checked by the kernel.
The parameter theorem covers the whole closed interval, including 2/3.
-/

namespace SixQubit.OpenMParity.Image

open MainTheory SixQubit.OpenMParity SixQubit.Orbit8Family SS.MacWilliams

noncomputable section

set_option maxRecDepth 10000

variable (T : SixQubit.ParityMomentFamily.Certificate) (hden : T.denominator = 32)
  (hmodel : ∀ P : SS.PauliString 6, P.wt ≤ 3 →
    CircleZero (QuadZ.sub
      (SixQubit.ParityCircleFamily.qtrace T.c0 T.c1
        T.L0 T.L1 P) (traceModel P)))

include hden hmodel

theorem Aco_one (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (T.state C S) 1 = 0 := by
  rw [T.Aco_eq_list_model C S hCS 1 traceList1 traceList1_nodup
    traceList1_weight traceModel (fun P hw => hmodel P (by omega)) traceList1_support]
  simpa only [hden] using model_sum_one C S

theorem Aco_two (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (T.state C S) 2 = 4 * parameter C := by
  rw [T.Aco_eq_list_model C S hCS 2 traceList2 traceList2_nodup
    traceList2_weight traceModel (fun P hw => hmodel P (by omega)) traceList2_support]
  simpa only [hden] using model_sum_two C S hCS

theorem Aco_three (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (T.state C S) 3 = 4 * (1 - parameter C) := by
  rw [T.Aco_eq_list_model C S hCS 3 traceList3 traceList3_nodup
    traceList3_weight traceModel (fun P hw => hmodel P (by omega)) traceList3_support]
  simpa only [hden] using model_sum_three C S hCS

/-- The normalized, complete seven-coefficient enumerator of the actual code. -/
theorem normalized_A (C S : ℝ) (hCS : C^2 + S^2 = 1) (j : Fin 7) :
    WImages.FII (parameter C) j = Aco (T.state C S) j / 4 := by
  have h0 := SixQubit.Pin.Aco_zero (T.state C S) (T.normalized C S hCS)
  have h1 := Aco_one T hden hmodel C S hCS
  have h2 := Aco_two T hden hmodel C S hCS
  have h3 := Aco_three T hden hmodel C S hCS
  obtain ⟨h4, h5, h6⟩ := macwilliams_six (T.state C S)
    (T.hasDistance C S hCS) h0
  fin_cases j <;> norm_num [WImages.FII] <;> linarith

/-- Every M(t), 2/3 ≤ t ≤ 1, is attained in orbit 4's two parity fibers. -/
theorem FII_subset_WImage :
    WImages.FII '' Set.Icc (2/3 : ℝ) 1 ⊆ Levels.WImage T.angle 0 1 := by
  rintro A ⟨t, ht, rfl⟩
  obtain ⟨C, S, hCS, hparameter⟩ := exists_parameter t ht.1 ht.2
  refine ⟨T.word T.c0 C S, T.word T.c1 C S,
    T.supported0 C S, T.supported1 C S,
    T.normalized C S hCS 0, T.normalized C S hCS 1,
    T.hasDistance C S hCS, ?_⟩
  intro j
  rw [← hparameter]
  exact normalized_A T hden hmodel C S hCS j

end

end SixQubit.OpenMParity.Image
