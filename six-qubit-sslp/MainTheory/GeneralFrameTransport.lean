import MainTheory.PermutationSemanticTransport
import MainTheory.IntrinsicTransport

/-! # Physical Boolean symmetries preserve KL at arbitrary logical rank -/

namespace MainTheory.GeneralFrameTransport

open SixQubit.CodeEquiv

noncomputable section

variable {n K d : ℕ}

theorem klCondition_iff_corr (p : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    SS.KLCondition p P ↔
      ∃ c : ℂ, ∀ j k, corr (p j) (p k) P.x P.z = if j = k then c else 0 := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c / Complex.I ^ P.numY, fun j k => ?_⟩
    have h := hc j k
    rw [innerC_eq_corr] at h
    by_cases hjk : j = k
    · simp only [hjk, if_true] at h ⊢
      exact (eq_div_iff (SS.pauliPrefactor_ne_zero P)).2 (by simpa [mul_comm] using h)
    · simp only [hjk, if_false] at h ⊢
      exact (mul_eq_zero.mp h).resolve_left (SS.pauliPrefactor_ne_zero P)
  · rintro ⟨c, hc⟩
    refine ⟨Complex.I ^ P.numY * c, fun j k => ?_⟩
    rw [innerC_eq_corr, hc]
    by_cases hjk : j = k <;> simp [hjk]

theorem hasDistance_bxor (p : Fin K → SS.State n ℂ)
    (f : SS.BitString n) (h : SS.HasDistance p d) :
    SS.HasDistance (fun k s => p k (SS.bxor s f)) d := by
  intro P hP
  obtain ⟨c, hc⟩ := (klCondition_iff_corr p P).1 (h P hP)
  apply (klCondition_iff_corr _ P).2
  refine ⟨SS.signC (SS.bdot P.z f) c, fun j k => ?_⟩
  change corr (flipAct f (p j)) (flipAct f (p k)) P.x P.z = _
  rw [corr_flipAct, hc]
  by_cases hjk : j = k <;> simp [hjk, SS.signC]

theorem hasDistance_permAct (sigma : Equiv.Perm (Fin n))
    (p : Fin K → SS.State n ℂ) (h : SS.HasDistance p d) :
    SS.HasDistance (fun k => permAct sigma (p k)) d := by
  intro P hP
  let P' : SS.PauliString n := ⟨permStr sigma P.x, permStr sigma P.z⟩
  have hP' : P'.wt ≤ d - 1 := by
    simpa only [P', wt_permStr] using hP
  obtain ⟨c, hc⟩ := (klCondition_iff_corr p P').1 (h P' hP')
  apply (klCondition_iff_corr _ P).2
  exact ⟨c, fun j k => by rw [corr_permAct]; exact hc j k⟩

def shiftExactCode (C : CodeSpec.ExactCode n K d) (f : SS.BitString n) :
    CodeSpec.ExactCode n K d where
  positiveRank := C.positiveRank
  frame := IntrinsicTransport.shiftFrame C.frame f
  hasDistance := hasDistance_bxor C.frame.vec f C.hasDistance

def permExactCode (C : CodeSpec.ExactCode n K d) (sigma : Equiv.Perm (Fin n)) :
    CodeSpec.ExactCode n K d where
  positiveRank := C.positiveRank
  frame := PermutationFrameBridge.permFrame C.frame sigma
  hasDistance := hasDistance_permAct sigma C.frame.vec C.hasDistance

end

end MainTheory.GeneralFrameTransport
