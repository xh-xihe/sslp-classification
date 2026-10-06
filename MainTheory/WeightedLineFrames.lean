import MainTheory.Orbit26DependentAnchors
import MainTheory.Orbit26OrthogonalGram
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.WeightedLineFrames
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors
open MainTheory.Orbit26 (M2)
noncomputable section
theorem projector_smul (t : ℂ) (v : Vec) :
    projector (t • v)=(Complex.normSq t : ℂ) • projector v := by
  ext i j
  simp only [projector,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,
    Pi.star_apply,smul_eq_mul,star_mul',Complex.normSq_eq_conj_mul_self,Complex.star_def]
  simp only [starRingEnd_apply]
  ring
theorem nsq_smul (t : ℂ) (v : Vec) : nsq (t • v)=Complex.normSq t*nsq v := by
  simp only [nsq,Pi.smul_apply,smul_eq_mul,map_mul,← Finset.mul_sum]
theorem line_frame {α : Type*} [Fintype α] (v : Vec) (t : α → ℂ) (mu : ℝ)
    (hv : nsq v=1) (hm : (∑ i,nsq (t i • v))=mu) :
    (∑ i,projector (t i • v))=(mu : ℂ) • projector v := by
  have hs : (∑ i,Complex.normSq (t i))=mu := by
    simpa only [nsq_smul,hv,mul_one] using hm
  simp_rw [projector_smul]
  rw [← Finset.sum_smul]
  have hcast : (∑ i,(Complex.normSq (t i) : ℂ))=(mu : ℂ) := by
    exact_mod_cast hs
  rw [hcast]
theorem line_frame_of_membership {α : Type*} [Fintype α]
    (v : Vec) (c : α → Vec) (mu : ℝ) (hv : nsq v=1)
    (hline : ∀ i,∃ t : ℂ,c i=t • v) (hm : (∑ i,nsq (c i))=mu) :
    (∑ i,projector (c i))=(mu : ℂ) • projector v := by
  classical
  choose t ht using hline
  have hm' : (∑ i,nsq (t i • v))=mu := by
    simpa only [← ht] using hm
  calc
    (∑ i,projector (c i))=(∑ i,projector (t i • v)) := by simp_rw [ht]
    _ = (mu : ℂ) • projector v := line_frame v t mu hv hm'
theorem orthogonal_line_frames {α β : Type*} [Fintype α] [Fintype β]
    (v w : Vec) (c : α → Vec) (d : β → Vec) (mu : ℝ)
    (hv : nsq v=1) (hw : nsq w=1)
    (hc : ∀ i,∃ t : ℂ,c i=t • v) (hd : ∀ j,∃ t : ℂ,d j=t • w)
    (hmc : (∑ i,nsq (c i))=mu) (hmd : (∑ j,nsq (d j))=mu) :
    (∑ i,projector (c i))=(mu : ℂ) • projector v ∧
    (∑ j,projector (d j))=(mu : ℂ) • projector w := by
  exact ⟨line_frame_of_membership v c mu hv hc hmc,
    line_frame_of_membership w d mu hw hd hmd⟩
theorem complementary_line_frames {α β : Type*} [Fintype α] [Fintype β]
    (v w : Vec) (c : α → Vec) (d : β → Vec) (mu : ℝ)
    (hv : nsq v=1) (hw : nsq w=1) (ho : star v ⬝ᵥ w=0)
    (hc : ∀ i,∃ t : ℂ,c i=t • v) (hd : ∀ j,∃ t : ℂ,d j=t • w)
    (hmc : (∑ i,nsq (c i))=mu) (hmd : (∑ j,nsq (d j))=mu) :
    (∑ i,projector (c i))=(mu : ℂ) • projector v ∧
    (∑ j,projector (d j))=(mu : ℂ) • (1-projector v) := by
  have hp := MainTheory.Orbit26OrthogonalGram.orthogonal_projector v w hv ho
  rw [hw,Complex.ofReal_one,one_smul] at hp
  exact ⟨line_frame_of_membership v c mu hv hc hmc,
    (line_frame_of_membership w d mu hw hd hmd).trans (congrArg (fun P : M2 => (mu : ℂ) • P) hp)⟩
end
end MainTheory.WeightedLineFrames
