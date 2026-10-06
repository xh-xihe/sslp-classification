import MainTheory.Orbit14SliceGeometry
import MainTheory.Orbit14BlockFrames
import MainTheory.Orbit14EdgeRows
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit14OrthogonalFrames
open scoped BigOperators Matrix
open SixQubit.Orbit14 MainTheory.Orbit14ParityFrames MainTheory.Orbit14BlockFrames
open MainTheory.Orbit14EdgeRows MainTheory.Orbit26DependentAnchors
noncomputable section

def reverse (i : Fin 4) : Fin 4 := ![3,2,1,0] i
def bottom (c : SS.State 6 ℂ) (r : Bool) (i : Fin 4) : Vec := bottomSpinor c (blockIndex r i)
def top (d : SS.State 6 ℂ) (r : Bool) (i : Fin 4) : Vec := topSpinor d (blockIndex r (reverse i))
def mass (c : SS.State 6 ℂ) (r : Bool) : ℝ := ∑ i,nsq (bottom c r i)

theorem actual_adjacency : ∀ (r : Bool) (i j : Fin 4),i≠j →
    middleAdjacent (bottomLabels (blockIndex r i)) (topLabels (blockIndex r (reverse j))) := by
  simp_rw [middle_adjacent_checked]
  decide +kernel

theorem sum_reverse {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) :
    (∑ i,f (reverse i))=∑ i,f i := by
  let e : Fin 4 ≃ Fin 4 := ⟨reverse,reverse,by decide +kernel,by decide +kernel⟩
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem physical_mass_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ r,(∑ i,nsq (top d r i))=mass c r) ∧
      (∀ r i,nsq (bottom c r i)+nsq (top d r i)=mass c r/2) ∧
      mass c false+mass c true=1 := by
  have hm := moments c d hc hd hnc hnd hkl
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := hm.sliceData
  have hn := hm.n0
  refine ⟨?_,?_,?_⟩
  · intro r
    change (∑ i,nsq (topSpinor d (blockIndex r (reverse i))))=mass c r
    rw [sum_reverse (fun i => nsq (topSpinor d (blockIndex r i)))]
    cases r
    all_goals norm_num [mass,bottom,top,blockIndex,reverse,bottomSpinor,topSpinor,
      bottomWords,bottomWordsOne,topWords,topWordsOne,nsq,Fin.sum_univ_succ,Fin.succ,
      Matrix.vecHead,Matrix.vecTail]
    all_goals linarith
  · intro r i
    cases r <;> fin_cases i
    all_goals norm_num [mass,bottom,top,blockIndex,reverse,bottomSpinor,topSpinor,
      bottomWords,bottomWordsOne,topWords,topWordsOne,nsq,Fin.sum_univ_succ,Fin.succ,
      Matrix.vecHead,Matrix.vecTail]
    all_goals linarith
  · norm_num [mass,bottom,blockIndex,bottomSpinor,bottomWords,bottomWordsOne,nsq,
      Fin.sum_univ_succ,Fin.succ]
    linear_combination hn

theorem physical_orthogonal_frames (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Bool) (hpos : 0 < mass c r) :
    ∃ v : Vec,nsq v=1 ∧ Module.finrank ℂ (ℂ ∙ v)=1 ∧
      (∀ i,∃ t : ℂ,bottom c r i=t • v) ∧
      (∀ j,star v ⬝ᵥ top d r j=0) ∧
      bottomBlockFrame c r=(mass c r : ℂ) • projector v ∧
      topBlockFrame d r=(mass c r : ℂ) • (1-projector v) := by
  obtain ⟨hmd,hb,_⟩ := physical_mass_rows c d hc hd hnc hnd hkl
  have ho : ∀ i j,i≠j → star (bottom c r i) ⬝ᵥ top d r j=0 := by
    intro i j hij
    exact physical_edge_rows c d hc hd hnc hnd hkl _ _ (actual_adjacency r i j hij)
  obtain ⟨v,hv,hl,hcv,hdv,hCf,hDf⟩ :=
    MainTheory.Orbit14SliceGeometry.balanced_slice_frames (bottom c r) (top d r)
      (mass c r) hpos rfl (hmd r) (hb r) ho
  refine ⟨v,hv,hl,hcv,hdv,hCf,?_⟩
  have he : (∑ i,projector (top d r i))=topBlockFrame d r :=
    sum_reverse (fun i => projector (topSpinor d (blockIndex r i)))
  exact he.symm.trans hDf

theorem physical_positive_block (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∃ r : Bool,0 < mass c r := by
  have hm := (physical_mass_rows c d hc hd hnc hnd hkl).2.2
  by_cases h0 : 0 < mass c false
  · exact ⟨false,h0⟩
  · exact ⟨true,by linarith [le_of_not_gt h0]⟩

end
end MainTheory.Orbit14OrthogonalFrames
