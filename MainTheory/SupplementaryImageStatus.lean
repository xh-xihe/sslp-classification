import MainTheory.Orbit2FullImage
import MainTheory.Orbit3FullImage
import MainTheory.ProvedWEUnion

/-! The updated thirteen-image union and the finite scope of the SI status.
The two open images are recorded as an audit scope, without asserting their
unknown converse. The image equalities below concern actual KL completions.
-/

namespace MainTheory.SupplementaryImageStatus
noncomputable section
open MainTheory

def provedImages : Set (Fin 7 → ℝ) :=
  DirectoryEnumeratorImages.directoryImage 1 ∪
  DirectoryEnumeratorImages.directoryImage 2 ∪ ProvedWEUnion.provedImages

theorem provedImages_eq : provedImages =
    WImages.FI '' Set.Icc (0 : ℝ) 1 ∪
    WImages.FII '' Set.Icc (2/3 : ℝ) 1 ∪ {WImages.R5A} := by
  rw [provedImages, Orbit2FullImage.directory_image, Orbit3FullImage.directory_image,
    ProvedWEUnion.provedImages_eq]
  ext A
  simp only [Set.mem_union]
  tauto

def provedPaperIds : Finset ℕ := {2,3,7,8,9,10,11,16,21,22,23,36,45}
def pendingPaperIds : Finset ℕ := {1,4}
def noGoPaperIds : Finset ℕ :=
  {5,6,12,13,14,15,17,18,19,20,24,25,26,27,28,29,30,31,32,33,34,35,
   37,38,39,40,41,42,43,44,46,47,48,49,50,51,52,53,54,55,56,57,58,59,
   60,61,62,63,64,65,66}

theorem status_counts : provedPaperIds.card = 13 ∧ pendingPaperIds.card = 2 ∧
    noGoPaperIds.card = 51 ∧ (provedPaperIds ∪ noGoPaperIds).card = 64 := by
  decide +kernel

theorem status_partition :
    provedPaperIds ∪ pendingPaperIds ∪ noGoPaperIds = Finset.Icc 1 66 ∧
    Disjoint provedPaperIds pendingPaperIds ∧
    Disjoint (provedPaperIds ∪ pendingPaperIds) noGoPaperIds := by
  decide +kernel

end
end MainTheory.SupplementaryImageStatus
