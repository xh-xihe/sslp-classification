import SixQubit.Generated.Orbit3Coordinates.Data
import MainTheory.Orbit3CubicPermutation

/-! # Physical meanings of the numeric phase blocks and permutation witnesses

The generated table's integer bit masks are decoded into actual supports.
Its permutation indices denote concrete mask-preserving physical permutations.
These lemmas do not assume coordinate invariance or positivity from a caller.
-/

namespace MainTheory.Orbit3CoordinateBlocks

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3PhaseBlocks MainTheory.Orbit3CubicBasis
open SixQubit.Generated

noncomputable section

private theorem num_injective :
    Function.Injective (SixQubit.Realize.num : SS.BitString 6 → ℕ) := by
  intro a b h
  have h' := congrArg (SixQubit.Realize.nbit : ℕ → SS.BitString 6) h
  simpa only [SixQubit.Realize.nbit_num] using h'

theorem encoded_block_eq_iff (a b c d : SS.BitString 6) :
    (SixQubit.Realize.num (support a b), charge a b) =
      (SixQubit.Realize.num (support c d), charge c d) ↔
      block a b = block c d := by
  constructor
  · intro h
    apply Prod.ext
    · exact num_injective (congrArg Prod.fst h)
    · change charge a b = charge c d
      exact congrArg (fun x : ℕ × ℤ => x.2) h
  · intro h
    apply Prod.ext
    · exact congrArg SixQubit.Realize.num (congrArg Prod.fst h)
    · exact congrArg (fun x : SS.BitString 6 × ℤ => x.2) h

theorem blockTag_eq_iff (i j : Fin 715) :
    Orbit3Coordinates.Data.blockTag i = Orbit3Coordinates.Data.blockTag j ↔
      block (Orbit3CubicTriples.physical i).1 (Orbit3CubicTriples.physical i).2.1 =
        block (Orbit3CubicTriples.physical j).1 (Orbit3CubicTriples.physical j).2.1 := by
  have hi := Orbit3Coordinates.Data.block_tags_correct i
  have hj := Orbit3Coordinates.Data.block_tags_correct j
  constructor
  · intro h
    apply (encoded_block_eq_iff _ _ _ _).mp
    change Orbit3Coordinates.Data.physicalBlockLabel i =
      Orbit3Coordinates.Data.physicalBlockLabel j
    rw [hi, hj, h]
  · intro h
    apply Orbit3Coordinates.Data.block_keys_injective
    rw [← hi, ← hj]
    exact (encoded_block_eq_iff _ _ _ _).mpr h

theorem permuted_eq (g : Fin 120) (i : Fin 715) :
    Orbit3Coordinates.Data.permuted g i =
      MainTheory.Orbit3CubicPermutation.permuteIndex
        (Orbit3PermutationMetadata.actual g) i := by
  unfold Orbit3Coordinates.Data.permuted MainTheory.Orbit3CubicPermutation.permuteIndex
  congr 1
  · exact (Orbit3PermutationMetadata.bitmap_correct g (Orbit3CubicTriples.triples i).1).symm
  · exact (Orbit3PermutationMetadata.bitmap_correct g (Orbit3CubicTriples.triples i).2.1).symm

theorem moment_permuted (W : Encoder) (g : Fin 120) (i j : Fin 715) :
    moment W (Orbit3Coordinates.Data.permuted g i)
      (Orbit3Coordinates.Data.permuted g j) = moment W i j := by
  rw [permuted_eq, permuted_eq]
  exact MainTheory.Orbit3CubicPermutation.moment_permuted _ W i j

theorem zero_outside_numeric_block (W : Encoder) (i j : Fin 715)
    (h : Orbit3Coordinates.Data.blockTag i ≠ Orbit3Coordinates.Data.blockTag j) :
    moment W i j = 0 := by
  apply zero_outside_phase_block
  exact fun hb => h ((blockTag_eq_iff i j).mpr hb)

end
end MainTheory.Orbit3CoordinateBlocks
