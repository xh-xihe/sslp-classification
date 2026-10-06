-- Generated proof-only aggregation for representative 74.
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009
import MainTheory.BinaryDetSymmetry

namespace MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate

open MainTheory.BinaryDetFast
open MainTheory.BinaryDetSymmetry

theorem slice_00 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 0 9 := by
  unfold FastRowSlice
  rw [show List.range' 0 (64 - 0) =
        List.range' 0 16 ++
        List.range' 16 16 ++
        List.range' 32 16 ++
        List.range' 48 16 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 0 0 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 0 16 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 0 32 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 0 48 16 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_00_00, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_00_16, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_00_32, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_00_48⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_01 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 1 9 := by
  unfold FastRowSlice
  rw [show List.range' 1 (64 - 1) =
        List.range' 1 16 ++
        List.range' 17 16 ++
        List.range' 33 16 ++
        List.range' 49 15 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 1 1 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 1 17 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 1 33 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 1 49 15 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_01_01, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_01_17, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_01_33, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_01_49⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_02 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 2 9 := by
  unfold FastRowSlice
  rw [show List.range' 2 (64 - 2) =
        List.range' 2 16 ++
        List.range' 18 16 ++
        List.range' 34 16 ++
        List.range' 50 14 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 2 2 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 2 18 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 2 34 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 2 50 14 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_02_02, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_02_18, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_02_34, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_02_50⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_03 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 3 9 := by
  unfold FastRowSlice
  rw [show List.range' 3 (64 - 3) =
        List.range' 3 16 ++
        List.range' 19 16 ++
        List.range' 35 16 ++
        List.range' 51 13 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 3 3 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 3 19 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 3 35 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 3 51 13 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_03_03, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_03_19, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_03_35, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard000.chunk_03_51⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_04 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 4 9 := by
  unfold FastRowSlice
  rw [show List.range' 4 (64 - 4) =
        List.range' 4 16 ++
        List.range' 20 16 ++
        List.range' 36 16 ++
        List.range' 52 12 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 4 4 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 4 20 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 4 36 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 4 52 12 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_04_04, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_04_20, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_04_36, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_04_52⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_05 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 5 9 := by
  unfold FastRowSlice
  rw [show List.range' 5 (64 - 5) =
        List.range' 5 16 ++
        List.range' 21 16 ++
        List.range' 37 16 ++
        List.range' 53 11 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 5 5 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 5 21 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 5 37 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 5 53 11 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_05_05, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_05_21, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_05_37, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_05_53⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_06 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 6 9 := by
  unfold FastRowSlice
  rw [show List.range' 6 (64 - 6) =
        List.range' 6 16 ++
        List.range' 22 16 ++
        List.range' 38 16 ++
        List.range' 54 10 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 6 6 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 6 22 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 6 38 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 6 54 10 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_06_06, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_06_22, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_06_38, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_06_54⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_07 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 7 9 := by
  unfold FastRowSlice
  rw [show List.range' 7 (64 - 7) =
        List.range' 7 16 ++
        List.range' 23 16 ++
        List.range' 39 16 ++
        List.range' 55 9 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 7 7 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 7 23 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 7 39 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 7 55 9 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_07_07, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_07_23, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_07_39, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard001.chunk_07_55⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_08 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 8 9 := by
  unfold FastRowSlice
  rw [show List.range' 8 (64 - 8) =
        List.range' 8 16 ++
        List.range' 24 16 ++
        List.range' 40 16 ++
        List.range' 56 8 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 8 8 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 8 24 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 8 40 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 8 56 8 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_08_08, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_08_24, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_08_40, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_08_56⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_09 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 9 := by
  unfold FastRowSlice
  rw [show List.range' 9 (64 - 9) =
        List.range' 9 16 ++
        List.range' 25 16 ++
        List.range' 41 16 ++
        List.range' 57 7 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 9 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 25 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 41 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 57 7 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_09_09, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_09_25, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_09_41, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_09_57⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_10 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 10 9 := by
  unfold FastRowSlice
  rw [show List.range' 10 (64 - 10) =
        List.range' 10 16 ++
        List.range' 26 16 ++
        List.range' 42 16 ++
        List.range' 58 6 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 10 10 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 10 26 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 10 42 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 10 58 6 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_10_10, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_10_26, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_10_42, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_10_58⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_11 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 11 9 := by
  unfold FastRowSlice
  rw [show List.range' 11 (64 - 11) =
        List.range' 11 16 ++
        List.range' 27 16 ++
        List.range' 43 16 ++
        List.range' 59 5 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 11 11 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 11 27 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 11 43 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 11 59 5 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_11_11, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_11_27, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_11_43, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard002.chunk_11_59⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_12 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 12 9 := by
  unfold FastRowSlice
  rw [show List.range' 12 (64 - 12) =
        List.range' 12 16 ++
        List.range' 28 16 ++
        List.range' 44 16 ++
        List.range' 60 4 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 12 12 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 12 28 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 12 44 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 12 60 4 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_12_12, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_12_28, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_12_44, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_12_60⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_13 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 13 9 := by
  unfold FastRowSlice
  rw [show List.range' 13 (64 - 13) =
        List.range' 13 16 ++
        List.range' 29 16 ++
        List.range' 45 16 ++
        List.range' 61 3 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 13 13 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 13 29 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 13 45 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 13 61 3 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_13_13, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_13_29, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_13_45, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_13_61⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_14 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 14 9 := by
  unfold FastRowSlice
  rw [show List.range' 14 (64 - 14) =
        List.range' 14 16 ++
        List.range' 30 16 ++
        List.range' 46 16 ++
        List.range' 62 2 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 14 14 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 14 30 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 14 46 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 14 62 2 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_14_14, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_14_30, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_14_46, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_14_62⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_15 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 15 9 := by
  unfold FastRowSlice
  rw [show List.range' 15 (64 - 15) =
        List.range' 15 16 ++
        List.range' 31 16 ++
        List.range' 47 16 ++
        List.range' 63 1 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 15 15 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 15 31 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 15 47 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 15 63 1 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_15_15, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_15_31, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_15_47, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard003.chunk_15_63⟩⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_16 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 16 9 := by
  unfold FastRowSlice
  rw [show List.range' 16 (64 - 16) =
        List.range' 16 16 ++
        List.range' 32 16 ++
        List.range' 48 16 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 16 16 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 16 32 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 16 48 16 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_16_16, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_16_32, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_16_48⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_17 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 17 9 := by
  unfold FastRowSlice
  rw [show List.range' 17 (64 - 17) =
        List.range' 17 16 ++
        List.range' 33 16 ++
        List.range' 49 15 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 17 17 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 17 33 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 17 49 15 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_17_17, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_17_33, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_17_49⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_18 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 18 9 := by
  unfold FastRowSlice
  rw [show List.range' 18 (64 - 18) =
        List.range' 18 16 ++
        List.range' 34 16 ++
        List.range' 50 14 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 18 18 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 18 34 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 18 50 14 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_18_18, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_18_34, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_18_50⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_19 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 19 9 := by
  unfold FastRowSlice
  rw [show List.range' 19 (64 - 19) =
        List.range' 19 16 ++
        List.range' 35 16 ++
        List.range' 51 13 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 19 19 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 19 35 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 19 51 13 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_19_19, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_19_35, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_19_51⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_20 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 20 9 := by
  unfold FastRowSlice
  rw [show List.range' 20 (64 - 20) =
        List.range' 20 16 ++
        List.range' 36 16 ++
        List.range' 52 12 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 20 20 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 20 36 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 20 52 12 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_20_20, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_20_36, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_20_52⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_21 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 21 9 := by
  unfold FastRowSlice
  rw [show List.range' 21 (64 - 21) =
        List.range' 21 16 ++
        List.range' 37 16 ++
        List.range' 53 11 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 21 21 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 21 37 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 21 53 11 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard004.chunk_21_21, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_21_37, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_21_53⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_22 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 22 9 := by
  unfold FastRowSlice
  rw [show List.range' 22 (64 - 22) =
        List.range' 22 16 ++
        List.range' 38 16 ++
        List.range' 54 10 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 22 22 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 22 38 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 22 54 10 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_22_22, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_22_38, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_22_54⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_23 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 23 9 := by
  unfold FastRowSlice
  rw [show List.range' 23 (64 - 23) =
        List.range' 23 16 ++
        List.range' 39 16 ++
        List.range' 55 9 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 23 23 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 23 39 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 23 55 9 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_23_23, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_23_39, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_23_55⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_24 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 24 9 := by
  unfold FastRowSlice
  rw [show List.range' 24 (64 - 24) =
        List.range' 24 16 ++
        List.range' 40 16 ++
        List.range' 56 8 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 24 24 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 24 40 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 24 56 8 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_24_24, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_24_40, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_24_56⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_25 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 25 9 := by
  unfold FastRowSlice
  rw [show List.range' 25 (64 - 25) =
        List.range' 25 16 ++
        List.range' 41 16 ++
        List.range' 57 7 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 25 25 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 25 41 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 25 57 7 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_25_25, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_25_41, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_25_57⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_26 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 26 9 := by
  unfold FastRowSlice
  rw [show List.range' 26 (64 - 26) =
        List.range' 26 16 ++
        List.range' 42 16 ++
        List.range' 58 6 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 26 26 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 26 42 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 26 58 6 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_26_26, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard005.chunk_26_42, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_26_58⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_27 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 27 9 := by
  unfold FastRowSlice
  rw [show List.range' 27 (64 - 27) =
        List.range' 27 16 ++
        List.range' 43 16 ++
        List.range' 59 5 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 27 27 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 27 43 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 27 59 5 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_27_27, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_27_43, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_27_59⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_28 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 28 9 := by
  unfold FastRowSlice
  rw [show List.range' 28 (64 - 28) =
        List.range' 28 16 ++
        List.range' 44 16 ++
        List.range' 60 4 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 28 28 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 28 44 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 28 60 4 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_28_28, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_28_44, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_28_60⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_29 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 29 9 := by
  unfold FastRowSlice
  rw [show List.range' 29 (64 - 29) =
        List.range' 29 16 ++
        List.range' 45 16 ++
        List.range' 61 3 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 29 29 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 29 45 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 29 61 3 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_29_29, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_29_45, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_29_61⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_30 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 30 9 := by
  unfold FastRowSlice
  rw [show List.range' 30 (64 - 30) =
        List.range' 30 16 ++
        List.range' 46 16 ++
        List.range' 62 2 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 30 30 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 30 46 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 30 62 2 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_30_30, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_30_46, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_30_62⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_31 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 31 9 := by
  unfold FastRowSlice
  rw [show List.range' 31 (64 - 31) =
        List.range' 31 16 ++
        List.range' 47 16 ++
        List.range' 63 1 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 31 31 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 31 47 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 31 63 1 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_31_31, ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_31_47, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard006.chunk_31_63⟩⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_32 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 32 9 := by
  unfold FastRowSlice
  rw [show List.range' 32 (64 - 32) =
        List.range' 32 16 ++
        List.range' 48 16 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 32 32 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 32 48 16 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_32_32, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_32_48⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_33 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 33 9 := by
  unfold FastRowSlice
  rw [show List.range' 33 (64 - 33) =
        List.range' 33 16 ++
        List.range' 49 15 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 33 33 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 33 49 15 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_33_33, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_33_49⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_34 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 34 9 := by
  unfold FastRowSlice
  rw [show List.range' 34 (64 - 34) =
        List.range' 34 16 ++
        List.range' 50 14 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 34 34 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 34 50 14 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_34_34, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_34_50⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_35 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 35 9 := by
  unfold FastRowSlice
  rw [show List.range' 35 (64 - 35) =
        List.range' 35 16 ++
        List.range' 51 13 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 35 35 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 35 51 13 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_35_35, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_35_51⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_36 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 36 9 := by
  unfold FastRowSlice
  rw [show List.range' 36 (64 - 36) =
        List.range' 36 16 ++
        List.range' 52 12 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 36 36 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 36 52 12 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_36_36, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_36_52⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_37 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 37 9 := by
  unfold FastRowSlice
  rw [show List.range' 37 (64 - 37) =
        List.range' 37 16 ++
        List.range' 53 11 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 37 37 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 37 53 11 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_37_37, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_37_53⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_38 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 38 9 := by
  unfold FastRowSlice
  rw [show List.range' 38 (64 - 38) =
        List.range' 38 16 ++
        List.range' 54 10 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 38 38 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 38 54 10 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_38_38, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_38_54⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_39 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 39 9 := by
  unfold FastRowSlice
  rw [show List.range' 39 (64 - 39) =
        List.range' 39 16 ++
        List.range' 55 9 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 39 39 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 39 55 9 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_39_39, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard007.chunk_39_55⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_40 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 40 9 := by
  unfold FastRowSlice
  rw [show List.range' 40 (64 - 40) =
        List.range' 40 16 ++
        List.range' 56 8 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 40 40 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 40 56 8 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_40_40, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_40_56⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_41 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 41 9 := by
  unfold FastRowSlice
  rw [show List.range' 41 (64 - 41) =
        List.range' 41 16 ++
        List.range' 57 7 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 41 41 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 41 57 7 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_41_41, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_41_57⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_42 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 42 9 := by
  unfold FastRowSlice
  rw [show List.range' 42 (64 - 42) =
        List.range' 42 16 ++
        List.range' 58 6 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 42 42 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 42 58 6 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_42_42, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_42_58⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_43 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 43 9 := by
  unfold FastRowSlice
  rw [show List.range' 43 (64 - 43) =
        List.range' 43 16 ++
        List.range' 59 5 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 43 43 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 43 59 5 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_43_43, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_43_59⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_44 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 44 9 := by
  unfold FastRowSlice
  rw [show List.range' 44 (64 - 44) =
        List.range' 44 16 ++
        List.range' 60 4 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 44 44 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 44 60 4 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_44_44, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_44_60⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_45 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 45 9 := by
  unfold FastRowSlice
  rw [show List.range' 45 (64 - 45) =
        List.range' 45 16 ++
        List.range' 61 3 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 45 45 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 45 61 3 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_45_45, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_45_61⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_46 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 46 9 := by
  unfold FastRowSlice
  rw [show List.range' 46 (64 - 46) =
        List.range' 46 16 ++
        List.range' 62 2 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 46 46 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 46 62 2 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_46_46, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_46_62⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_47 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 47 9 := by
  unfold FastRowSlice
  rw [show List.range' 47 (64 - 47) =
        List.range' 47 16 ++
        List.range' 63 1 by decide]
  have hchunks :
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 47 47 16 9 ∧
      FastPairChunk MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 47 63 1 9 :=
    ⟨MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_47_47, MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard008.chunk_47_63⟩
  simpa only [List.forall_append, FastPairChunk, and_assoc] using hchunks

theorem slice_48 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 48 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_48_48

theorem slice_49 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 49 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_49_49

theorem slice_50 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 50 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_50_50

theorem slice_51 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 51 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_51_51

theorem slice_52 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 52 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_52_52

theorem slice_53 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 53 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_53_53

theorem slice_54 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 54 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_54_54

theorem slice_55 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 55 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_55_55

theorem slice_56 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 56 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_56_56

theorem slice_57 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 57 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_57_57

theorem slice_58 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 58 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_58_58

theorem slice_59 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 59 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_59_59

theorem slice_60 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 60 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_60_60

theorem slice_61 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 61 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_61_61

theorem slice_62 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 62 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_62_62

theorem slice_63 :
    FastRowSlice MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 63 9 := by
  simpa only [FastRowSlice, FastPairChunk] using MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Arithmetic.Shard009.chunk_63_63

/-- The 64 slices cover every unordered pair of six-bit bottom rows. -/
theorem table : FastTriangularTable MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 := by
  unfold FastTriangularTable
  rw [show List.range 64 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] by decide]
  exact ⟨slice_00,
    ⟨slice_01,
      ⟨slice_02,
        ⟨slice_03,
          ⟨slice_04,
            ⟨slice_05,
              ⟨slice_06,
                ⟨slice_07,
                  ⟨slice_08,
                    ⟨slice_09,
                      ⟨slice_10,
                        ⟨slice_11,
                          ⟨slice_12,
                            ⟨slice_13,
                              ⟨slice_14,
                                ⟨slice_15,
                                  ⟨slice_16,
                                    ⟨slice_17,
                                      ⟨slice_18,
                                        ⟨slice_19,
                                          ⟨slice_20,
                                            ⟨slice_21,
                                              ⟨slice_22,
                                                ⟨slice_23,
                                                  ⟨slice_24,
                                                    ⟨slice_25,
                                                      ⟨slice_26,
                                                        ⟨slice_27,
                                                          ⟨slice_28,
                                                            ⟨slice_29,
                                                              ⟨slice_30,
                                                                ⟨slice_31,
                                                                  ⟨slice_32,
                                                                    ⟨slice_33,
                                                                      ⟨slice_34,
                                                                        ⟨slice_35,
                                                                          ⟨slice_36,
                                                                            ⟨slice_37,
                                                                              ⟨slice_38,
                                                                                ⟨slice_39,
                                                                                  ⟨slice_40,
                                                                                    ⟨slice_41,
                                                                                      ⟨slice_42,
                                                                                        ⟨slice_43,
                                                                                          ⟨slice_44,
                                                                                            ⟨slice_45,
                                                                                              ⟨slice_46,
                                                                                                ⟨slice_47,
                                                                                                  ⟨slice_48,
                                                                                                    ⟨slice_49,
                                                                                                      ⟨slice_50,
                                                                                                        ⟨slice_51,
                                                                                                          ⟨slice_52,
                                                                                                            ⟨slice_53,
                                                                                                              ⟨slice_54,
                                                                                                                ⟨slice_55,
                                                                                                                  ⟨slice_56,
                                                                                                                    ⟨slice_57,
                                                                                                                      ⟨slice_58,
                                                                                                                        ⟨slice_59,
                                                                                                                          ⟨slice_60,
                                                                                                                            ⟨slice_61,
                                                                                                                              ⟨slice_62,
                                                                                                                                slice_63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Semantic determinant bound for all three universally quantified bottom rows. -/
theorem bottomBound : BottomDetBound MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop 9 :=
  MainTheory.BinaryDetSymmetry.ReducedBound.bottomDetBound
    (MainTheory.BinaryDetFast.FastTriangularTable.reducedBound table)

end MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate
