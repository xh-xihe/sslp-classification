import MainTheory.Generated.Orbit31SupportCoverage.Aggregate
import MainTheory.Orbit31SignedSupport

/-! Counts bind the actual support certificates and literal overlap predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31NoSingletonCounts
open MainTheory.Orbit31SupportCoverageBase
open MainTheory.Orbit31SignedSupport
open MainTheory.Generated.Orbit31SupportCoverage

theorem count0_records : ((Shard000.records.zipIdx 0).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 0 := by decide +kernel

theorem count0 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard000.certificates j) = true ∧ noSingleton (0+j.val) = true).card = 0 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard000.records.zipIdx 0) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count0_records] at h
  simpa only [List.length_zipIdx,Shard000.length,List.getElem_zipIdx,
    Shard000.certificates,Bool.and_eq_true] using h

theorem count1_records : ((Shard001.records.zipIdx 4096).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 0 := by decide +kernel

theorem count1 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard001.certificates j) = true ∧ noSingleton (4096+j.val) = true).card = 0 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard001.records.zipIdx 4096) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count1_records] at h
  simpa only [List.length_zipIdx,Shard001.length,List.getElem_zipIdx,
    Shard001.certificates,Bool.and_eq_true] using h

theorem count2_records : ((Shard002.records.zipIdx 8192).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 0 := by decide +kernel

theorem count2 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard002.certificates j) = true ∧ noSingleton (8192+j.val) = true).card = 0 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard002.records.zipIdx 8192) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count2_records] at h
  simpa only [List.length_zipIdx,Shard002.length,List.getElem_zipIdx,
    Shard002.certificates,Bool.and_eq_true] using h

theorem count3_records : ((Shard003.records.zipIdx 12288).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count3 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard003.certificates j) = true ∧ noSingleton (12288+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard003.records.zipIdx 12288) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count3_records] at h
  simpa only [List.length_zipIdx,Shard003.length,List.getElem_zipIdx,
    Shard003.certificates,Bool.and_eq_true] using h

theorem count4_records : ((Shard004.records.zipIdx 16384).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 0 := by decide +kernel

theorem count4 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard004.certificates j) = true ∧ noSingleton (16384+j.val) = true).card = 0 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard004.records.zipIdx 16384) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count4_records] at h
  simpa only [List.length_zipIdx,Shard004.length,List.getElem_zipIdx,
    Shard004.certificates,Bool.and_eq_true] using h

theorem count5_records : ((Shard005.records.zipIdx 20480).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count5 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard005.certificates j) = true ∧ noSingleton (20480+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard005.records.zipIdx 20480) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count5_records] at h
  simpa only [List.length_zipIdx,Shard005.length,List.getElem_zipIdx,
    Shard005.certificates,Bool.and_eq_true] using h

theorem count6_records : ((Shard006.records.zipIdx 24576).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count6 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard006.certificates j) = true ∧ noSingleton (24576+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard006.records.zipIdx 24576) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count6_records] at h
  simpa only [List.length_zipIdx,Shard006.length,List.getElem_zipIdx,
    Shard006.certificates,Bool.and_eq_true] using h

theorem count7_records : ((Shard007.records.zipIdx 28672).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 360 := by decide +kernel

theorem count7 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard007.certificates j) = true ∧ noSingleton (28672+j.val) = true).card = 360 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard007.records.zipIdx 28672) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count7_records] at h
  simpa only [List.length_zipIdx,Shard007.length,List.getElem_zipIdx,
    Shard007.certificates,Bool.and_eq_true] using h

theorem count8_records : ((Shard008.records.zipIdx 32768).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 0 := by decide +kernel

theorem count8 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard008.certificates j) = true ∧ noSingleton (32768+j.val) = true).card = 0 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard008.records.zipIdx 32768) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count8_records] at h
  simpa only [List.length_zipIdx,Shard008.length,List.getElem_zipIdx,
    Shard008.certificates,Bool.and_eq_true] using h

theorem count9_records : ((Shard009.records.zipIdx 36864).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count9 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard009.certificates j) = true ∧ noSingleton (36864+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard009.records.zipIdx 36864) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count9_records] at h
  simpa only [List.length_zipIdx,Shard009.length,List.getElem_zipIdx,
    Shard009.certificates,Bool.and_eq_true] using h

theorem count10_records : ((Shard010.records.zipIdx 40960).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count10 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard010.certificates j) = true ∧ noSingleton (40960+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard010.records.zipIdx 40960) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count10_records] at h
  simpa only [List.length_zipIdx,Shard010.length,List.getElem_zipIdx,
    Shard010.certificates,Bool.and_eq_true] using h

theorem count11_records : ((Shard011.records.zipIdx 45056).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 360 := by decide +kernel

theorem count11 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard011.certificates j) = true ∧ noSingleton (45056+j.val) = true).card = 360 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard011.records.zipIdx 45056) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count11_records] at h
  simpa only [List.length_zipIdx,Shard011.length,List.getElem_zipIdx,
    Shard011.certificates,Bool.and_eq_true] using h

theorem count12_records : ((Shard012.records.zipIdx 49152).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 169 := by decide +kernel

theorem count12 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard012.certificates j) = true ∧ noSingleton (49152+j.val) = true).card = 169 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard012.records.zipIdx 49152) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count12_records] at h
  simpa only [List.length_zipIdx,Shard012.length,List.getElem_zipIdx,
    Shard012.certificates,Bool.and_eq_true] using h

theorem count13_records : ((Shard013.records.zipIdx 53248).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 360 := by decide +kernel

theorem count13 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard013.certificates j) = true ∧ noSingleton (53248+j.val) = true).card = 360 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard013.records.zipIdx 53248) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count13_records] at h
  simpa only [List.length_zipIdx,Shard013.length,List.getElem_zipIdx,
    Shard013.certificates,Bool.and_eq_true] using h

theorem count14_records : ((Shard014.records.zipIdx 57344).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 360 := by decide +kernel

theorem count14 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard014.certificates j) = true ∧ noSingleton (57344+j.val) = true).card = 360 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard014.records.zipIdx 57344) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count14_records] at h
  simpa only [List.length_zipIdx,Shard014.length,List.getElem_zipIdx,
    Shard014.certificates,Bool.and_eq_true] using h

theorem count15_records : ((Shard015.records.zipIdx 61440).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = 449 := by decide +kernel

theorem count15 : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Shard015.certificates j) = true ∧ noSingleton (61440+j.val) = true).card = 449 := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    (Shard015.records.zipIdx 61440) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count15_records] at h
  simpa only [List.length_zipIdx,Shard015.length,List.getElem_zipIdx,
    Shard015.certificates,Bool.and_eq_true] using h

def counts : Fin 16 → ℕ := ![0,0,0,169,0,169,169,360,0,169,169,360,169,360,360,449]

theorem count (i : Fin 16) : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (Aggregate.certificates i j) = true ∧
      noSingleton (4096*i.val+j.val) = true).card = counts i := by
  fin_cases i
  · exact count0
  · exact count1
  · exact count2
  · exact count3
  · exact count4
  · exact count5
  · exact count6
  · exact count7
  · exact count8
  · exact count9
  · exact count10
  · exact count11
  · exact count12
  · exact count13
  · exact count14
  · exact count15

theorem count_total : (∑ i, counts i) = 2903 := by decide +kernel

end MainTheory.Generated.Orbit31NoSingletonCounts
