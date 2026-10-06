import MainTheory.Generated.Orbit31SupportCoverage.Shard000
import MainTheory.Generated.Orbit31SupportCoverage.Shard001
import MainTheory.Generated.Orbit31SupportCoverage.Shard002
import MainTheory.Generated.Orbit31SupportCoverage.Shard003
import MainTheory.Generated.Orbit31SupportCoverage.Shard004
import MainTheory.Generated.Orbit31SupportCoverage.Shard005
import MainTheory.Generated.Orbit31SupportCoverage.Shard006
import MainTheory.Generated.Orbit31SupportCoverage.Shard007
import MainTheory.Generated.Orbit31SupportCoverage.Shard008
import MainTheory.Generated.Orbit31SupportCoverage.Shard009
import MainTheory.Generated.Orbit31SupportCoverage.Shard010
import MainTheory.Generated.Orbit31SupportCoverage.Shard011
import MainTheory.Generated.Orbit31SupportCoverage.Shard012
import MainTheory.Generated.Orbit31SupportCoverage.Shard013
import MainTheory.Generated.Orbit31SupportCoverage.Shard014
import MainTheory.Generated.Orbit31SupportCoverage.Shard015

/-! All support masks, including boundary faces, have a checked certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31SupportCoverage.Aggregate
open MainTheory.Orbit31SupportCoverageBase

def certificates : Fin 16 → Fin 4096 → Certificate := ![
  Shard000.certificates,
  Shard001.certificates,
  Shard002.certificates,
  Shard003.certificates,
  Shard004.certificates,
  Shard005.certificates,
  Shard006.certificates,
  Shard007.certificates,
  Shard008.certificates,
  Shard009.certificates,
  Shard010.certificates,
  Shard011.certificates,
  Shard012.certificates,
  Shard013.certificates,
  Shard014.certificates,
  Shard015.certificates]
def counts : Fin 16 → ℕ := ![0,367,367,979,367,979,979,1603,367,979,979,1603,979,1603,1603,1849]

theorem valid (i : Fin 16) : ∀ j : Fin 4096,
    Valid (4096 * i.val + j.val) (certificates i j) := by
  fin_cases i
  · exact Shard000.valid
  · exact Shard001.valid
  · exact Shard002.valid
  · exact Shard003.valid
  · exact Shard004.valid
  · exact Shard005.valid
  · exact Shard006.valid
  · exact Shard007.valid
  · exact Shard008.valid
  · exact Shard009.valid
  · exact Shard010.valid
  · exact Shard011.valid
  · exact Shard012.valid
  · exact Shard013.valid
  · exact Shard014.valid
  · exact Shard015.valid

theorem count (i : Fin 16) : (Finset.univ.filter fun j : Fin 4096 =>
    isPrimal (certificates i j) = true).card = counts i := by
  fin_cases i
  · exact Shard000.count
  · exact Shard001.count
  · exact Shard002.count
  · exact Shard003.count
  · exact Shard004.count
  · exact Shard005.count
  · exact Shard006.count
  · exact Shard007.count
  · exact Shard008.count
  · exact Shard009.count
  · exact Shard010.count
  · exact Shard011.count
  · exact Shard012.count
  · exact Shard013.count
  · exact Shard014.count
  · exact Shard015.count

theorem count_total : (∑ i, counts i) = 15603 := by decide +kernel

end MainTheory.Generated.Orbit31SupportCoverage.Aggregate
