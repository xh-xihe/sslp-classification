import MainTheory.Generated.Orbit31PhaseCoverage.Shard000
import MainTheory.Generated.Orbit31PhaseCoverage.Shard001
import MainTheory.Generated.Orbit31PhaseCoverage.Shard002
import MainTheory.Generated.Orbit31PhaseCoverage.Shard003
import MainTheory.Generated.Orbit31PhaseCoverage.Shard004
import MainTheory.Generated.Orbit31PhaseCoverage.Shard005
import MainTheory.Generated.Orbit31PhaseCoverage.Shard006
import MainTheory.Generated.Orbit31PhaseCoverage.Shard007
import MainTheory.Generated.Orbit31PhaseCoverage.Shard008
import MainTheory.Generated.Orbit31PhaseCoverage.Shard009
import MainTheory.Generated.Orbit31PhaseCoverage.Shard010
import MainTheory.Generated.Orbit31PhaseCoverage.Shard011
import MainTheory.Generated.Orbit31PhaseCoverage.Shard012
import MainTheory.Generated.Orbit31PhaseCoverage.Shard013
import MainTheory.Generated.Orbit31PhaseCoverage.Shard014
import MainTheory.Generated.Orbit31PhaseCoverage.Shard015

/-! Complete record set for the no-singleton supports, with exact graph checks. -/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PhaseCoverage.Aggregate
open MainTheory.Orbit31PhaseCoverageBase
open MainTheory.Orbit31SignedSupport (isColoring)

def records : List Entry := Shard000.records ++ Shard001.records ++ Shard002.records ++ Shard003.records ++ Shard004.records ++ Shard005.records ++ Shard006.records ++ Shard007.records ++ Shard008.records ++ Shard009.records ++ Shard010.records ++ Shard011.records ++ Shard012.records ++ Shard013.records ++ Shard014.records ++ Shard015.records

theorem checked : records.all (fun entry => decide (Valid entry)) = true := by
  simp only [records,List.all_append,Shard000.checked,Shard001.checked,Shard002.checked,Shard003.checked,Shard004.checked,Shard005.checked,Shard006.checked,Shard007.checked,Shard008.checked,Shard009.checked,Shard010.checked,Shard011.checked,Shard012.checked,Shard013.checked,Shard014.checked,Shard015.checked,Bool.true_and]
theorem valid : ∀ entry ∈ records, Valid entry := by
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked
theorem length : records.length = 2903 := by
  norm_num [records,List.length_append,Shard000.length,Shard001.length,Shard002.length,Shard003.length,Shard004.length,Shard005.length,Shard006.length,Shard007.length,Shard008.length,Shard009.length,Shard010.length,Shard011.length,Shard012.length,Shard013.length,Shard014.length,Shard015.length]
theorem color_count : (records.filter (fun entry => isColoring entry.phase)).length = 311 := by
  norm_num [records,List.filter_append,List.length_append,Shard000.color_count,Shard001.color_count,Shard002.color_count,Shard003.color_count,Shard004.color_count,Shard005.color_count,Shard006.color_count,Shard007.color_count,Shard008.color_count,Shard009.color_count,Shard010.color_count,Shard011.color_count,Shard012.color_count,Shard013.color_count,Shard014.color_count,Shard015.color_count]
theorem masks_increasing : (records.map Entry.mask).IsChain (· < ·) := by decide +kernel
theorem masks_nodup : (records.map Entry.mask).Nodup :=
  masks_increasing.pairwise.imp (fun h => ne_of_lt h)

end MainTheory.Generated.Orbit31PhaseCoverage.Aggregate
