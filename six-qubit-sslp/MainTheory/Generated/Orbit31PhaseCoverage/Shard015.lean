import MainTheory.Orbit31PhaseCoverageBase

/-! Every listed support has a checked primal witness and phase certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PhaseCoverage.Shard015
open MainTheory.Orbit31PhaseCoverageBase
open MainTheory.Orbit31SignedSupport (isColoring)

def records : List Entry := [
  {mask:=⟨65500,by decide⟩,vertices:=[38,41,46,60,65,122],phase:=.coloring ![false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false]},
  {mask:=⟨65501,by decide⟩,vertices:=[1,4,5,7,10,36,60,122],phase:=.coloring ![false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false]},
  {mask:=⟨65502,by decide⟩,vertices:=[19,20,21,26,37,59,121],phase:=.coloring ![false,false,true,true,true,false,true,true,false,false,true,true,false,false,true,true]},
  {mask:=⟨65503,by decide⟩,vertices:=[0,1,4,5,7,10,18,59,121],phase:=.coloring ![false,true,false,false,false,false,false,false,false,true,false,false,false,true,false,false]},
  {mask:=⟨65510,by decide⟩,vertices:=[19,23,24,27,37,62,139],phase:=.coloring ![false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false]},
  {mask:=⟨65511,by decide⟩,vertices:=[0,1,2,9,18,58,138],phase:=.coloring ![false,true,true,false,false,true,true,true,false,true,true,false,false,true,true,false]},
  {mask:=⟨65514,by decide⟩,vertices:=[19,21,23,29,37,77,124],phase:=.coloring ![false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false]},
  {mask:=⟨65515,by decide⟩,vertices:=[0,1,3,4,8,18,76,120],phase:=.coloring ![false,true,false,true,false,true,true,true,false,true,false,true,false,true,false,true]},
  {mask:=⟨65516,by decide⟩,vertices:=[38,41,46,60,64,122],phase:=.coloring ![false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false]},
  {mask:=⟨65517,by decide⟩,vertices:=[1,2,4,8,36,58,120],phase:=.coloring ![false,false,true,true,false,true,true,true,false,false,true,true,false,false,true,true]},
  {mask:=⟨65518,by decide⟩,vertices:=[19,21,23,24,27,37,60,122],phase:=.coloring ![false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false]},
  {mask:=⟨65519,by decide⟩,vertices:=[0,1,2,4,8,18,58,120],phase:=.coloring ![false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true]},
  {mask:=⟨65523,by decide⟩,vertices:=[0,1,3,5,9,18,76,138],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65525,by decide⟩,vertices:=[1,2,5,9,36,58,138],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65526,by decide⟩,vertices:=[19,20,23,27,37,59,139],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65527,by decide⟩,vertices:=[0,1,2,5,9,18,58,138],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65529,by decide⟩,vertices:=[1,3,4,5,8,36,76,120],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65530,by decide⟩,vertices:=[19,21,23,25,26,37,77,121],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65531,by decide⟩,vertices:=[0,1,3,4,5,8,18,76,120],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65532,by decide⟩,vertices:=[38,41,46,60,64,65,122],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65533,by decide⟩,vertices:=[1,2,4,5,8,36,58,120],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65534,by decide⟩,vertices:=[19,20,21,23,26,37,59,121],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]},
  {mask:=⟨65535,by decide⟩,vertices:=[0,1,2,4,5,8,18,58,120],phase:=.coloring ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]}]

theorem checked : records.all (fun entry => decide (Valid entry)) = true := by decide +kernel
theorem valid : ∀ entry ∈ records, Valid entry := by
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked
theorem length : records.length = 23 := by decide +kernel
theorem color_count : (records.filter (fun entry => isColoring entry.phase)).length = 23 := by decide +kernel

end MainTheory.Generated.Orbit31PhaseCoverage.Shard015
