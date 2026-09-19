import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk6 : List ℕ :=
  [2017, 2019, 2021, 2023, 2027, 2031, 2047]

theorem kernel_s11_cover_bound_block6 :
    ∀ m ∈ kernelS11CoverMasksChunk6,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block6

end Erdos1011
