import R5Kernel.S8UniformData

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_s8c7_uniform_chunk11 : ∀ i : Fin 16,
    KernelS8C7UniformCertificate (i.val + 176) := by
  unfold KernelS8C7UniformCertificate
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c7_uniform_chunk11

end Erdos1011

