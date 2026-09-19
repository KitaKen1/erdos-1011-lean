import R5Kernel.Probes.S11C11LowCardWitness

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_low_witness_block11 : ∀ i : Fin 128,
    KernelC11LowCardWitnessValid (i.val + 1408) := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_witness_block11

end Erdos1011
