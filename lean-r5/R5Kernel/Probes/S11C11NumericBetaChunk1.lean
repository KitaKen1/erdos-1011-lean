import R5Kernel.Probes.S11C11NumericDefinitions
import R5Kernel.Probes.S11C11Canonical126
import R5Kernel.Probes.S11C11CycleTypesExplicit
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

namespace Erdos1011

theorem kernel_c11_canonical_beta_chunk1 : ∀ i : Fin 32, ∀ j : Fin 198,
    kernelC11CycleTypeAt j ⊆ r5RepMaskSet11C11
        (kernelC11Row (kernelC11CanonicalRep126
          ⟨i.val + 32, by omega⟩).val).mask →
      (kernelC11CycleTypeAt j).card ≤ (kernelC11Row
        (kernelC11CanonicalRep126
          ⟨i.val + 32, by omega⟩).val).beta := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_beta_chunk1

end Erdos1011
