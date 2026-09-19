import R5Kernel.Probes.S11C11NumericMask
import R5Kernel.Probes.S11C11NumericBetaChunks
import R5Kernel.Probes.S11C11NumericBoundChunks
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def KernelC11Certificate (i : Fin 126) : Prop :=
  (kernelC11Row (kernelC11CanonicalRep126 i).val).mask =
      kernelC11CanonicalRep126 i ∧
  (∀ I ∈ cycleTypes 11 11,
    I ⊆ r5RepMaskSet11C11
      (kernelC11Row (kernelC11CanonicalRep126 i).val).mask →
      I.card ≤ (kernelC11Row (kernelC11CanonicalRep126 i).val).beta) ∧
  r5RepNatScaledValue11C11
      (kernelC11Row (kernelC11CanonicalRep126 i).val) ≤ 206

theorem kernel_c11_all_canonical_certificates (i : Fin 126) :
    KernelC11Certificate i := by
  exact ⟨kernel_c11_canonical_row_mask i,
    kernel_c11_canonical_beta i,
    kernel_c11_canonical_scaled_bound i⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_all_canonical_certificates

end Erdos1011
