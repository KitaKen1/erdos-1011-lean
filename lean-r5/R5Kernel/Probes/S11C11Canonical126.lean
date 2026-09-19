import R5Kernel.Probes.S11C11CanonicalDefinitions

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC11CanonicalRep126 (i : Fin 126) : Fin 2048 :=
  ⟨kernelC11CanonicalMasks.getD i.val 0, by
    fin_cases i <;> decide⟩

theorem kernel_c11_canonical_rep126_mem (i : Fin 126) :
    (kernelC11CanonicalRep126 i).val ∈ kernelC11CanonicalMasks := by
  fin_cases i <;> decide

theorem kernel_c11_canonical_rep126_prefix (i : Fin 125) :
    kernelC11CanonicalRep126 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
      kernelC11CanonicalRep i := by
  rfl

end Erdos1011
