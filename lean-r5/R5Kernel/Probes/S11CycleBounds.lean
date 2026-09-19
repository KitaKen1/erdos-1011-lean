import R5Kernel.Probes.CycleSurplusBridge
import R5Kernel.Probes.S11C5AllMasks
import R5Kernel.Probes.S11C7AllMasks
import R5Kernel.Probes.S11C9AllMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011

theorem kernel_s11c5_supportSurplus_le_142
    {A B : Finset (Finset (Fin 11))}
    (hAU : A ⊆ cycleTypes 11 5) (hBU : B ⊆ cycleTypes 11 5)
    (hcompat : DegreeCompatible A B) :
    supportSurplus A B ≤ 142 := by
  have h : 2 * supportSurplus A B ≤ 284 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s11_all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c5_supportSurplus_le_142

theorem kernel_s11c7_supportSurplus_le_129
    {A B : Finset (Finset (Fin 11))}
    (hAU : A ⊆ cycleTypes 11 7) (hBU : B ⊆ cycleTypes 11 7)
    (hcompat : DegreeCompatible A B) :
    supportSurplus A B ≤ 129 := by
  have h : 4 * supportSurplus A B ≤ 516 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s11c7_all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_supportSurplus_le_129

theorem kernel_s11c9_supportSurplus_le_116
    {A B : Finset (Finset (Fin 11))}
    (hAU : A ⊆ cycleTypes 11 9) (hBU : B ⊆ cycleTypes 11 9)
    (hcompat : DegreeCompatible A B) :
    supportSurplus A B ≤ 116 := by
  have h : 2 * supportSurplus A B ≤ 232 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s11c9_all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_supportSurplus_le_116

end Erdos1011

