import R5Kernel.Probes.S11C9OrbitDefinitions

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c9_action_bijective : ∀ d : Fin 18,
    Function.Bijective (kernelC9Action d) := by decide +kernel

noncomputable def kernelC9ActionEquiv (d : Fin 18) : Fin 9 ≃ Fin 9 :=
  Equiv.ofBijective (kernelC9Action d) (kernel_c9_action_bijective d)

theorem kernel_c9_action_adj : ∀ (d : Fin 18) (x y : Fin 9),
    (cycleGraph 9 9).Adj (kernelC9Action d x) (kernelC9Action d y) ↔
      (cycleGraph 9 9).Adj x y := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_action_adj

end Erdos1011
