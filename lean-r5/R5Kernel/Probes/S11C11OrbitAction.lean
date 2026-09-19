import R5Kernel.Probes.S11C11Local

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC11Action (d : Fin 22) (x : Fin 11) : Fin 11 :=
  ⟨(if d.val < 11 then x.val + d.val else d.val - x.val) % 11,
    Nat.mod_lt _ (by decide)⟩

theorem kernel_c11_action_bijective : ∀ d : Fin 22,
    Function.Bijective (kernelC11Action d) := by decide +kernel

noncomputable def kernelC11ActionEquiv (d : Fin 22) : Fin 11 ≃ Fin 11 :=
  Equiv.ofBijective (kernelC11Action d) (kernel_c11_action_bijective d)

theorem kernel_c11_action_adj : ∀ (d : Fin 22) (x y : Fin 11),
    (cycleGraph 11 11).Adj (kernelC11Action d x) (kernelC11Action d y) ↔
      (cycleGraph 11 11).Adj x y := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_action_adj

end Erdos1011
