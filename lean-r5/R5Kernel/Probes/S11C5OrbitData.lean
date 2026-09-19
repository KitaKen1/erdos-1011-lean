import R5Kernel.Probes.S11C5BetaData
import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

-- Five rotations and five reflections, checked only on Fin 5.
def kernelC5Action (d : Fin 10) (x : Fin 5) : Fin 5 :=
  ⟨(if d.val < 5 then x.val + d.val else d.val - x.val) % 5,
    Nat.mod_lt _ (by decide)⟩

theorem kernel_c5_action_bijective : ∀ d : Fin 10,
    Function.Bijective (kernelC5Action d) := by decide +kernel

noncomputable def kernelC5ActionEquiv (d : Fin 10) : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective (kernelC5Action d) (kernel_c5_action_bijective d)

theorem kernel_c5_action_adj : ∀ (d : Fin 10) (x y : Fin 5),
    (cycleGraph 5 5).Adj (kernelC5Action d x) (kernelC5Action d y) ↔
      (cycleGraph 5 5).Adj x y := by decide +kernel

theorem kernel_c5_all_subsets_covered : ∀ J : Finset (Fin 5),
    ∃ c : Fin 32, ∃ d : Fin 10, c.val ∈ kernelC5CanonicalMasks ∧
      (kernelC5SmallMask c.val).map (kernelC5ActionEquiv d).toEmbedding = J := by
  decide +kernel

def kernelIsoPrefix (k : Fin 7) : Finset (Fin 6) :=
  Finset.univ.filter (fun x => x.val < k.val)

theorem kernel_iso_prefix_card : ∀ k : Fin 7, (kernelIsoPrefix k).card = k.val := by
  decide +kernel

def kernelS11Pack (c : Fin 32) (k : Fin 7) : Fin 2048 :=
  ⟨(c.val + 32 * (2 ^ k.val - 1)) % 2048, Nat.mod_lt _ (by decide)⟩

-- Eight cycle shapes × seven isolated-vertex counts; the zero case is
-- retained explicitly, then excluded by nonemptiness in the general proof.
theorem kernel_s11_packed_shapes : ∀ c : Fin 32,
    c.val ∈ kernelC5CanonicalMasks → ∀ k : Fin 7,
      r5RepMaskSet11 (kernelS11Pack c k) =
        kernelJoinParts (kernelC5SmallMask c.val, kernelIsoPrefix k) ∧
      ((kernelS11Pack c k).val ∈ kernelS11RepresentativeMasks ∨ kernelS11Pack c k = 0) := by
  decide +kernel

theorem kernel_s11_zero_mask : r5RepMaskSet11 0 = ∅ := by decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c5_all_subsets_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_c5_action_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_iso_prefix_card
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_packed_shapes

end Erdos1011
