import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC7Action (d : Fin 14) (x : Fin 7) : Fin 7 :=
  ⟨(if d.val < 7 then x.val + d.val else d.val - x.val) % 7,
    Nat.mod_lt _ (by decide)⟩

theorem kernel_c7_action_bijective : ∀ d : Fin 14,
    Function.Bijective (kernelC7Action d) := by decide +kernel

noncomputable def kernelC7ActionEquiv (d : Fin 14) : Fin 7 ≃ Fin 7 :=
  Equiv.ofBijective (kernelC7Action d) (kernel_c7_action_bijective d)

theorem kernel_c7_action_adj : ∀ (d : Fin 14) (x y : Fin 7),
    (cycleGraph 7 7).Adj (kernelC7Action d x) (kernelC7Action d y) ↔
      (cycleGraph 7 7).Adj x y := by
  decide +kernel

def kernelC7CanonicalMasks : List ℕ :=
  [0, 1, 3, 5, 7, 9, 11, 15, 19, 21, 23, 27, 31, 43, 47, 55, 63, 127]

def kernelC7SmallMask (m : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter (fun x => (m / 2 ^ x.val) % 2 = 1)

theorem kernel_c7_all_subsets_covered : ∀ J : Finset (Fin 7),
    ∃ c : Fin 128, ∃ d : Fin 14, c.val ∈ kernelC7CanonicalMasks ∧
      (kernelC7SmallMask c.val).map (kernelC7ActionEquiv d).toEmbedding = J := by
  decide +kernel

def kernelC7IsoPrefix (k : Fin 5) : Finset (Fin 4) :=
  Finset.univ.filter (fun x => x.val < k.val)

theorem kernel_c7_iso_prefix_card : ∀ k : Fin 5, (kernelC7IsoPrefix k).card = k.val := by
  decide +kernel

def kernelS11C7Pack (c : Fin 128) (k : Fin 5) : Fin 2048 :=
  ⟨(c.val + 128 * (2 ^ k.val - 1)) % 2048, Nat.mod_lt _ (by decide)⟩

theorem kernel_s11c7_packed_shapes : ∀ c : Fin 128,
    c.val ∈ kernelC7CanonicalMasks → ∀ k : Fin 5,
      r5RepMaskSet11C7 (kernelS11C7Pack c k) =
        kernelC7JoinParts (kernelC7SmallMask c.val, kernelC7IsoPrefix k) ∧
      ((kernelS11C7Pack c k).val ∈ kernelS11C7RepresentativeMasks ∨
        kernelS11C7Pack c k = 0) := by
  decide +kernel

theorem kernel_s11c7_zero_mask : r5RepMaskSet11C7 0 = ∅ := by decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_all_subsets_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_action_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_iso_prefix_card
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_packed_shapes

end Erdos1011
