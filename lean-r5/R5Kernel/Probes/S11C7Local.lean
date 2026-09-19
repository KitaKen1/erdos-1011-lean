import R5Kernel.Probes.S11C7CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

theorem kernel_c7_local_alpha : ∀ J : Finset (Fin 7),
    (cycleGraph 7 7).IsIndepSet (J : Set (Fin 7)) → J.card ≤ 3 := by
  decide +kernel

def kernelC7Embedding : Fin 7 ↪ Fin 11 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 11 => z.val) h)

def kernelC7Slice (I : Finset (Fin 11)) : Finset (Fin 7) :=
  Finset.univ.filter (fun x => kernelC7Embedding x ∈ I)

theorem kernel_c7_slice_map (I : Finset (Fin 11)) :
    (kernelC7Slice I).map kernelC7Embedding = I.filter (fun x => x.val < 7) := by
  ext x
  simp only [Finset.mem_map, kernelC7Slice, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c7_slice_independent (I : Finset (Fin 11))
    (hI : (cycleGraph 11 7).IsIndepSet (I : Set (Fin 11))) :
    (cycleGraph 7 7).IsIndepSet (kernelC7Slice I : Set (Fin 7)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC7Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC7Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC7Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 11 7 _ _ ∨ cycleRel 11 7 _ _)
  change x ≠ y ∧ (cycleRel 7 7 x y ∨ cycleRel 7 7 y x) at hadj
  exact ⟨fun h => hxy (kernelC7Embedding.injective h), hadj.2⟩

theorem kernel_c7_isolates_card :
    ((Finset.univ : Finset (Fin 11)).filter (fun x => ¬ x.val < 7)).card = 4 := by
  decide +kernel

theorem kernel_s11c7_independent_card (I : Finset (Fin 11))
    (hI : (cycleGraph 11 7).IsIndepSet (I : Set (Fin 11))) : I.card ≤ 7 := by
  have hcycle := kernel_c7_local_alpha (kernelC7Slice I) (kernel_c7_slice_independent I hI)
  have hcyclecard : (I.filter (fun x => x.val < 7)).card ≤ 3 := by
    rw [← kernel_c7_slice_map, Finset.card_map]
    exact hcycle
  have hiso : (I.filter (fun x => ¬ x.val < 7)).card ≤ 4 := by
    rw [← kernel_c7_isolates_card]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I))
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 7)
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_local_alpha
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_independent_card

end Erdos1011
