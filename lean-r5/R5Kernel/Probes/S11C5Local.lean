import R5Kernel.Probes.S11C5CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

-- Only 32 subsets of the five-cycle, independent of its six isolated vertices.
theorem kernel_c5_local_alpha : ∀ J : Finset (Fin 5),
    (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) → J.card ≤ 2 := by
  decide +kernel

def kernelC5Embedding : Fin 5 ↪ Fin 11 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 11 => z.val) h)

def kernelC5Slice (I : Finset (Fin 11)) : Finset (Fin 5) :=
  Finset.univ.filter (fun x => kernelC5Embedding x ∈ I)

theorem kernel_c5_slice_map (I : Finset (Fin 11)) :
    (kernelC5Slice I).map kernelC5Embedding = I.filter (fun x => x.val < 5) := by
  ext x
  simp only [Finset.mem_map, kernelC5Slice, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c5_slice_independent (I : Finset (Fin 11))
    (hI : (cycleGraph 11 5).IsIndepSet (I : Set (Fin 11))) :
    (cycleGraph 5 5).IsIndepSet (kernelC5Slice I : Set (Fin 5)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC5Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC5Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC5Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 11 5 _ _ ∨ cycleRel 11 5 _ _)
  change x ≠ y ∧ (cycleRel 5 5 x y ∨ cycleRel 5 5 y x) at hadj
  exact ⟨fun h => hxy (kernelC5Embedding.injective h), hadj.2⟩

theorem kernel_c5_isolates_card :
    ((Finset.univ : Finset (Fin 11)).filter (fun x => ¬ x.val < 5)).card = 6 := by
  decide +kernel

theorem kernel_s11_independent_card (I : Finset (Fin 11))
    (hI : (cycleGraph 11 5).IsIndepSet (I : Set (Fin 11))) : I.card ≤ 8 := by
  have hcycle := kernel_c5_local_alpha (kernelC5Slice I) (kernel_c5_slice_independent I hI)
  have hcyclecard : (I.filter (fun x => x.val < 5)).card ≤ 2 := by
    rw [← kernel_c5_slice_map, Finset.card_map]
    exact hcycle
  have hiso : (I.filter (fun x => ¬ x.val < 5)).card ≤ 6 := by
    rw [← kernel_c5_isolates_card]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I))
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 5)
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_c5_local_alpha
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_independent_card

end Erdos1011
