import R5Kernel.Probes.S11C9CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c9_local_alpha : ∀ J : Finset (Fin 9),
    (cycleGraph 9 9).IsIndepSet (J : Set (Fin 9)) → J.card ≤ 4 := by
  decide +kernel

def kernelC9Embedding : Fin 9 ↪ Fin 11 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 11 => z.val) h)

def kernelC9Slice (I : Finset (Fin 11)) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => kernelC9Embedding x ∈ I)

theorem kernel_c9_slice_map (I : Finset (Fin 11)) :
    (kernelC9Slice I).map kernelC9Embedding = I.filter (fun x => x.val < 9) := by
  ext x
  simp only [Finset.mem_map, kernelC9Slice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c9_slice_independent (I : Finset (Fin 11))
    (hI : (cycleGraph 11 9).IsIndepSet (I : Set (Fin 11))) :
    (cycleGraph 9 9).IsIndepSet (kernelC9Slice I : Set (Fin 9)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC9Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC9Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC9Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 11 9 _ _ ∨ cycleRel 11 9 _ _)
  change x ≠ y ∧ (cycleRel 9 9 x y ∨ cycleRel 9 9 y x) at hadj
  exact ⟨fun h => hxy (kernelC9Embedding.injective h), hadj.2⟩

theorem kernel_c9_isolates_card :
    ((Finset.univ : Finset (Fin 11)).filter (fun x => ¬ x.val < 9)).card = 2 := by
  decide +kernel

theorem kernel_s11c9_independent_card (I : Finset (Fin 11))
    (hI : (cycleGraph 11 9).IsIndepSet (I : Set (Fin 11))) : I.card ≤ 6 := by
  have hcycle := kernel_c9_local_alpha (kernelC9Slice I) (kernel_c9_slice_independent I hI)
  have hcyclecard : (I.filter (fun x => x.val < 9)).card ≤ 4 := by
    rw [← kernel_c9_slice_map, Finset.card_map]
    exact hcycle
  have hiso : (I.filter (fun x => ¬ x.val < 9)).card ≤ 2 := by
    rw [← kernel_c9_isolates_card]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I))
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 9)
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_local_alpha
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_independent_card

end Erdos1011
