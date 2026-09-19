import R5Kernel.Probes.S11C9Structural

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Erdos1011
open scoped BigOperators

def kernelC9Independents : Finset (Finset (Fin 9)) :=
  {∅, {0}, {1}, {2}, {0, 2}, {3},
   {0, 3}, {1, 3}, {4}, {0, 4}, {1, 4}, {2, 4},
   {0, 2, 4}, {5}, {0, 5}, {1, 5}, {2, 5}, {0, 2, 5},
   {3, 5}, {0, 3, 5}, {1, 3, 5}, {6}, {0, 6}, {1, 6},
   {2, 6}, {0, 2, 6}, {3, 6}, {0, 3, 6}, {1, 3, 6}, {4, 6},
   {0, 4, 6}, {1, 4, 6}, {2, 4, 6}, {0, 2, 4, 6}, {7}, {0, 7},
   {1, 7}, {2, 7}, {0, 2, 7}, {3, 7}, {0, 3, 7}, {1, 3, 7},
   {4, 7}, {0, 4, 7}, {1, 4, 7}, {2, 4, 7}, {0, 2, 4, 7}, {5, 7},
   {0, 5, 7}, {1, 5, 7}, {2, 5, 7}, {0, 2, 5, 7}, {3, 5, 7}, {0, 3, 5, 7},
   {1, 3, 5, 7}, {8}, {1, 8}, {2, 8}, {3, 8}, {1, 3, 8},
   {4, 8}, {1, 4, 8}, {2, 4, 8}, {5, 8}, {1, 5, 8}, {2, 5, 8},
   {3, 5, 8}, {1, 3, 5, 8}, {6, 8}, {1, 6, 8}, {2, 6, 8}, {3, 6, 8},
   {1, 3, 6, 8}, {4, 6, 8}, {1, 4, 6, 8}, {2, 4, 6, 8}}

theorem kernel_c9_independents_complete : ∀ J : Finset (Fin 9),
    (cycleGraph 9 9).IsIndepSet (J : Set (Fin 9)) → J ∈ kernelC9Independents := by
  decide +kernel

def kernelC9Product : Finset (Finset (Fin 9) × Finset (Fin 2)) :=
  kernelC9Independents ×ˢ Finset.univ

theorem kernel_c9_iso_slice_map (I : Finset (Fin 11)) :
    (kernelC9IsoSlice I).map kernelC9IsoEmbedding = I.filter (fun x => ¬ x.val < 9) := by
  ext x
  simp only [Finset.mem_map, kernelC9IsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 9 < 9; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 2 := ⟨x.val - 9, by omega⟩
    have hy : kernelC9IsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 9) + 9 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_c9_join_slices (I : Finset (Fin 11)) :
    kernelC9JoinParts (kernelC9Slice I, kernelC9IsoSlice I) = I := by
  unfold kernelC9JoinParts
  rw [kernel_c9_slice_map, kernel_c9_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

theorem kernel_s11c9_types_covered :
    cycleTypes 11 9 ⊆ kernelC9Product.image kernelC9JoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC9Slice I, kernelC9IsoSlice I), ?_, kernel_c9_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c9_independents_complete _
    (kernel_c9_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s11c9_sum_le_cover (F : Finset (Fin 11) → ℕ) :
    (∑ I ∈ cycleTypes 11 9, F I) ≤
      ∑ p ∈ kernelC9Product, F (kernelC9JoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s11c9_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

def kernelS11C9CoverValue (r : R5RepDualRecord11) : ℕ :=
  let R := r5RepMaskSet11C9 r.mask
  r.beta * (∑ e ∈ R, r5RepScaledNum11C9 r e) +
    ∑ p ∈ kernelC9Product, let I := kernelC9JoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - ∑ e ∈ I, if e ∈ R then r5RepScaledNum11C9 r e else 0
      else 0

theorem kernel_s11c9_value_le_cover (r : R5RepDualRecord11) :
    r5RepNatScaledValue11C9 r ≤ kernelS11C9CoverValue r := by
  unfold r5RepNatScaledValue11C9 kernelS11C9CoverValue
  exact Nat.add_le_add_left (kernel_s11c9_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_value_le_cover

end Erdos1011
