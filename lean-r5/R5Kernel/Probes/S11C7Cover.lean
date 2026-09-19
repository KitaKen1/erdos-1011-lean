import R5Kernel.Probes.S11C7Local

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011
open scoped BigOperators

def kernelC7Independents : Finset (Finset (Fin 7)) :=
  {∅, {0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {0, 4},
   {1, 4}, {2, 4}, {0, 2, 4}, {5}, {0, 5}, {1, 5}, {2, 5},
   {0, 2, 5}, {3, 5}, {0, 3, 5}, {1, 3, 5}, {6}, {1, 6}, {2, 6},
   {3, 6}, {1, 3, 6}, {4, 6}, {1, 4, 6}, {2, 4, 6}}

theorem kernel_c7_independents_complete : ∀ J : Finset (Fin 7),
    (cycleGraph 7 7).IsIndepSet (J : Set (Fin 7)) → J ∈ kernelC7Independents := by
  decide +kernel

def kernelC7IsoEmbedding : Fin 4 ↪ Fin 11 where
  toFun x := ⟨x.val + 7, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 11 => z.val) h
    apply Fin.ext
    change x.val + 7 = y.val + 7 at hv
    omega

def kernelC7IsoSlice (I : Finset (Fin 11)) : Finset (Fin 4) :=
  Finset.univ.filter (fun x => kernelC7IsoEmbedding x ∈ I)

def kernelC7JoinParts (p : Finset (Fin 7) × Finset (Fin 4)) : Finset (Fin 11) :=
  p.1.map kernelC7Embedding ∪ p.2.map kernelC7IsoEmbedding

def kernelC7Product : Finset (Finset (Fin 7) × Finset (Fin 4)) :=
  kernelC7Independents ×ˢ Finset.univ

theorem kernel_c7_iso_slice_map (I : Finset (Fin 11)) :
    (kernelC7IsoSlice I).map kernelC7IsoEmbedding = I.filter (fun x => ¬ x.val < 7) := by
  ext x
  simp only [Finset.mem_map, kernelC7IsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 7 < 7; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 4 := ⟨x.val - 7, by omega⟩
    have hy : kernelC7IsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 7) + 7 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_c7_join_slices (I : Finset (Fin 11)) :
    kernelC7JoinParts (kernelC7Slice I, kernelC7IsoSlice I) = I := by
  unfold kernelC7JoinParts
  rw [kernel_c7_slice_map, kernel_c7_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

theorem kernel_s11c7_types_covered :
    cycleTypes 11 7 ⊆ kernelC7Product.image kernelC7JoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC7Slice I, kernelC7IsoSlice I), ?_, kernel_c7_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c7_independents_complete _
    (kernel_c7_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s11c7_sum_le_cover (F : Finset (Fin 11) → ℕ) :
    (∑ I ∈ cycleTypes 11 7, F I) ≤
      ∑ p ∈ kernelC7Product, F (kernelC7JoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s11c7_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

def kernelS11C7CoverValue (r : R5RepDualRecord11) : ℕ :=
  let R := r5RepMaskSet11C7 r.mask
  r.beta * (∑ e ∈ R, r5RepScaledNum11C7 r e) +
    ∑ p ∈ kernelC7Product, let I := kernelC7JoinParts p
      if (I ∩ R).Nonempty then
        4 * I.card - ∑ e ∈ I, if e ∈ R then r5RepScaledNum11C7 r e else 0
      else 0

theorem kernel_s11c7_value_le_cover (r : R5RepDualRecord11) :
    r5RepNatScaledValue11C7 r ≤ kernelS11C7CoverValue r := by
  unfold r5RepNatScaledValue11C7 kernelS11C7CoverValue
  exact Nat.add_le_add_left (kernel_s11c7_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_value_le_cover

end Erdos1011
