import R5Kernel.Probes.S11C5Local

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011
open scoped BigOperators

def kernelC5Independents : Finset (Finset (Fin 5)) :=
  {∅, {0}, {1}, {2}, {3}, {4}, {0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}}

theorem kernel_c5_independents_complete : ∀ J : Finset (Fin 5),
    (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) → J ∈ kernelC5Independents := by
  decide +kernel

def kernelIsoEmbedding : Fin 6 ↪ Fin 11 where
  toFun x := ⟨x.val + 5, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 11 => z.val) h
    apply Fin.ext
    change x.val + 5 = y.val + 5 at hv
    omega

def kernelIsoSlice (I : Finset (Fin 11)) : Finset (Fin 6) :=
  Finset.univ.filter (fun x => kernelIsoEmbedding x ∈ I)

def kernelJoinParts (p : Finset (Fin 5) × Finset (Fin 6)) : Finset (Fin 11) :=
  p.1.map kernelC5Embedding ∪ p.2.map kernelIsoEmbedding

def kernelC5Product : Finset (Finset (Fin 5) × Finset (Fin 6)) :=
  kernelC5Independents ×ˢ Finset.univ

theorem kernel_iso_slice_map (I : Finset (Fin 11)) :
    (kernelIsoSlice I).map kernelIsoEmbedding = I.filter (fun x => ¬ x.val < 5) := by
  ext x
  simp only [Finset.mem_map, kernelIsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 5 < 5; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 6 := ⟨x.val - 5, by omega⟩
    have hy : kernelIsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 5) + 5 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_join_slices (I : Finset (Fin 11)) :
    kernelJoinParts (kernelC5Slice I, kernelIsoSlice I) = I := by
  unfold kernelJoinParts
  rw [kernel_c5_slice_map, kernel_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

-- Only coverage is needed: every summand is a natural number, so even a
-- redundant cover would give a sound upper bound. No unproved enumeration
-- or external certificate enters this argument.
theorem kernel_s11_types_covered :
    cycleTypes 11 5 ⊆ kernelC5Product.image kernelJoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC5Slice I, kernelIsoSlice I), ?_, kernel_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c5_independents_complete _
    (kernel_c5_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s11_sum_le_cover (F : Finset (Fin 11) → ℕ) :
    (∑ I ∈ cycleTypes 11 5, F I) ≤ ∑ p ∈ kernelC5Product, F (kernelJoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s11_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

def kernelS11CoverValue (r : R5RepDualRecord11) : ℕ :=
  let R := r5RepMaskSet11 r.mask
  r.beta * (∑ e ∈ R, r5RepScaledNum11 r e) +
    ∑ p ∈ kernelC5Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - ∑ e ∈ I, if e ∈ R then r5RepScaledNum11 r e else 0
      else 0

theorem kernel_s11_value_le_cover (r : R5RepDualRecord11) :
    r5RepNatScaledValue11 r ≤ kernelS11CoverValue r := by
  unfold r5RepNatScaledValue11 kernelS11CoverValue
  exact Nat.add_le_add_left (kernel_s11_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_value_le_cover

end Erdos1011
