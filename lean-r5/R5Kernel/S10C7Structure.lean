import R5Kernel.Probes.S11C7BetaData
import R5Kernel.SmallUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C7
open scoped BigOperators

def kernelC7Embedding : Fin 7 ↪ Fin 10 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 10 => z.val) h)

def kernelC7Slice (I : Finset (Fin 10)) : Finset (Fin 7) :=
  Finset.univ.filter (fun x => kernelC7Embedding x ∈ I)

theorem kernel_c7_slice_map (I : Finset (Fin 10)) :
    (kernelC7Slice I).map kernelC7Embedding = I.filter (fun x => x.val < 7) := by
  ext x
  simp only [Finset.mem_map, kernelC7Slice, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c7_slice_independent (I : Finset (Fin 10))
    (hI : (cycleGraph 10 7).IsIndepSet (I : Set (Fin 10))) :
    (cycleGraph 7 7).IsIndepSet (kernelC7Slice I : Set (Fin 7)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC7Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC7Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC7Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 10 7 _ _ ∨ cycleRel 10 7 _ _)
  change x ≠ y ∧ (cycleRel 7 7 x y ∨ cycleRel 7 7 y x) at hadj
  exact ⟨fun h => hxy (kernelC7Embedding.injective h), hadj.2⟩

def kernelIsoEmbedding : Fin 3 ↪ Fin 10 where
  toFun x := ⟨x.val + 7, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 10 => z.val) h
    apply Fin.ext
    change x.val + 7 = y.val + 7 at hv
    omega

def kernelIsoSlice (I : Finset (Fin 10)) : Finset (Fin 3) :=
  Finset.univ.filter (fun x => kernelIsoEmbedding x ∈ I)

def kernelJoinParts (p : Finset (Fin 7) × Finset (Fin 3)) : Finset (Fin 10) :=
  p.1.map kernelC7Embedding ∪ p.2.map kernelIsoEmbedding

def kernelC7Product : Finset (Finset (Fin 7) × Finset (Fin 3)) :=
  kernelC7Independents ×ˢ Finset.univ

theorem kernel_iso_slice_map (I : Finset (Fin 10)) :
    (kernelIsoSlice I).map kernelIsoEmbedding = I.filter (fun x => ¬ x.val < 7) := by
  ext x
  simp only [Finset.mem_map, kernelIsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 7 < 7; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 3 := ⟨x.val - 7, by omega⟩
    have hy : kernelIsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 7) + 7 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_join_slices (I : Finset (Fin 10)) :
    kernelJoinParts (kernelC7Slice I, kernelIsoSlice I) = I := by
  unfold kernelJoinParts
  rw [kernel_c7_slice_map, kernel_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

-- Only coverage is needed: every summand is a natural number, so even a
-- redundant cover would give a sound upper bound. No unproved enumeration
-- or external certificate enters this argument.
theorem kernel_s10_types_covered :
    cycleTypes 10 7 ⊆ kernelC7Product.image kernelJoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC7Slice I, kernelIsoSlice I), ?_, kernel_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c7_independents_complete _
    (kernel_c7_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s10_sum_le_cover (F : Finset (Fin 10) → ℕ) :
    (∑ I ∈ cycleTypes 10 7, F I) ≤ ∑ p ∈ kernelC7Product, F (kernelJoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s10_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))


theorem kernel_s10_beta_of_cycle_bound (R : Finset (Fin 10)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 7),
      (cycleGraph 7 7).IsIndepSet (J : Set (Fin 7)) →
      J ⊆ kernelC7Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 7)).card ≤ b)
    (I : Finset (Fin 10)) (hI : (cycleGraph 10 7).IsIndepSet (I : Set (Fin 10)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC7Slice I ⊆ kernelC7Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC7Slice I) (kernel_c7_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 7)).card ≤ a := by
    rw [← kernel_c7_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 7) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 7)
  omega


run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_sum_le_cover
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_beta_of_cycle_bound

end Erdos1011.S10C7
