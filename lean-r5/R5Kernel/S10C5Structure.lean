import R5Kernel.Probes.S11C5OrbitData
import R5Kernel.SmallUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def kernelC5Embedding : Fin 5 ↪ Fin 10 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 10 => z.val) h)

def kernelC5Slice (I : Finset (Fin 10)) : Finset (Fin 5) :=
  Finset.univ.filter (fun x => kernelC5Embedding x ∈ I)

theorem kernel_c5_slice_map (I : Finset (Fin 10)) :
    (kernelC5Slice I).map kernelC5Embedding = I.filter (fun x => x.val < 5) := by
  ext x
  simp only [Finset.mem_map, kernelC5Slice, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c5_slice_independent (I : Finset (Fin 10))
    (hI : (cycleGraph 10 5).IsIndepSet (I : Set (Fin 10))) :
    (cycleGraph 5 5).IsIndepSet (kernelC5Slice I : Set (Fin 5)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC5Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC5Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC5Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 10 5 _ _ ∨ cycleRel 10 5 _ _)
  change x ≠ y ∧ (cycleRel 5 5 x y ∨ cycleRel 5 5 y x) at hadj
  exact ⟨fun h => hxy (kernelC5Embedding.injective h), hadj.2⟩

def kernelIsoEmbedding : Fin 5 ↪ Fin 10 where
  toFun x := ⟨x.val + 5, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 10 => z.val) h
    apply Fin.ext
    change x.val + 5 = y.val + 5 at hv
    omega

def kernelIsoSlice (I : Finset (Fin 10)) : Finset (Fin 5) :=
  Finset.univ.filter (fun x => kernelIsoEmbedding x ∈ I)

def kernelJoinParts (p : Finset (Fin 5) × Finset (Fin 5)) : Finset (Fin 10) :=
  p.1.map kernelC5Embedding ∪ p.2.map kernelIsoEmbedding

def kernelC5Product : Finset (Finset (Fin 5) × Finset (Fin 5)) :=
  kernelC5Independents ×ˢ Finset.univ

theorem kernel_iso_slice_map (I : Finset (Fin 10)) :
    (kernelIsoSlice I).map kernelIsoEmbedding = I.filter (fun x => ¬ x.val < 5) := by
  ext x
  simp only [Finset.mem_map, kernelIsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 5 < 5; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 5 := ⟨x.val - 5, by omega⟩
    have hy : kernelIsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 5) + 5 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_join_slices (I : Finset (Fin 10)) :
    kernelJoinParts (kernelC5Slice I, kernelIsoSlice I) = I := by
  unfold kernelJoinParts
  rw [kernel_c5_slice_map, kernel_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

-- Only coverage is needed: every summand is a natural number, so even a
-- redundant cover would give a sound upper bound. No unproved enumeration
-- or external certificate enters this argument.
theorem kernel_s10_types_covered :
    cycleTypes 10 5 ⊆ kernelC5Product.image kernelJoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC5Slice I, kernelIsoSlice I), ?_, kernel_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c5_independents_complete _
    (kernel_c5_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s10_sum_le_cover (F : Finset (Fin 10) → ℕ) :
    (∑ I ∈ cycleTypes 10 5, F I) ≤ ∑ p ∈ kernelC5Product, F (kernelJoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s10_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))


theorem kernel_s10_beta_of_cycle_bound (R : Finset (Fin 10)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 5),
      (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) →
      J ⊆ kernelC5Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 5)).card ≤ b)
    (I : Finset (Fin 10)) (hI : (cycleGraph 10 5).IsIndepSet (I : Set (Fin 10)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC5Slice I ⊆ kernelC5Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC5Slice I) (kernel_c5_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 5)).card ≤ a := by
    rw [← kernel_c5_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 5) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 5)
  omega


run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_sum_le_cover
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_beta_of_cycle_bound

end Erdos1011.S10C5
