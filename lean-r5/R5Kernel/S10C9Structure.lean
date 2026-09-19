import R5Kernel.Probes.S11C9BetaData
import R5Kernel.Probes.S11C9Cover
import R5Kernel.SmallUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def kernelC9Embedding : Fin 9 ↪ Fin 10 where
  toFun x := ⟨x.val, by omega⟩
  inj' := by intro x y h; exact Fin.ext (congrArg (fun z : Fin 10 => z.val) h)

def kernelC9Slice (I : Finset (Fin 10)) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => kernelC9Embedding x ∈ I)

theorem kernel_c9_slice_map (I : Finset (Fin 10)) :
    (kernelC9Slice I).map kernelC9Embedding = I.filter (fun x => x.val < 9) := by
  ext x
  simp only [Finset.mem_map, kernelC9Slice, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.isLt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨⟨x.val, hlt⟩, hx, rfl⟩

theorem kernel_c9_slice_independent (I : Finset (Fin 10))
    (hI : (cycleGraph 10 9).IsIndepSet (I : Set (Fin 10))) :
    (cycleGraph 9 9).IsIndepSet (kernelC9Slice I : Set (Fin 9)) := by
  rw [SimpleGraph.isIndepSet_iff] at hI ⊢
  intro x hx y hy hxy hadj
  have hxI : kernelC9Embedding x ∈ I := (Finset.mem_filter.mp hx).2
  have hyI : kernelC9Embedding y ∈ I := (Finset.mem_filter.mp hy).2
  apply hI hxI hyI (fun h => hxy (kernelC9Embedding.injective h))
  change _ ≠ _ ∧ (cycleRel 10 9 _ _ ∨ cycleRel 10 9 _ _)
  change x ≠ y ∧ (cycleRel 9 9 x y ∨ cycleRel 9 9 y x) at hadj
  exact ⟨fun h => hxy (kernelC9Embedding.injective h), hadj.2⟩

def kernelIsoEmbedding : Fin 1 ↪ Fin 10 where
  toFun x := ⟨x.val + 9, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 10 => z.val) h
    apply Fin.ext
    change x.val + 9 = y.val + 9 at hv
    omega

def kernelIsoSlice (I : Finset (Fin 10)) : Finset (Fin 1) :=
  Finset.univ.filter (fun x => kernelIsoEmbedding x ∈ I)

def kernelJoinParts (p : Finset (Fin 9) × Finset (Fin 1)) : Finset (Fin 10) :=
  p.1.map kernelC9Embedding ∪ p.2.map kernelIsoEmbedding

def kernelC9Product : Finset (Finset (Fin 9) × Finset (Fin 1)) :=
  kernelC9Independents ×ˢ Finset.univ

theorem kernel_iso_slice_map (I : Finset (Fin 10)) :
    (kernelIsoSlice I).map kernelIsoEmbedding = I.filter (fun x => ¬ x.val < 9) := by
  ext x
  simp only [Finset.mem_map, kernelIsoSlice, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, by change ¬ y.val + 9 < 9; omega⟩
  · rintro ⟨hx, hge⟩
    let y : Fin 1 := ⟨x.val - 9, by omega⟩
    have hy : kernelIsoEmbedding y = x := by
      apply Fin.ext
      change (x.val - 9) + 9 = x.val
      omega
    exact ⟨y, by simpa only [hy] using hx, hy⟩

theorem kernel_join_slices (I : Finset (Fin 10)) :
    kernelJoinParts (kernelC9Slice I, kernelIsoSlice I) = I := by
  unfold kernelJoinParts
  rw [kernel_c9_slice_map, kernel_iso_slice_map]
  exact Finset.filter_union_filter_not_eq _ _

-- Only coverage is needed: every summand is a natural number, so even a
-- redundant cover would give a sound upper bound. No unproved enumeration
-- or external certificate enters this argument.
theorem kernel_s10_types_covered :
    cycleTypes 10 9 ⊆ kernelC9Product.image kernelJoinParts := by
  intro I hI
  apply Finset.mem_image.mpr
  refine ⟨(kernelC9Slice I, kernelIsoSlice I), ?_, kernel_join_slices I⟩
  apply Finset.mem_product.mpr
  exact ⟨kernel_c9_independents_complete _
    (kernel_c9_slice_independent I (Finset.mem_filter.mp hI).2.2), Finset.mem_univ _⟩

theorem kernel_s10_sum_le_cover (F : Finset (Fin 10) → ℕ) :
    (∑ I ∈ cycleTypes 10 9, F I) ≤ ∑ p ∈ kernelC9Product, F (kernelJoinParts p) := by
  exact (Finset.sum_le_sum_of_subset kernel_s10_types_covered).trans
    (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))


theorem kernel_s10_beta_of_cycle_bound (R : Finset (Fin 10)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 9),
      (cycleGraph 9 9).IsIndepSet (J : Set (Fin 9)) →
      J ⊆ kernelC9Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 9)).card ≤ b)
    (I : Finset (Fin 10)) (hI : (cycleGraph 10 9).IsIndepSet (I : Set (Fin 10)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC9Slice I ⊆ kernelC9Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC9Slice I) (kernel_c9_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 9)).card ≤ a := by
    rw [← kernel_c9_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 9) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 9)
  omega


run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_types_covered
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_sum_le_cover
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_beta_of_cycle_bound

end Erdos1011.S10C9
