import R5Kernel.Symmetry

set_option Elab.async false

namespace R5Kernel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem independent_map_iff (G : SimpleGraph α) (H : SimpleGraph β)
    (e : α ≃ β) (hadj : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y)
    (I : Finset α) :
    H.IsIndepSet (I.map e.toEmbedding : Set β) ↔ G.IsIndepSet (I : Set α) := by
  constructor
  · intro h x hx y hy hne hxy
    exact h (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
      (fun he => hne (e.injective he)) ((hadj x y).mpr hxy)
  · intro h x hx y hy hne hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact h ha hb (fun he => hne (congrArg e he)) ((hadj a b).mp hxy)

def independentFamily [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    Finset (Finset α) := Finset.univ.filter (fun I => I.Nonempty ∧ G.IsIndepSet (I : Set α))

theorem independentFamily_equiv [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : α ≃ β) (hadj : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y) :
    mappedFamily e (independentFamily G) = independentFamily H := by
  ext J
  constructor
  · intro hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_map.mp hJ
    have hgood := (Finset.mem_filter.mp hI).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hgood.1.map,
      (independent_map_iff G H e hadj I).mpr hgood.2⟩
  · intro hJ
    have hgood := (Finset.mem_filter.mp hJ).2
    let I := J.map e.symm.toEmbedding
    have heq : I.map e.toEmbedding = J := by
      ext x
      simp [I]
    apply Finset.mem_map.mpr
    refine ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, heq⟩
    · exact hgood.1.map
    · apply (independent_map_iff G H e hadj I).mp
      simpa only [heq] using hgood.2

theorem graph_dualCertificate_transport [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : α ≃ β) (hadj : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y)
    (R : Finset α) (b d bound : ℕ) (w : α → ℕ)
    (hbeta : ∀ I ∈ independentFamily G, I ⊆ R → I.card ≤ b)
    (hvalue : dualValue (independentFamily G) R b d w ≤ bound) :
    (∀ J ∈ independentFamily H, J ⊆ R.map e.toEmbedding → J.card ≤ b) ∧
      dualValue (independentFamily H) (R.map e.toEmbedding) b d
        (fun y => w (e.symm y)) ≤ bound := by
  simpa only [independentFamily_equiv G H e hadj] using
    dualCertificate_transport e (independentFamily G) R b d bound w hbeta hvalue

run_cmd checkStandardAxioms ``independent_map_iff
run_cmd checkStandardAxioms ``independentFamily_equiv
run_cmd checkStandardAxioms ``graph_dualCertificate_transport

end R5Kernel
