import R5Kernel.Common
import R5Kernel.Audit

set_option Elab.async false

run_cmd do
  Lean.Elab.Command.liftIO do
    IO.println "BEGIN symmetry transport proof"
    (← IO.getStdout).flush

/- General, proof-producing transport of the actual natural-valued dual
inequality. No table enumeration or native evaluation is used here. -/
namespace R5Kernel
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def dualValue (U : Finset (Finset α)) (R : Finset α)
    (b d : ℕ) (w : α → ℕ) : ℕ :=
  b * (∑ x ∈ R, w x) +
    ∑ I ∈ U, if (I ∩ R).Nonempty then
      d * I.card - ∑ x ∈ I, if x ∈ R then w x else 0
    else 0

def mappedFamily (e : α ≃ β) (U : Finset (Finset α)) : Finset (Finset β) :=
  U.map (Finset.mapEmbedding e.toEmbedding).toEmbedding

theorem dualValue_equiv (e : α ≃ β) (U : Finset (Finset α))
    (R : Finset α) (b d : ℕ) (w : α → ℕ) :
    dualValue (mappedFamily e U) (R.map e.toEmbedding) b d (fun y => w (e.symm y)) =
      dualValue U R b d w := by
  simp [dualValue, mappedFamily, Finset.sum_map, ← Finset.map_inter]

run_cmd checkStandardAxioms ``dualValue_equiv

theorem betaValid_equiv (e : α ≃ β) (U : Finset (Finset α))
    (R : Finset α) (b : ℕ) :
    (∀ J ∈ mappedFamily e U, J ⊆ R.map e.toEmbedding → J.card ≤ b) ↔
      (∀ I ∈ U, I ⊆ R → I.card ≤ b) := by
  simp [mappedFamily, Finset.mem_map, Finset.map_subset_map]

run_cmd checkStandardAxioms ``betaValid_equiv

theorem dualCertificate_transport (e : α ≃ β) (U : Finset (Finset α))
    (R : Finset α) (b d bound : ℕ) (w : α → ℕ)
    (hbeta : ∀ I ∈ U, I ⊆ R → I.card ≤ b)
    (hvalue : dualValue U R b d w ≤ bound) :
    (∀ J ∈ mappedFamily e U, J ⊆ R.map e.toEmbedding → J.card ≤ b) ∧
      dualValue (mappedFamily e U) (R.map e.toEmbedding) b d
        (fun y => w (e.symm y)) ≤ bound := by
  refine ⟨(betaValid_equiv e U R b).mpr hbeta, ?_⟩
  simpa only [dualValue_equiv] using hvalue

run_cmd checkStandardAxioms ``dualCertificate_transport

end R5Kernel
