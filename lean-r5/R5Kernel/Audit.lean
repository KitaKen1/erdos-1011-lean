import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace R5Kernel
open Lean Elab Command

/-- Fail closed on every axiom outside the three standard Lean axioms.
In particular native computation axioms and sorryAx are not exceptions. -/
def checkStandardAxioms (target : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms target
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let extra := axioms.filter fun name => !allowed.contains name
  unless extra.isEmpty do
    throwError "R5_KERNEL_REJECTED {target}: extra={extra.size}; first={extra[0]!}"
  logInfo m!"R5_KERNEL_PASS {target}: standard={axioms.size}, extra=0, sorryAx=0"

end R5Kernel
