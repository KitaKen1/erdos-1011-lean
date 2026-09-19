import R5Kernel.Parts.M080
import R5Kernel.Audit

namespace Erdos1011Kernel

theorem formal_target_r5_ge80 :
    ∀ n : ℕ, 80 ≤ n →
      Erdos1011.M 5 n = n ^ 2 / 4 - 3 * n + 14 ∧
      Erdos1011.f 5 n = (n ^ 2 / 4 - 3 * n + 14) + 1 ∧
      Erdos1011.ThresholdExtremalOffset 5 n :=
  Erdos1011.fixed_five_candidate

#check formal_target_r5_ge80
#print axioms formal_target_r5_ge80
run_cmd R5Kernel.checkStandardAxioms ``formal_target_r5_ge80

end Erdos1011Kernel
