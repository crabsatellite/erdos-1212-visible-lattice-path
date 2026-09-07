import Erdos1212Kernel.TaoDerivativeFamily
import Erdos1212Kernel.TaoVdcRate
import Erdos1212Kernel.TaoSecondDerivativeBase

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

theorem taoVdc_family_base (F : Nat → Real → Real) (a : Int) (M N : Nat) {A T C : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N)
    (hC : 16 * (2 + 2 * Real.pi) ≤ C)
    (hF : taoDerivativeHypotheses F 2 (a : Real) ((a : Real) + M) A N T) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
      C * A ^ (2 * taoVdcAlpha 2) * taoVdcRate 2 N T := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hbase := taoSecondDerivative_proposition10_base (F 0) (F 1) (F 2) (F 3) a M N hA hN hT hMN
    (hF.1 0 (by omega)) (hF.1 1 (by omega)) (hF.1 2 le_rfl) hF.2.1
    (fun x hx => by simpa only [pow_one] using hF.2.2 1 (by decide) x hx)
    (hF.2.2 2 (by decide)) (hF.2.2 3 (by decide))
  rw [taoVdc_amplitude_two, taoVdcRate_two hNp hT]
  change ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
    C * A ^ 2 * taoSecondDerivativeRate N T
  have hmul := mul_le_mul_of_nonneg_right hC
    (mul_nonneg (sq_nonneg A) (taoSecondDerivative_rate_nonneg hNp hT))
  exact hbase.trans (by simpa only [taoSecondDerivativeRate, mul_assoc] using hmul)

end

end Erdos1212Kernel
