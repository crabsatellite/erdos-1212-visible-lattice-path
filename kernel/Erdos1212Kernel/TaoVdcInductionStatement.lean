import Erdos1212Kernel.TaoVdcFamilyBase

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

def taoVdcBound (k : Nat) (C : Real) : Prop :=
  ∀ (F : Nat → Real → Real) (a : Int) (M N : Nat) {A T : Real},
    1 ≤ A → 0 < N → 0 < T → M ≤ N →
    taoDerivativeHypotheses F k (a : Real) ((a : Real) + M) A N T →
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
      C * A ^ (2 * taoVdcAlpha k) * taoVdcRate k N T

theorem taoVdcBound_base {C : Real} (hC : 16 * (2 + 2 * Real.pi) ≤ C) : taoVdcBound 2 C := by
  intro F a M N A T hA hN hT hMN hF
  exact taoVdc_family_base F a M N hA hN hT hMN hC hF

end

end Erdos1212Kernel
