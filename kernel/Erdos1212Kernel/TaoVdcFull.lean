import Erdos1212Kernel.TaoVdcInductionStep

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

def taoVdcConstant : Real := 256

theorem taoVdcConstant_base : 16 * (2 + 2 * Real.pi) ≤ taoVdcConstant := by
  have hp := Real.pi_le_four
  unfold taoVdcConstant
  nlinarith

theorem taoVdcConstant_two : 2 ≤ taoVdcConstant := by norm_num [taoVdcConstant]

theorem taoVdcConstant_closes : 4 + 4 * Real.sqrt taoVdcConstant ≤ taoVdcConstant := by
  have hs : Real.sqrt (256 : Real) = 16 := by
    rw [show (256 : Real) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [taoVdcConstant, hs]
  norm_num

/-- The induction is discharged internally. This is not a conditional
interface requiring a lower-order exponential-sum premise. -/
theorem taoVdcBound_all {k : Nat} (hk : 2 ≤ k) : taoVdcBound k taoVdcConstant := by
  induction k, hk using Nat.le_induction with
  | base => exact taoVdcBound_base taoVdcConstant_base
  | succ n hn ih =>
      exact taoVdcBound_step hn taoVdcConstant_two taoVdcConstant_closes ih

/-- Tao Notes 5, Proposition 10, on the literal integer half-open
interval [a,a+M), with M<=N and an explicit absolute constant 256.
The supplied derivative family contains the actual phase and its first
k+1 derivatives, connected by HasDerivAt on the original interval. -/
theorem taoVdc_proposition10 (F : Nat → Real → Real) (k : Nat) (a : Int) (M N : Nat)
    {A T : Real} (hk : 2 ≤ k) (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N)
    (hF : taoDerivativeHypotheses F k (a : Real) ((a : Real) + M) A N T) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
      256 * A ^ (2 * taoVdcAlpha k) *
        ((1 / (N : Real) ^ (taoVdcAlpha k)) * ((N : Real) ^ k / T) ^ (taoVdcBeta k) *
          (Real.log (2 + T)) ^ (taoVdcAlpha k) +
          (T / (N : Real) ^ k) ^ (taoVdcBeta k)) := by
  simpa only [taoVdcConstant, taoVdcRate] using
    (taoVdcBound_all hk F a M N hA hN hT hMN hF)

theorem taoVdc_proposition10_source_amplitude (F : Nat → Real → Real) (k : Nat) (a : Int) (M N : Nat)
    {A T : Real} (hk : 3 ≤ k) (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N)
    (hF : taoDerivativeHypotheses F k (a : Real) ((a : Real) + M) A N T) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
      256 * A ^ (1 / (2 : Real) ^ (k - 3)) *
        ((1 / (N : Real) ^ (1 / (2 : Real) ^ (k - 2))) *
            ((N : Real) ^ k / T) ^ (1 / ((2 : Real) ^ k - 2)) *
            (Real.log (2 + T)) ^ (1 / (2 : Real) ^ (k - 2)) +
          (T / (N : Real) ^ k) ^ (1 / ((2 : Real) ^ k - 2))) := by
  have h := taoVdc_proposition10 F k a M N (by omega) hA hN hT hMN hF
  rw [taoVdc_source_amplitude_exponent hk] at h
  simpa only [taoVdcAlpha, taoVdcBeta] using h

end

end Erdos1212Kernel
