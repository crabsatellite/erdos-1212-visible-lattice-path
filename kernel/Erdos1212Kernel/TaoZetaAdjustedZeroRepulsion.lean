import Erdos1212Kernel.TaoZetaAdjustedReciprocalPositivity

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem four_mul_le_residual_norm_combination_of_three_four_one
    {L0 L1 L2 S0 S1 S2 E0 E1 E2 : Complex} {k : Real}
    (hpos : 0 ≤ (3 * L0 + 4 * L1 + L2).re)
    (h0 : L0 + S0 = -E0) (h1 : L1 + S1 = -E1)
    (h2 : L2 + S2 = -E2)
    (hS0 : 0 ≤ S0.re) (hk : k ≤ S1.re) (hS2 : 0 ≤ S2.re) :
    4 * k ≤ 3 * ‖E0‖ + 4 * ‖E1‖ + ‖E2‖ := by
  have h0re := congrArg Complex.re h0
  have h1re := congrArg Complex.re h1
  have h2re := congrArg Complex.re h2
  simp only [Complex.add_re, Complex.neg_re] at h0re h1re h2re
  norm_num [Complex.add_re, Complex.mul_re] at hpos
  have hE0 : -E0.re ≤ ‖E0‖ :=
    (neg_le_abs E0.re).trans (Complex.abs_re_le_norm E0)
  have hE1 : -E1.re ≤ ‖E1‖ :=
    (neg_le_abs E1.re).trans (Complex.abs_re_le_norm E1)
  have hE2 : -E2.re ≤ ‖E2‖ :=
    (neg_le_abs E2.re).trans (Complex.abs_re_le_norm E2)
  linarith

theorem three_div_gap_le_adjustedResidualNormCombination
    {σ β t R0 R1 R2 : Real} (hσ : 1 < σ)
    (hR0 : 0 < R0) (hR1 : 0 < R1) (hR2 : 0 < R2)
    (hAvoid0 : ∀ z ∈ closedBall (σ : Complex) R0, z ≠ 1)
    (hAvoid1 : ∀ z ∈ closedBall
      ((σ : Complex) + (t : Complex) * Complex.I) R1, z ≠ 1)
    (hAvoid2 : ∀ z ∈ closedBall
      ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) R2, z ≠ 1)
    (hβσ : β < σ)
    (hρzero : riemannZeta ((β : Complex) + (t : Complex) * Complex.I) = 0)
    (hρU : (β : Complex) + (t : Complex) * Complex.I ∈
      closedBall ((σ : Complex) + (t : Complex) * Complex.I) R1)
    (hhalf : 2 * (σ - β) ≤ R1)
    {E0 E1 E2 : Complex}
    (h0 : taoZetaLogDerivative (σ : Complex) +
        taoZetaAdjustedReciprocalSum (σ : Complex) R0 = -E0)
    (h1 : taoZetaLogDerivative
          ((σ : Complex) + (t : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum
          ((σ : Complex) + (t : Complex) * Complex.I) R1 = -E1)
    (h2 : taoZetaLogDerivative
          ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum
          ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) R2 = -E2) :
    3 / (σ - β) ≤ 3 * ‖E0‖ + 4 * ‖E1‖ + ‖E2‖ := by
  have hcenter0 : 1 < ((σ : Real) : Complex).re := by simpa using hσ
  have hcenter1 : 1 < ((σ : Complex) + (t : Complex) * Complex.I).re := by simp [hσ]
  have hcenter2 :
      1 < ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I).re := by simp [hσ]
  have hS0 := re_taoZetaAdjustedReciprocalSum_nonneg hR0 hcenter0 hAvoid0
  have hS2 := re_taoZetaAdjustedReciprocalSum_nonneg hR2 hcenter2 hAvoid2
  have hkernelSum := re_taoZetaAdjustedReciprocalSum_ge_kernel hR1 hcenter1
    hAvoid1 hρU hρzero
  have hkernel := three_div_four_mul_gap_le_re_taoZetaAdjustedKernel
    (t := t) hR1 hβσ hhalf
  have htarget : 3 / (4 * (σ - β)) ≤
      (taoZetaAdjustedReciprocalSum
        ((σ : Complex) + (t : Complex) * Complex.I) R1).re :=
    hkernel.trans hkernelSum
  have hpos := taoZetaLogDerivative_three_four_one_nonneg σ t hσ
  have hcombo := four_mul_le_residual_norm_combination_of_three_four_one
    hpos h0 h1 h2 hS0 htarget hS2
  calc
    3 / (σ - β) = 4 * (3 / (4 * (σ - β))) := by
      field_simp [sub_ne_zero.mpr (Ne.symm hβσ.ne)]
    _ ≤ 3 * ‖E0‖ + 4 * ‖E1‖ + ‖E2‖ := hcombo

end

end Erdos1212Kernel
