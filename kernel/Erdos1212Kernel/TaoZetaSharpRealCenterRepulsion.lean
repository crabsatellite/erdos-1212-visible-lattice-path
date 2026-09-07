import Erdos1212Kernel.TaoZetaPoleRemoved

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem fifteen_div_four_gap_le_sharpRealCenter_and_adjustedResidualNorm
    {σ β t R1 R2 : Real} (hσ : 1 < σ)
    (hR1 : 0 < R1) (hR2 : 0 < R2)
    (hAvoid1 : ∀ z ∈ closedBall
      ((σ : Complex) + (t : Complex) * Complex.I) R1, z ≠ 1)
    (hAvoid2 : ∀ z ∈ closedBall
      ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) R2, z ≠ 1)
    (hβσ : β < σ)
    (hρzero : riemannZeta ((β : Complex) + (t : Complex) * Complex.I) = 0)
    (hρU : (β : Complex) + (t : Complex) * Complex.I ∈
      closedBall ((σ : Complex) + (t : Complex) * Complex.I) R1)
    (hquarter : 4 * (σ - β) ≤ R1)
    (hL0 : ‖taoZetaLogDerivative (σ : Complex)‖ ≤ 9 / (8 * (σ - 1)))
    {E1 E2 : Complex}
    (h1 : taoZetaLogDerivative
          ((σ : Complex) + (t : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum
          ((σ : Complex) + (t : Complex) * Complex.I) R1 = -E1)
    (h2 : taoZetaLogDerivative
          ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum
          ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) R2 = -E2) :
    15 / (4 * (σ - β)) ≤
      27 / (8 * (σ - 1)) + 4 * ‖E1‖ + ‖E2‖ := by
  let L0 := taoZetaLogDerivative (σ : Complex)
  let L1 := taoZetaLogDerivative ((σ : Complex) + (t : Complex) * Complex.I)
  let L2 := taoZetaLogDerivative
    ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)
  let S1 := taoZetaAdjustedReciprocalSum
    ((σ : Complex) + (t : Complex) * Complex.I) R1
  let S2 := taoZetaAdjustedReciprocalSum
    ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I) R2
  have hcenter1 : 1 < ((σ : Complex) + (t : Complex) * Complex.I).re := by simp [hσ]
  have hcenter2 :
      1 < ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I).re := by simp [hσ]
  have hS2 : 0 ≤ S2.re :=
    re_taoZetaAdjustedReciprocalSum_nonneg hR2 hcenter2 hAvoid2
  have hkernelSum :
      (taoZetaAdjustedKernel
        ((σ : Complex) + (t : Complex) * Complex.I) R1
        ((β : Complex) + (t : Complex) * Complex.I)).re ≤ S1.re :=
    re_taoZetaAdjustedReciprocalSum_ge_kernel hR1 hcenter1 hAvoid1 hρU hρzero
  have hkernel := fifteen_div_sixteen_mul_gap_le_re_taoZetaAdjustedKernel
    (t := t) hR1 hβσ hquarter
  have htarget : 15 / (16 * (σ - β)) ≤ S1.re := hkernel.trans hkernelSum
  have hpos : 0 ≤ (3 * L0 + 4 * L1 + L2).re := by
    simpa only [L0, L1, L2] using taoZetaLogDerivative_three_four_one_nonneg σ t hσ
  have hcombo := four_mul_le_residual_norm_combination_of_three_four_one
    (L0 := L0) (L1 := L1) (L2 := L2)
    (S0 := 0) (S1 := S1) (S2 := S2)
    (E0 := -L0) (E1 := E1) (E2 := E2)
    hpos (by simp) (by simpa only [L1, S1] using h1)
    (by simpa only [L2, S2] using h2) (by simp) htarget hS2
  have hL0' : ‖L0‖ ≤ 9 / (8 * (σ - 1)) := by simpa only [L0] using hL0
  have hbound :
      4 * (15 / (16 * (σ - β))) ≤
        27 / (8 * (σ - 1)) + 4 * ‖E1‖ + ‖E2‖ := by
    calc
      _ ≤ 3 * ‖-L0‖ + 4 * ‖E1‖ + ‖E2‖ := hcombo
      _ ≤ 3 * (9 / (8 * (σ - 1))) + 4 * ‖E1‖ + ‖E2‖ := by
        rw [norm_neg]
        gcongr
      _ = 27 / (8 * (σ - 1)) + 4 * ‖E1‖ + ‖E2‖ := by ring
  calc
    15 / (4 * (σ - β)) = 4 * (15 / (16 * (σ - β))) := by
      field_simp [sub_ne_zero.mpr (Ne.symm hβσ.ne)]
      norm_num
    _ ≤ _ := hbound

end

end Erdos1212Kernel
