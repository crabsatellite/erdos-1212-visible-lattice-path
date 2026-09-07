import Erdos1212Kernel.TaoVdcExponents
import Mathlib.Data.Real.Sqrt

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

theorem taoVdc_square_root_majorant {C D P B : Real} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hB : 0 ≤ B) :
    Real.sqrt (C * D ^ 2 * (4 * P ^ 2 + B ^ 2)) ≤ Real.sqrt C * D * (2 * P + B) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hpoly : 4 * P ^ 2 + B ^ 2 ≤ (2 * P + B) ^ 2 := by nlinarith [mul_nonneg hP hB]
  have hprod := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hC (sq_nonneg D))
  have he : (Real.sqrt C * D * (2 * P + B)) ^ 2 = C * D ^ 2 * (2 * P + B) ^ 2 := by
    calc
      _ = (Real.sqrt C) ^ 2 * D ^ 2 * (2 * P + B) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hC]
  rw [he]
  exact hprod

theorem taoVdc_constant_closes_step {C D P B : Real} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hB : 0 ≤ B) (hclose : 4 + 4 * Real.sqrt C ≤ C) :
    2 * (2 * B + Real.sqrt C * D * (2 * P + B)) ≤ C * D * (P + B) := by
  have hDP : 0 ≤ D * P := mul_nonneg (by linarith) hP
  have hDB : B ≤ D * B := by nlinarith [mul_le_mul_of_nonneg_right hD hB]
  have hrootB : 0 ≤ Real.sqrt C * D * B := by positivity
  have hmid : 2 * (2 * B + Real.sqrt C * D * (2 * P + B)) ≤
      (4 + 4 * Real.sqrt C) * D * (P + B) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hclose (show 0 ≤ D * (P + B) by positivity)
  exact hmid.trans (by simpa only [mul_assoc] using h)

theorem taoVdc_trivial_from_rate {S C D R : Real} (hS : S ≤ 1) (hC : 2 ≤ C)
    (hD : 1 ≤ D) (hR : 1 / 2 ≤ R) : S ≤ C * D * R := by
  have hCD : 2 ≤ C * D := by nlinarith [mul_le_mul_of_nonneg_left hD (show 0 ≤ C by linarith)]
  have h := mul_le_mul hCD hR (by norm_num : (0 : Real) ≤ 1 / 2) (by nlinarith : 0 ≤ C * D)
  linarith

end

end Erdos1212Kernel
