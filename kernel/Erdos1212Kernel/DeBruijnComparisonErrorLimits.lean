import Erdos1212Kernel.DeBruijnF1PositiveComparison
import Erdos1212Kernel.DeBruijnF1G1SaddleProducts

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The actual source comparison defect on printed page 30. -/
def deBruijnComparisonError (C u : Real) : Real := deBruijnF1 u - C * deBruijnRho u

theorem deBruijnComparisonError_ratio_limit {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) :
    Tendsto (fun u : Real => deBruijnComparisonError C u / deBruijnF1 u) atTop (nhds 0) := by
  have h := (tendsto_const_nhds (x := (1 : Real))).sub (hInv.const_mul C)
  have hv : 1 - C * (1 / C) = 0 := by field_simp; norm_num
  rw [hv] at h
  apply h.congr'
  filter_upwards [eventually_deBruijnF1_pos] with u hu
  unfold deBruijnComparisonError
  field_simp [hu.ne']

theorem deBruijnComparisonError_product_limit {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) :
    Tendsto (fun u : Real => deBruijnComparisonError C u * deBruijn1951G1 u) atTop (nhds 0) := by
  have h := (deBruijnComparisonError_ratio_limit hC hInv).mul tendsto_deBruijnF1G1_product
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_deBruijnF1_pos] with u hu
  field_simp [hu.ne']

theorem deBruijnComparisonError_shifted_product_limit {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) :
    Tendsto (fun u : Real => u * deBruijnComparisonError C u * deBruijn1951G1 (u - 1)) atTop (nhds 0) := by
  have h := (deBruijnComparisonError_ratio_limit hC hInv).mul tendsto_deBruijnF1G1_shifted_product
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_deBruijnF1_pos] with u hu
  field_simp [hu.ne']

end

end Erdos1212Kernel
