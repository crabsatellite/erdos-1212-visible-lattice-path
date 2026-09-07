import Erdos1212Kernel.DeBruijnAdjointUniformBounds
import Erdos1212Kernel.DeBruijnDickmanAbelianLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem tendsto_deBruijn1951_scaled_regular_part :
    Tendsto (fun a : Real => a * (deBruijn1951NearIntegral (a - 1) + deBruijn1951PositiveTail (a - 1)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply squeeze_zero_norm' (a := fun a : Real => a * deBruijn1951RegularPartBound)
  · filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iic_mem_nhds (show (0 : Real) < 1 by norm_num))] with a ha hOne
    have haPos : 0 < a := ha
    have h := deBruijn1951RegularPart_bound (a := a) ⟨haPos, hOne⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos haPos]
    exact mul_le_mul_of_nonneg_left h haPos.le
  · have h0 : Tendsto (fun a : Real => a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := continuousWithinAt_id.tendsto
    simpa only [zero_mul] using h0.mul_const deBruijn1951RegularPartBound

theorem deBruijn1951_G1_boundary_identity {a : Real} (ha : 0 < a) :
    -a * deBruijn1951G1 (a - 1) = deBruijn1951BoundaryAverage a -
      a * (deBruijn1951NearIntegral (a - 1) + deBruijn1951PositiveTail (a - 1)) := by
  rw [deBruijn1951G1_eq_regularized (by linarith : -1 < a - 1)]
  unfold deBruijn1951RegularizedAdjoint deBruijn1951NegativeTail deBruijn1951BoundaryAverage
  rw [sub_add_cancel]
  ring

/-- The complete boundary limit in (2.15), now for G1 defined by the
proved principal value rather than only for its negative tail. -/
theorem deBruijn1951_G1_boundary_normalization :
    Tendsto (fun a : Real => -a * deBruijn1951G1 (a - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h := tendsto_deBruijn1951BoundaryAverage.sub tendsto_deBruijn1951_scaled_regular_part
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (deBruijn1951_G1_boundary_identity ha).symm

end

end Erdos1212Kernel
