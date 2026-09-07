import Erdos1212Kernel.TaoPNTDiskGeometry

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem eventually_taoPNT_delta_le_zeroFreeBaseRadius (d : Real) (hd : 0 ≤ d) :
    ∀ᶠ U : Real in atTop,
      (399 / 100 : Real) *
          (d / Real.log (3 + (2 * Real.pi) * U)) ≤
        taoZeroFreeBaseRadius U / 4 := by
  have hU : ∀ᶠ U : Real in atTop, 1 < U := eventually_gt_atTop 1
  have hloglog : ∀ᶠ U : Real in atTop,
      1596 * d ≤ Real.log (Real.log U) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (1596 * d)
  filter_upwards [hU, hloglog] with U hU hll
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have harg : 0 < 3 + (2 * Real.pi) * U := by positivity
  have hUarg : U ≤ 3 + (2 * Real.pi) * U := by
    have hpi := Real.pi_gt_three
    nlinarith
  have hlogOrder : Real.log U ≤ Real.log (3 + (2 * Real.pi) * U) :=
    Real.log_le_log (by positivity) hUarg
  have hlogArg : 0 < Real.log (3 + (2 * Real.pi) * U) :=
    hlogU.trans_le hlogOrder
  have hdelta : d / Real.log (3 + (2 * Real.pi) * U) ≤
      d / Real.log U :=
    div_le_div_of_nonneg_left hd hlogU hlogOrder
  calc
    (399 / 100 : Real) *
        (d / Real.log (3 + (2 * Real.pi) * U)) ≤
      (399 / 100 : Real) * (d / Real.log U) :=
        mul_le_mul_of_nonneg_left hdelta (by norm_num)
    _ ≤ Real.log (Real.log U) / (400 * Real.log U) := by
      rw [show (399 / 100 : Real) * (d / Real.log U) =
          ((399 / 100 : Real) * d) / Real.log U by ring]
      rw [show Real.log (Real.log U) / (400 * Real.log U) =
          (Real.log (Real.log U) / 400) / Real.log U by ring]
      apply (div_le_div_iff_of_pos_right hlogU).2
      nlinarith
    _ = taoZeroFreeBaseRadius U / 4 := by
      unfold taoZeroFreeBaseRadius
      ring

theorem exists_taoPNT_delta_zeroFreeBaseRadius_threshold
    (d : Real) (hd : 0 ≤ d) :
    ∃ U₀ : Real, ∀ U, U₀ ≤ U →
      (399 / 100 : Real) *
          (d / Real.log (3 + (2 * Real.pi) * U)) ≤
        taoZeroFreeBaseRadius U / 4 := by
  exact Filter.eventually_atTop.1
    (eventually_taoPNT_delta_le_zeroFreeBaseRadius d hd)

end

end Erdos1212Kernel
