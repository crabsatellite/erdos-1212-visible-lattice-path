import Erdos1212Kernel.TaoZetaCanonicalResidualThreshold
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem tendsto_mul_taoCanonicalResidualConstant_scaled_nhdsGT_zero :
    Tendsto (fun a : Real =>
      a * taoCanonicalResidualConstant (20 * a / 21))
      (𝓝[>] 0) (nhds 0) := by
  let c : Real := 21 / 20
  have hcpos : 0 < c := by unfold c; norm_num
  have hid : Tendsto (fun a : Real => a) (𝓝[>] 0) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun a : Real => a + c) (𝓝[>] 0) (nhds c) := by
    simpa using hid.add_const c
  have hlogShift : Tendsto (fun a : Real => Real.log (a + c))
      (𝓝[>] 0) (nhds (Real.log c)) :=
    (Real.continuousAt_log hcpos.ne').tendsto.comp hshift
  have hfirst : Tendsto (fun a : Real => a * Real.log (a + c))
      (𝓝[>] 0) (nhds 0) := by
    simpa using hid.mul hlogShift
  have hself : Tendsto (fun a : Real => a * Real.log a)
      (𝓝[>] 0) (nhds 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hlogRatio : Tendsto (fun a : Real =>
      a * Real.log (1 + 1 / (20 * a / 21)))
      (𝓝[>] 0) (nhds 0) := by
    have hdiff : Tendsto (fun a : Real =>
        a * Real.log (a + c) - a * Real.log a)
        (𝓝[>] 0) (nhds 0) := by
      simpa using hfirst.sub hself
    refine hdiff.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hapos : 0 < a := ha
    have harg : 1 + 1 / (20 * a / 21) = (a + c) / a := by
      unfold c
      field_simp [hapos.ne']
    rw [harg, Real.log_div (by positivity : a + c ≠ 0) hapos.ne']
    ring
  unfold taoCanonicalResidualConstant
  have hconst : Tendsto (fun a : Real =>
      a * (3200 * (7 + 48 * Real.log 2))) (𝓝[>] 0) (nhds 0) := by
    convert hid.const_mul (3200 * (7 + 48 * Real.log 2)) using 1
    · funext a
      ring
    · ring
  have hlogScaled : Tendsto (fun a : Real =>
      a * (3200 * 4 * Real.log (1 + 1 / (20 * a / 21))))
      (𝓝[>] 0) (nhds 0) := by
    convert hlogRatio.const_mul (3200 * 4) using 1
    · funext a
      ring
    · ring
  convert hconst.add hlogScaled using 1
  · funext a
    ring
  · ring

theorem exists_taoZeroFreeParameter :
    ∃ a : Real, 0 < a ∧
      a * taoCanonicalResidualConstant (20 * a / 21) ≤ 1 / 100 := by
  have hevent : ∀ᶠ a : Real in 𝓝[>] 0,
      a * taoCanonicalResidualConstant (20 * a / 21) < 1 / 100 :=
    (tendsto_order.1
      tendsto_mul_taoCanonicalResidualConstant_scaled_nhdsGT_zero).2
      (1 / 100) (by norm_num)
  obtain ⟨a, hbound, ha⟩ := (hevent.and self_mem_nhdsWithin).exists
  exact ⟨a, ha, hbound.le⟩

end

end Erdos1212Kernel
