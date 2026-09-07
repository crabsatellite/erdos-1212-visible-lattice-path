import Erdos1212Kernel.TaoLittlewoodZetaBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem tendsto_taoLittlewood_loglog_sq_div_log_rpow :
    Tendsto
      (fun T : Real =>
        Real.log (Real.log T) ^ 2 / (Real.log T) ^ (7 / 8 : Real))
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun L : Real => Real.log L ^ 2 / L ^ (7 / 8 : Real))
      atTop (nhds 0) :=
    by
      have h := (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : Real) < 7 / 8)).tendsto_div_nhds_zero
      apply Filter.Tendsto.congr' _ h
      exact Filter.Eventually.of_forall fun L => by
        change (Real.log L) ^ (2 : Real) / L ^ (7 / 8 : Real) =
          (Real.log L) ^ (2 : Nat) / L ^ (7 / 8 : Real)
        rw [Real.rpow_two]
  exact hbase.comp Real.tendsto_log_atTop

theorem eventually_taoLittlewood_large_scalar :
    ∀ᶠ T : Real in atTop,
      Real.log (Real.log T) ^ 2 /
          (8 * Real.log 2 * Real.log T) ≤
        1 / (4 * (Real.log T) ^ (1 / 8 : Real)) := by
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : ∀ᶠ T : Real in atTop,
      Real.log (Real.log T) ^ 2 / (Real.log T) ^ (7 / 8 : Real) ≤
        2 * Real.log 2 := by
    have h := (tendsto_order.1 tendsto_taoLittlewood_loglog_sq_div_log_rpow).2
      (2 * Real.log 2) (by positivity)
    exact h.mono fun T hT => hT.le
  filter_upwards [hratio, eventually_gt_atTop (Real.exp 1)] with T hratioT hT
  let L : Real := Real.log T
  let A : Real := Real.log L ^ 2
  have hLp : 0 < L := by
    unfold L
    exact Real.log_pos ((Real.one_lt_exp_iff.mpr one_pos).trans hT)
  have hL78 : 0 < L ^ (7 / 8 : Real) := by positivity
  have hL18 : 0 < L ^ (1 / 8 : Real) := by positivity
  have hprod : L ^ (7 / 8 : Real) * L ^ (1 / 8 : Real) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hA : A ≤ (2 * Real.log 2) * L ^ (7 / 8 : Real) := by
    have := (div_le_iff₀ hL78).mp (show A / L ^ (7 / 8 : Real) ≤ 2 * Real.log 2 by
      simpa only [A, L] using hratioT)
    exact this
  have hmul : A * L ^ (1 / 8 : Real) ≤ (2 * Real.log 2) * L := by
    have := mul_le_mul_of_nonneg_right hA hL18.le
    rw [mul_assoc, hprod] at this
    exact this
  have hden1 : 0 < 8 * Real.log 2 * L := by positivity
  apply (div_le_iff₀ hden1).2
  have hrhs : 1 / (4 * L ^ (1 / 8 : Real)) * (8 * Real.log 2 * L) =
      (2 * Real.log 2 * L) / L ^ (1 / 8 : Real) := by
    field_simp
    ring
  rw [hrhs]
  apply (le_div_iff₀ hL18).2
  simpa only [A, L] using hmul

end

end Erdos1212Kernel
