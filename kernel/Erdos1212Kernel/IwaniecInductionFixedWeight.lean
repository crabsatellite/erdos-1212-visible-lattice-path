import Erdos1212Kernel.IwaniecAuxiliaryXiWeightScale
import Erdos1212Kernel.IwaniecAuxiliaryWeightCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 600000

theorem iwaniecWeightPower_fixed_linear_bound {level t : Real}
    (hy : 1 < level) (ht : 1 ≤ t)
    (hsmall : 5 * t ^ 3 * Real.log t ^ 5 / Real.log level ^ 2 ≤ 1) :
    iwaniecAuxWeightPower level t ≤ 1 + 10 * t ^ 3 * Real.log t ^ 5 / Real.log level ^ 2 := by
  let D := 5 * t ^ 3 * Real.log t ^ 5 / Real.log level ^ 2
  have ht0 : 0 ≤ t := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlogbase := Real.log_le_sub_one_of_pos (iwaniecAuxWeightBase_pos level ht)
  have hlogbound : Real.log (iwaniecAuxWeightBase level t) * (5 * t) ≤ D := by
    calc
      _ ≤ (iwaniecAuxWeightBase level t - 1) * (5 * t) :=
        mul_le_mul_of_nonneg_right hlogbase (show 0 ≤ 5 * t by positivity)
      _ = D := by dsimp [D]; unfold iwaniecAuxWeightBase; ring
  have hexp := Real.abs_exp_sub_one_le (x := D) (by rw [abs_of_nonneg hD]; exact hsmall)
  rw [abs_of_nonneg hD] at hexp
  have hupper : Real.exp D ≤ 1 + 2 * D := by have hh := (abs_le.mp hexp).2; linarith
  unfold iwaniecAuxWeightPower
  rw [Real.rpow_def_of_pos (iwaniecAuxWeightBase_pos level ht)]
  calc
    _ ≤ Real.exp D := Real.exp_le_exp.mpr hlogbound
    _ ≤ 1 + 2 * D := hupper
    _ = _ := by dsimp [D]; ring

theorem eventually_iwaniecWeightPower_fixed_linear_bound {t : Real} (ht : 1 ≤ t) :
    ∀ᶠ level : Real in atTop, 1 < level ∧
      iwaniecAuxWeightPower level t ≤ 1 + 10 * t ^ 3 * Real.log t ^ 5 / Real.log level ^ 2 := by
  let A := 5 * t ^ 3 * Real.log t ^ 5
  have hA : 0 ≤ A := by have hlog := Real.log_nonneg ht; dsimp [A]; positivity
  filter_upwards [eventually_gt_atTop (1 : Real), Real.tendsto_log_atTop.eventually_ge_atTop (max 1 A)]
    with level hy hL
  have hL1 : 1 ≤ Real.log level := (le_max_left _ _).trans hL
  have hAL : A ≤ Real.log level := (le_max_right _ _).trans hL
  have hsmall : A / Real.log level ^ 2 ≤ 1 := by
    apply (div_le_one₀ (sq_pos_of_pos (Real.log_pos hy))).mpr
    nlinarith only [hL1, hAL]
  exact ⟨hy, iwaniecWeightPower_fixed_linear_bound hy ht hsmall⟩

theorem iwaniec_induction_slack_scalar {q v a K : Real}
    (hq : 0 < q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hvq : v * q ≤ 1) (hlarge : a + K + a * K < v) :
    (1 - v * q) * (1 + a * q) * (1 + K * q) < 1 := by
  let D := a + K + a * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hv : 0 < v := hD.trans_lt hlarge
  have hprod : (1 + a * q) * (1 + K * q) ≤ 1 + D * q := by
    have hqSq : q ^ 2 ≤ q := by nlinarith only [hq, hq1]
    have hh := mul_le_mul_of_nonneg_left hqSq (mul_nonneg ha hK)
    dsimp [D]
    nlinarith only [hh]
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1 - v * q by linarith)
  have hstrict : (1 - v * q) * (1 + D * q) < 1 := by
    have hpos : 0 < (v - D) * q := mul_pos (sub_pos.mpr hlarge) hq
    have hcross : 0 ≤ v * D * q ^ 2 := by positivity
    nlinarith only [hpos, hcross]
  simpa only [mul_assoc] using hscaled.trans_lt hstrict

end

end Erdos1212Kernel
