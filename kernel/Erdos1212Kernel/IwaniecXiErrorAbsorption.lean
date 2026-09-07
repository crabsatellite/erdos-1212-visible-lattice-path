import Erdos1212Kernel.IwaniecXiScaleGrowth
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1400000

theorem iwaniec_exp_two_sub_power_tendsto_zero {c : Real} (hc : 0 < c) :
    Tendsto (fun t : Real => Real.exp (2 * t - c * t ^ (11 / 10 : Real))) atTop (nhds 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)) ?_
    Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_ge_atTop (1 : Real),
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).eventually_ge_atTop (3 / c)] with t ht hp
  have ht0 : 0 < t := by linarith
  have hthree : 3 ≤ t ^ (1 / 10 : Real) * c := (div_le_iff₀ hc).mp hp
  have hpow : t ^ (11 / 10 : Real) = t * t ^ (1 / 10 : Real) := by
    rw [show (11 / 10 : Real) = 1 + 1 / 10 by norm_num, Real.rpow_add ht0, Real.rpow_one]
  have hm : 3 * t ≤ c * t ^ (11 / 10 : Real) := by
    have h := mul_le_mul_of_nonneg_right hthree ht0.le
    rw [hpow]
    nlinarith
  exact Real.exp_le_exp.mpr (by linarith)

theorem tendsto_iwaniecLogLogThree_atTop :
    Tendsto (fun y : Real => Real.log (Real.log (3 * y))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : Real) < 3)))

theorem iwaniecPaperXi_root_ratio {y : Real} (hy : 1 < y)
    (hu : 0 < Real.log (Real.log (3 * y))) :
    Real.sqrt (Real.log y / iwaniecPaperXi y) = (Real.log (Real.log (3 * y))) ^ (11 / 10 : Real) := by
  have hlog := Real.log_pos hy
  have hp := Real.rpow_pos_of_pos hu (11 / 5 : Real)
  have hratio : Real.log y / iwaniecPaperXi y = (Real.log (Real.log (3 * y))) ^ (11 / 5 : Real) := by
    unfold iwaniecPaperXi
    field_simp [hlog.ne', hp.ne']
  rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
  norm_num

theorem iwaniecPaperXi_le_exp_loglog {y : Real} (hy : 1 < y)
    (hu : 1 ≤ Real.log (Real.log (3 * y))) :
    iwaniecPaperXi y ≤ Real.exp (Real.log (Real.log (3 * y))) := by
  have hy0 : 0 < y := by linarith
  have hlog := Real.log_pos hy
  have h3 : 1 < 3 * y := by linarith
  have hp : 1 ≤ (Real.log (Real.log (3 * y))) ^ (11 / 5 : Real) :=
    Real.one_le_rpow hu (by norm_num)
  calc
    _ ≤ Real.log y := div_le_self hlog.le hp
    _ ≤ Real.log (3 * y) := Real.log_le_log hy0 (by linarith)
    _ = _ := (Real.exp_log (Real.log_pos h3)).symm

/-- The paper's exact xi(y) and logarithmic cutoff are retained. This
scalar estimate includes the original coefficient-one case below. -/
theorem tendsto_iwaniecXi_error_factor {c : Real} (hc : 0 < c) :
    Tendsto (fun y : Real => iwaniecPaperXi y ^ 2 *
      Real.exp (-c * Real.sqrt (Real.log y / iwaniecPaperXi y))) atTop (nhds 0) := by
  have hlim := (iwaniec_exp_two_sub_power_tendsto_zero hc).comp tendsto_iwaniecLogLogThree_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)) _ hlim
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_iwaniecLogLogThree_atTop.eventually_ge_atTop 1] with y hy hu
  have hu0 : 0 < Real.log (Real.log (3 * y)) := by linarith
  have hxi0 : 0 ≤ iwaniecPaperXi y := div_nonneg (Real.log_pos hy).le (Real.rpow_nonneg hu0.le _)
  have hsq := pow_le_pow_left₀ hxi0 (iwaniecPaperXi_le_exp_loglog hy hu) 2
  rw [iwaniecPaperXi_root_ratio hy hu0]
  calc
    _ ≤ (Real.exp (Real.log (Real.log (3 * y)))) ^ 2 *
        Real.exp (-c * (Real.log (Real.log (3 * y))) ^ (11 / 10 : Real)) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = _ := by
      rw [pow_two, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The original error factor in Iwaniec's Corollary 3 tends to zero. -/
theorem tendsto_iwaniecXi_unit_error_factor :
    Tendsto (fun y : Real => iwaniecPaperXi y ^ 2 *
      Real.exp (-Real.sqrt (Real.log y / iwaniecPaperXi y))) atTop (nhds 0) := by
  simpa only [neg_one_mul] using tendsto_iwaniecXi_error_factor (c := 1) (by norm_num)

theorem eventually_iwaniecXi_source_error_absorbed {C : Real} (hC : 0 ≤ C) :
    ∀ᶠ y : Real in atTop, 100 * C * iwaniecPaperXi y ^ 2 *
      Real.exp (-Real.sqrt (Real.log y / iwaniecPaperXi y)) ≤ 1 := by
  have h := tendsto_iwaniecXi_unit_error_factor.const_mul (100 * C)
  simp only [mul_zero] at h
  have he := h.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [he] with y hy
  nlinarith

end

end Erdos1212Kernel
