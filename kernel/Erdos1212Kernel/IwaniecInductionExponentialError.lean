import Erdos1212Kernel.IwaniecXiErrorAbsorption

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem iwaniec_exp_linear_sub_power_tendsto_zero (k : Real) {c : Real} (hc : 0 < c) :
    Tendsto (fun t : Real => Real.exp (k * t - c * t ^ (11 / 10 : Real))) atTop (nhds 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)) ?_
    Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_ge_atTop (1 : Real),
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).eventually_ge_atTop ((k + 1) / c)]
    with t ht hp
  have ht0 : 0 < t := by linarith
  have hcoef : k + 1 ≤ t ^ (1 / 10 : Real) * c := (div_le_iff₀ hc).mp hp
  have hpow : t ^ (11 / 10 : Real) = t * t ^ (1 / 10 : Real) := by
    rw [show (11 / 10 : Real) = 1 + 1 / 10 by norm_num, Real.rpow_add ht0, Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_right hcoef ht0.le
  apply Real.exp_le_exp.mpr
  rw [hpow]
  nlinarith only [hscaled]

theorem tendsto_iwaniecXi_log_weighted_error (d : Nat) {c : Real} (hc : 0 < c) :
    Tendsto (fun y : Real => Real.log y ^ d * iwaniecPaperXi y ^ 2 *
      Real.exp (-c * Real.sqrt (Real.log y / iwaniecPaperXi y))) atTop (nhds 0) := by
  have hlim := (iwaniec_exp_linear_sub_power_tendsto_zero ((d : Real) + 2) hc).comp
    tendsto_iwaniecLogLogThree_atTop
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : Real)] with y hy
    have hL := (Real.log_pos hy).le
    positivity
  · filter_upwards [eventually_gt_atTop (1 : Real), tendsto_iwaniecLogLogThree_atTop.eventually_ge_atTop 1]
      with y hy hu
    let u := Real.log (Real.log (3 * y))
    have hu0 : 0 < u := by dsimp [u]; linarith
    have hL0 : 0 ≤ Real.log y := (Real.log_pos hy).le
    have hLexp : Real.log y ≤ Real.exp u := by
      have hh := Real.log_le_log (show 0 < y by linarith) (show y ≤ 3 * y by linarith)
      simpa only [u, Real.exp_log (Real.log_pos (show 1 < 3 * y by linarith))] using hh
    have hXi0 : 0 ≤ iwaniecPaperXi y := div_nonneg hL0 (Real.rpow_nonneg hu0.le _)
    have hXi := iwaniecPaperXi_le_exp_loglog hy hu
    have hprod := mul_le_mul (pow_le_pow_left₀ hL0 hLexp d)
      (pow_le_pow_left₀ hXi0 hXi 2) (sq_nonneg _) (pow_nonneg (Real.exp_pos u).le d)
    have hscaled := mul_le_mul_of_nonneg_right hprod
      (Real.exp_pos (-c * Real.sqrt (Real.log y / iwaniecPaperXi y))).le
    rw [iwaniecPaperXi_root_ratio hy hu0] at hscaled ⊢
    calc
      _ ≤ Real.exp u ^ d * Real.exp u ^ 2 * Real.exp (-c * u ^ (11 / 10 : Real)) := hscaled
      _ = Real.exp (((d : Real) + 2) * u - c * u ^ (11 / 10 : Real)) := by
        rw [← pow_add, ← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        congr 1
        ring

/-- The exact small exponential factor required by source equation (4.2),
not merely its qualitative convergence to zero. -/
theorem eventually_iwaniec_source_four_two :
    ∀ᶠ y : Real in atTop, 1 < y ∧
      200 * iwaniecPaperXi y ^ 2 * Real.exp (-Real.sqrt (Real.log y / iwaniecPaperXi y)) <
        (Real.log y ^ 2)⁻¹ := by
  have hlim := (tendsto_iwaniecXi_log_weighted_error 2 (c := 1) (by norm_num)).const_mul 200
  simp only [neg_one_mul, mul_zero] at hlim
  filter_upwards [eventually_gt_atTop (1 : Real), hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))]
    with y hy hh
  refine ⟨hy, ?_⟩
  rw [← one_div]
  apply (lt_div_iff₀ (sq_pos_of_pos (Real.log_pos hy))).mpr
  nlinarith only [hh]

theorem eventually_iwaniecXi_error_le_inv_log_sq (C : Real) :
    ∀ᶠ y : Real in atTop, 1 < y ∧
      C * iwaniecPaperXi y ^ 2 * Real.exp (-Real.sqrt (Real.log y / iwaniecPaperXi y)) ≤
        (Real.log y ^ 2)⁻¹ := by
  have hlim := (tendsto_iwaniecXi_log_weighted_error 2 (c := 1) (by norm_num)).const_mul C
  simp only [neg_one_mul, mul_zero] at hlim
  filter_upwards [eventually_gt_atTop (1 : Real), hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))]
    with y hy hh
  refine ⟨hy, ?_⟩
  rw [← one_div]
  apply (le_div_iff₀ (sq_pos_of_pos (Real.log_pos hy))).mpr
  nlinarith only [hh]

end

end Erdos1212Kernel
