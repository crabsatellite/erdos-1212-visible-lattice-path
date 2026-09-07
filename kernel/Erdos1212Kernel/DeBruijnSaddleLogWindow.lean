import Erdos1212Kernel.DeBruijnSaddleLogIdentity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem tendsto_deBruijn_log_power_div (n : Nat) :
    Tendsto (fun u : Real => (Real.log u) ^ n / u) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with u hu
  simp only [Function.comp_apply, Real.exp_neg, Real.exp_log hu, div_eq_mul_inv]

theorem eventually_deBruijn_log_square_le : ∀ᶠ u : Real in atTop, (Real.log u) ^ 2 ≤ u := by
  have h := (tendsto_deBruijn_log_power_div 2).eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [h, eventually_gt_atTop (0 : Real)] with u hu hu0
  have hmul := (div_lt_iff₀ hu0).mp hu
  simpa only [one_mul] using hmul.le

theorem deBruijnSaddle_log_upper {u : Real} (hu : 1 < u) (hL : 4 ≤ Real.log u)
    (hU : (Real.log u) ^ 2 ≤ u) : deBruijnSaddle u ≤ 2 * Real.log u := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < Real.log u := by linarith
  have h4 : 4 * Real.log u ≤ u := by nlinarith
  have he : Real.exp (2 * Real.log u) = u ^ 2 := by
    rw [show 2 * Real.log u = Real.log u + Real.log u by ring, Real.exp_add, Real.exp_log hu0]
    ring
  apply deBruijnSaddleAverage_strictMono.le_iff_le.mp
  rw [deBruijnSaddle_average hu, deBruijnSaddleAverage_eq_quot (show 2 * Real.log u ≠ 0 by positivity), he]
  apply (le_div_iff₀ (show 0 < 2 * Real.log u by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_left h4 hu0.le
  nlinarith

theorem deBruijnSaddle_log_width {u : Real} (hu : 1 < u) (hL : 4 ≤ Real.log u)
    (hU : (Real.log u) ^ 2 ≤ u) :
    0 ≤ deBruijnSaddle u - Real.log u ∧ deBruijnSaddle u - Real.log u ≤ Real.log (Real.log u) + 2 := by
  have hL0 : 0 < Real.log u := by linarith
  have hξ := deBruijnSaddle_pos hu
  have hxiL := deBruijnSaddle_log_lower hu
  have hlog := Real.log_le_log hξ (deBruijnSaddle_log_upper hu hL hU)
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hL0.ne'] at hlog
  have hlogTwo : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2); linarith
  have hδ := deBruijnSaddleLogCorrection_le_inverse hu (by linarith : 1 ≤ deBruijnSaddle u)
  have hi : 1 / u ≤ 1 := (div_le_iff₀ (show 0 < u by linarith)).mpr (by linarith)
  have hid := deBruijnSaddle_log_split hu
  exact ⟨by linarith, by linarith⟩

theorem deBruijnSaddle_log_two_term_lower {u : Real} (hu : 1 < u) (hL : 0 < Real.log u) :
    0 ≤ deBruijnSaddle u - Real.log u - Real.log (Real.log u) := by
  have hlog := Real.log_le_log hL (deBruijnSaddle_log_lower hu).le
  have hδ := (deBruijnSaddleLogCorrection_bounds hu).1
  linarith [deBruijnSaddle_log_split hu]

theorem deBruijnSaddle_log_increment_identity {u : Real} (hu : 1 < u) (hL : 0 < Real.log u) :
    Real.log (deBruijnSaddle u) = Real.log (Real.log u) +
      Real.log (1 + (deBruijnSaddle u - Real.log u) / Real.log u) := by
  have harg : deBruijnSaddle u = Real.log u * (1 + (deBruijnSaddle u - Real.log u) / Real.log u) := by
    field_simp
    <;> ring
  have ht : 0 ≤ (deBruijnSaddle u - Real.log u) / Real.log u :=
    div_nonneg (sub_nonneg.mpr (deBruijnSaddle_log_lower hu).le) hL.le
  calc
    _ = Real.log (Real.log u * (1 + (deBruijnSaddle u - Real.log u) / Real.log u)) := by rw [← harg]
    _ = _ := Real.log_mul hL.ne' (by positivity)

end

end Erdos1212Kernel
