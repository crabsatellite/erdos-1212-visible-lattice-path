import Erdos1212Kernel.AlgebraicCorridorRoughCompositeCount
import Erdos1212Kernel.AlgebraicCorridorSupportScale
import Erdos1212Kernel.AlgebraicCorridorCrossingAlgebraic

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

theorem eventually_band_lt_z :
    ∀ᶠ N : ℝ in atTop, (band N : ℝ) < z N := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell 3000 2,
    ell_tendsto.eventually_gt_atTop (10002 : ℝ)] with N hdom hscale hellLarge
  have hNPos : 0 < N := zero_lt_one.trans hdom.1
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hLPos : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hu : 0 < u N := by unfold u; positivity
  have hband : (band N : ℝ) ≤ 10000 * ell N ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 10000 * ell N ^ 2)).le
  have hbandCube : (band N : ℝ) < ell N ^ 3 := by
    nlinarith [sq_nonneg (ell N - 1)]
  have hexponent : 3 * L N < ell N / u N := by
    unfold u
    apply (lt_div_iff₀ (by positivity : 0 < 1000 * L N)).mpr
    nlinarith
  have hzExp : z N = Real.exp (ell N / u N) := by
    rw [← log_z hNPos hu, Real.exp_log (z_pos hNPos hu)]
  have hellCube : ell N ^ 3 = Real.exp (3 * L N) := by
    calc
      ell N ^ 3 = Real.exp (L N) ^ 3 := by
        rw [exp_L hellPos]
      _ = Real.exp ((3 : ℝ) * L N) :=
        (Real.exp_nat_mul (L N) 3).symm
  rw [hellCube] at hbandCube
  rw [hzExp]
  exact hbandCube.trans (Real.exp_lt_exp.mpr hexponent)

theorem eventually_two_z_lt_floor_half :
    ∀ᶠ N : ℝ in atTop, 2 * z N < (Nat.floor (N / 2) : ℝ) := by
  filter_upwards [eventually_large_domain,
    eventually_ge_atTop (64 : ℝ)] with N hdom hN64
  have hN : 1 ≤ N := hdom.1.le
  have hu : 0 < u N := by unfold u; nlinarith [hdom.2.2]
  have hexponent : 1 / u N ≤ (1 / 2 : ℝ) := by
    unfold u
    rw [div_le_iff₀ (mul_pos (by norm_num)
      (zero_lt_one.trans_le hdom.2.2))]
    nlinarith [hdom.2.2]
  have hzsqrt : z N ≤ Real.sqrt N := by
    unfold z
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN hexponent
  have hsqrt : Real.sqrt N ≤ N / 8 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg (N - 64)]
  have hmargin : 2 * z N + 1 ≤ N / 2 := by
    nlinarith
  have hfloor := Nat.lt_floor_add_one (N / 2)
  exact lt_of_lt_of_le (by linarith : 2 * z N < N / 2 - 1)
    (by linarith : N / 2 - 1 ≤ (Nat.floor (N / 2) : ℝ))

theorem eventually_band_two :
    ∀ᶠ N : ℝ in atTop, 2 ≤ band N := by
  filter_upwards [eventually_large_domain] with N hdom
  have hceil : 10000 * ell N ^ 2 ≤ (band N : ℝ) := Nat.le_ceil _
  have hellPos : 0 < ell N := zero_lt_one.trans_le hdom.2.1
  have hreal : (2 : ℝ) ≤ band N := by nlinarith [sq_pos_of_pos hellPos]
  exact_mod_cast hreal

end

end Erdos1212Kernel.CorridorScale
