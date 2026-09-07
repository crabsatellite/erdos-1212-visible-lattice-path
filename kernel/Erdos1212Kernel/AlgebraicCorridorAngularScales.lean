import Erdos1212Kernel.AlgebraicCorridorScales

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

theorem decay_exponent_tendsto :
    Tendsto (fun N : ℝ => ell N / (20000 * L N)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell (C * 20000) 1] with N hdom hbound
  have hL : 0 < L N := zero_lt_one.trans_le hdom.2.2
  apply (le_div_iff₀ (mul_pos (by norm_num) hL)).mpr
  simpa only [pow_one, mul_assoc] using hbound.le

theorem rho_tendsto_zero : Tendsto rho atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp decay_exponent_tendsto)
  change Tendsto (fun N : ℝ => Real.exp (-ell N / (20000 * L N))) atTop (nhds 0)
  simpa only [Function.comp_def, neg_div] using h

/-- The exact root-distance scale comparison at the end of Lemma 6.1. -/
theorem eventually_root_error_le_rho_sq :
    ∀ᶠ N : ℝ in atTop, N ^ ((-1 : ℝ) / (2 * (degree N : ℝ))) ≤ rho N ^ 2 := by
  filter_upwards [eventually_large_domain] with N hdom
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hL : 0 < L N := zero_lt_one.trans_le hdom.2.2
  have hd : 0 < (degree N : ℝ) := by
    exact_mod_cast (show 0 < degree N from (degree_bounds hdom.2.2).1)
  have hden : 2 * (degree N : ℝ) ≤ 10000 * L N := by
    linarith [(degree_bounds hdom.2.2).2]
  have hcompare : ell N / (10000 * L N) ≤ ell N / (2 * (degree N : ℝ)) :=
    div_le_div_of_nonneg_left (zero_le_one.trans hdom.2.1)
      (mul_pos (by norm_num) hd) hden
  rw [Real.rpow_def_of_pos hN, rho, pow_two, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change ell N * ((-1 : ℝ) / (2 * (degree N : ℝ))) ≤
    -ell N / (20000 * L N) + -ell N / (20000 * L N)
  convert neg_le_neg hcompare using 1 <;> field_simp [hL.ne', hd.ne'] <;> ring

end

end Erdos1212Kernel.CorridorScale
