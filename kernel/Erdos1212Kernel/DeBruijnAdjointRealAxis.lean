import Erdos1212Kernel.DeBruijnAdjointDerivative

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnExpQuot_continuousAt {z : Real} (hz : z ≠ 0) : ContinuousAt deBruijnExpQuot z :=
  (Real.continuous_exp.continuousAt.sub continuousAt_const).div continuousAt_id hz

theorem deBruijn1951ExpIntegral_hasDerivAt {z : Real} (hz : z ≠ 0) :
    HasDerivAt deBruijn1951ExpIntegral (deBruijnExpQuot z) z := by
  exact intervalIntegral.integral_hasDerivAt_right (deBruijnExpQuot_intervalIntegrable_zero z)
    deBruijnExpQuot_measurable.stronglyMeasurable.stronglyMeasurableAtFilter (deBruijnExpQuot_continuousAt hz)

theorem deBruijn1951AdjointNumerator_shift (u z : Real) :
    deBruijn1951AdjointNumerator u z = Real.exp z * deBruijn1951AdjointNumerator (u - 1) z := by
  unfold deBruijn1951AdjointNumerator
  rw [← Real.exp_add]
  congr 1
  ring

/-- The literal real-axis derivative used in the source's verification of
the adjoint equation; the parameter shift is retained exactly. -/
theorem deBruijn1951AdjointNumerator_hasDerivAt_real (u : Real) {z : Real} (hz : z ≠ 0) :
    HasDerivAt (deBruijn1951AdjointNumerator (u - 1))
      (u * deBruijn1951AdjointNumerator (u - 1) z - deBruijn1951AdjointDensity u z +
        deBruijn1951AdjointDensity (u - 1) z) z := by
  have h := (((hasDerivAt_id z).const_mul (u - 1 + 1)).sub (deBruijn1951ExpIntegral_hasDerivAt hz)).exp
  apply h.congr_deriv
  simp only [mul_one, sub_add_cancel, Pi.sub_apply, id_eq]
  have hA : Real.exp (u * z - deBruijn1951ExpIntegral z) = deBruijn1951AdjointNumerator (u - 1) z := by
    simp only [deBruijn1951AdjointNumerator, sub_add_cancel]
  rw [hA]
  unfold deBruijn1951AdjointDensity deBruijnExpQuot
  rw [deBruijn1951AdjointNumerator_shift u z]
  field_simp
  <;> ring

theorem tendsto_deBruijn1951AdjointNumerator_atTop (u : Real) :
    Tendsto (deBruijn1951AdjointNumerator u) atTop (nhds 0) := by
  have hs : Tendsto (fun z : Real => (1 / 8 : Real) * z ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : Nat) ≠ 0)).const_mul_atTop (by norm_num)
  have he : Tendsto (fun z : Real => Real.exp (-(1 / 8 : Real) * z ^ 2)) atTop (nhds 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hb := he.const_mul (Real.exp (2 * |u + 1| ^ 2))
  simp only [mul_zero] at hb
  apply squeeze_zero' _ _ hb
  · filter_upwards with z
    exact (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : Real)] with z hz
    exact deBruijn1951AdjointNumerator_gaussian_bound hz le_rfl

theorem tendsto_deBruijn1951_first_moment_exp {a : Real} (ha : 0 < a) :
    Tendsto (fun z : Real => z * Real.exp (-a * z)) atTop (nhds 0) := by
  have hs : Tendsto (fun z : Real => a * z) atTop atTop := tendsto_id.const_mul_atTop ha
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hs).div_const a
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards with z
  dsimp
  rw [pow_one, neg_mul]
  field_simp

theorem tendsto_deBruijn1951AdjointNumerator_reflected {u : Real} (hu : -1 < u) :
    Tendsto (fun z : Real => deBruijn1951AdjointNumerator u (-z)) atTop (nhds 0) := by
  have h := (tendsto_deBruijn1951_first_moment_exp (show 0 < u + 1 by linarith)).mul tendsto_deBruijn1951Phi
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with z hz
  rw [deBruijn1951AdjointNumerator_neg u hz.ne']
  unfold deBruijn1951BoundaryKernel
  ring

theorem tendsto_deBruijn1951AdjointNumerator_atBot {u : Real} (hu : -1 < u) :
    Tendsto (deBruijn1951AdjointNumerator u) atBot (nhds 0) := by
  have h := (tendsto_deBruijn1951AdjointNumerator_reflected hu).comp tendsto_neg_atBot_atTop
  apply h.congr'
  filter_upwards with z
  simp only [Function.comp_apply, neg_neg]

end

end Erdos1212Kernel
