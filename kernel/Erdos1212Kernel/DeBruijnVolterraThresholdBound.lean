import Erdos1212Kernel.DeBruijnVolterraThresholdIntegrals

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- Source Lemma 2, with its threshold set E chosen as [0,q] for the
proved monotone rho kernel. Both of the paper's signed gap inequalities
are used before their unweighted terms cancel. -/
theorem deBruijnVolterra_upper_threshold {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x m M q : Real} (hx : 1 ≤ x) (hq : q ∈ Set.Icc (0 : Real) 1)
    (hbound : ∀ y ∈ Set.Icc (x - 1) x, m ≤ f y ∧ f y ≤ M)
    (hmean : deBruijnVolterraWindowMean f x = q * m + (1 - q) * M) :
    f x ≤ M - (M - m) * deBruijnRhoVolterraPrefix x q := by
  let p := deBruijnRhoVolterraKernel x q
  have hzero : (0 : Real) ∈ Set.Icc 0 1 := by norm_num
  have hone : (1 : Real) ∈ Set.Icc 0 1 := by norm_num
  have hK := deBruijnRhoVolterraKernel_continuousOn hx
  have hF := deBruijnRhoVolterra_lag_continuousOn hf hx
  have hK0 := deBruijnVolterra_subinterval_integrable hK hzero hq
  have hK1 := deBruijnVolterra_subinterval_integrable hK hq hone
  have hF0 := deBruijnVolterra_subinterval_integrable hF hzero hq
  have hF1 := deBruijnVolterra_subinterval_integrable hF hq hone
  have hKF0 := deBruijnVolterra_subinterval_integrable (hK.mul hF) hzero hq
  have hKF1 := deBruijnVolterra_subinterval_integrable (hK.mul hF) hq hone
  have hlow := intervalIntegral.integral_mono_on hq.1
    (deBruijnVolterra_subinterval_integrable (continuousOn_const.mul (continuousOn_const.sub hF)) hzero hq)
    (deBruijnVolterra_subinterval_integrable (hK.mul (continuousOn_const.sub hF)) hzero hq)
    (show ∀ t ∈ Set.Icc (0 : Real) q,
      p * (m - f (x - t)) ≤ deBruijnRhoVolterraKernel x t * (m - f (x - t)) from by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 := ⟨ht.1, ht.2.trans hq.2⟩
      have hft := (hbound (x - t) ⟨by linarith [ht'.2], by linarith [ht'.1]⟩).1
      exact mul_le_mul_of_nonpos_right (deBruijnRhoVolterraKernel_monotoneOn hx ht' hq ht.2) (sub_nonpos.mpr hft))
  have hhigh := intervalIntegral.integral_mono_on hq.2
    (deBruijnVolterra_subinterval_integrable (continuousOn_const.mul (continuousOn_const.sub hF)) hq hone)
    (deBruijnVolterra_subinterval_integrable (hK.mul (continuousOn_const.sub hF)) hq hone)
    (show ∀ t ∈ Set.Icc q (1 : Real),
      p * (M - f (x - t)) ≤ deBruijnRhoVolterraKernel x t * (M - f (x - t)) from by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 := ⟨hq.1.trans ht.1, ht.2⟩
      have hft := (hbound (x - t) ⟨by linarith [ht'.2], by linarith [ht'.1]⟩).2
      exact mul_le_mul_of_nonneg_right (deBruijnRhoVolterraKernel_monotoneOn hx hq ht' ht.1) (sub_nonneg.mpr hft))
  simp only [Pi.mul_apply, Pi.sub_apply] at hlow hhigh
  rw [intervalIntegral.integral_const_mul, deBruijnVolterra_plain_gap_integral hf hx hzero hq m,
    deBruijnVolterra_weighted_gap_integral hf hx hzero hq m] at hlow
  rw [intervalIntegral.integral_const_mul, deBruijnVolterra_plain_gap_integral hf hx hq hone M,
    deBruijnVolterra_weighted_gap_integral hf hx hq hone M] at hhigh
  simp only [sub_zero] at hlow
  have hsK := intervalIntegral.integral_add_adjacent_intervals hK0 hK1
  rw [deBruijnRhoVolterraKernel_integral hx] at hsK
  have hsF := intervalIntegral.integral_add_adjacent_intervals hF0 hF1
  rw [deBruijnVolterraWindowMean_lag] at hsF
  have hsKF := intervalIntegral.integral_add_adjacent_intervals hKF0 hKF1
  simp only [Pi.mul_apply] at hsKF
  rw [← heq x hx] at hsKF
  have htK : (∫ t in q..1, deBruijnRhoVolterraKernel x t) =
      1 - ∫ t in (0 : Real)..q, deBruijnRhoVolterraKernel x t := by linarith
  have htF : (∫ t in q..1, f (x - t)) =
      deBruijnVolterraWindowMean f x - ∫ t in (0 : Real)..q, f (x - t) := by linarith
  have htKF : (∫ t in q..1, deBruijnRhoVolterraKernel x t * f (x - t)) =
      f x - ∫ t in (0 : Real)..q, deBruijnRhoVolterraKernel x t * f (x - t) := by linarith
  rw [htK, htF, htKF, hmean] at hhigh
  have hsum := add_le_add hlow hhigh
  unfold deBruijnRhoVolterraPrefix
  nlinarith [hsum]

theorem deBruijnVolterra_lower_threshold {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x m M q : Real} (hx : 1 ≤ x) (hq : q ∈ Set.Icc (0 : Real) 1)
    (hbound : ∀ y ∈ Set.Icc (x - 1) x, m ≤ f y ∧ f y ≤ M)
    (hmean : deBruijnVolterraWindowMean f x = (1 - q) * m + q * M) :
    m + (M - m) * deBruijnRhoVolterraPrefix x q ≤ f x := by
  have hb : ∀ y ∈ Set.Icc (x - 1) x, -M ≤ -f y ∧ -f y ≤ -m := by
    intro y hy
    exact ⟨neg_le_neg (hbound y hy).2, neg_le_neg (hbound y hy).1⟩
  have hm : deBruijnVolterraWindowMean (fun y : Real => -f y) x = q * (-M) + (1 - q) * (-m) := by
    change (∫ y in (x - 1)..x, -f y) = _
    rw [intervalIntegral.integral_neg]
    change -deBruijnVolterraWindowMean f x = _
    rw [hmean]
    ring
  have h := deBruijnVolterra_upper_threshold (f := fun y : Real => -f y) hf.neg heq.neg hx hq hb hm
  dsimp only at h
  nlinarith

end

end Erdos1212Kernel
