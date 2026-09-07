import Erdos1212Kernel.DeBruijnVolterraThresholdBound

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnVolterra_upper_point_contraction {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x γ : Real} (hx : 1 ≤ x)
    (hgap : γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMean f x) :
    f x ≤ deBruijnVolterraWindowMax f x - (γ / x) * deBruijnVolterraOscillation f x := by
  have hD := deBruijnVolterraOscillation_nonneg hf hx
  by_cases hz : deBruijnVolterraOscillation f x = 0
  · rw [hz, mul_zero, sub_zero]
    exact (deBruijnVolterraWindow_bounds hf hx x ⟨by linarith, le_rfl⟩).2
  · have hp : 0 < deBruijnVolterraOscillation f x := lt_of_le_of_ne hD (Ne.symm hz)
    let q := (deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMean f x) / deBruijnVolterraOscillation f x
    have hb := deBruijnVolterraWindowMean_bounds hf hx
    have hq : q ∈ Set.Icc (0 : Real) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hb.2) hD
      · dsimp [q]
        rw [div_le_iff₀ hp]
        unfold deBruijnVolterraOscillation
        linarith [hb.1]
    have hm : deBruijnVolterraWindowMean f x = q * deBruijnVolterraWindowMin f x +
        (1 - q) * deBruijnVolterraWindowMax f x := by
      dsimp [q]
      field_simp
      <;> unfold deBruijnVolterraOscillation
      <;> ring
    have hpoint := deBruijnVolterra_upper_threshold hf heq hx hq (deBruijnVolterraWindow_bounds hf hx) hm
    have hγq : γ ≤ q := (le_div_iff₀ hp).mpr hgap
    have hprefix : γ / x ≤ deBruijnRhoVolterraPrefix x q :=
      (div_le_div_of_nonneg_right hγq (by linarith : 0 ≤ x)).trans (deBruijnRhoVolterraPrefix_lower hx hq)
    have hmul := mul_le_mul_of_nonneg_right hprefix hD
    change f x ≤ deBruijnVolterraWindowMax f x - deBruijnVolterraOscillation f x * deBruijnRhoVolterraPrefix x q at hpoint
    nlinarith

theorem deBruijnVolterra_lower_point_contraction {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x γ : Real} (hx : 1 ≤ x)
    (hgap : γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMin f x) :
    deBruijnVolterraWindowMin f x + (γ / x) * deBruijnVolterraOscillation f x ≤ f x := by
  have hD := deBruijnVolterraOscillation_nonneg hf hx
  by_cases hz : deBruijnVolterraOscillation f x = 0
  · rw [hz, mul_zero, add_zero]
    exact (deBruijnVolterraWindow_bounds hf hx x ⟨by linarith, le_rfl⟩).1
  · have hp : 0 < deBruijnVolterraOscillation f x := lt_of_le_of_ne hD (Ne.symm hz)
    let q := (deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMin f x) / deBruijnVolterraOscillation f x
    have hb := deBruijnVolterraWindowMean_bounds hf hx
    have hq : q ∈ Set.Icc (0 : Real) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hb.1) hD
      · dsimp [q]
        rw [div_le_iff₀ hp]
        unfold deBruijnVolterraOscillation
        linarith [hb.2]
    have hm : deBruijnVolterraWindowMean f x = (1 - q) * deBruijnVolterraWindowMin f x +
        q * deBruijnVolterraWindowMax f x := by
      dsimp [q]
      field_simp
      <;> unfold deBruijnVolterraOscillation
      <;> ring
    have hpoint := deBruijnVolterra_lower_threshold hf heq hx hq (deBruijnVolterraWindow_bounds hf hx) hm
    have hγq : γ ≤ q := (le_div_iff₀ hp).mpr hgap
    have hprefix : γ / x ≤ deBruijnRhoVolterraPrefix x q :=
      (div_le_div_of_nonneg_right hγq (by linarith : 0 ≤ x)).trans (deBruijnRhoVolterraPrefix_lower hx hq)
    have hmul := mul_le_mul_of_nonneg_right hprefix hD
    change deBruijnVolterraWindowMin f x + deBruijnVolterraOscillation f x * deBruijnRhoVolterraPrefix x q ≤ f x at hpoint
    nlinarith

end

end Erdos1212Kernel
