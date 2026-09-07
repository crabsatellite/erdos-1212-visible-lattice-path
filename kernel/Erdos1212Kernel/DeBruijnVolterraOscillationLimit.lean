import Erdos1212Kernel.DeBruijnVolterraOscillationProduct

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem tendsto_deBruijnVolterraOscillation_odd {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    Tendsto (fun n : Nat => deBruijnVolterraOscillation f (2 * (n : Real) + 1)) atTop (nhds 0) := by
  have h := tendsto_deBruijnVolterraOddProduct.mul_const (deBruijnVolterraOscillation f 1)
  simp only [zero_mul] at h
  exact squeeze_zero (fun n => deBruijnVolterraOscillation_nonneg hf (by
    have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith : 1 ≤ 2 * (n : Real) + 1))
    (deBruijnVolterra_odd_product_bound hf heq) h

/-- The sampled product bound is transported back to every real window
using the proved monotonicity of the actual essential oscillation. -/
theorem tendsto_deBruijnVolterraOscillation {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    Tendsto (deBruijnVolterraOscillation f) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_deBruijnVolterraOscillation_odd hf heq) ε hε
  have hN1 : 1 ≤ 2 * (N : Real) + 1 := by
    have hN0 : 0 ≤ (N : Real) := Nat.cast_nonneg N
    linarith
  refine ⟨2 * (N : Real) + 1, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := hN1.trans hx
  have hDx := deBruijnVolterraOscillation_nonneg hf hx1
  have hDN := deBruijnVolterraOscillation_nonneg hf hN1
  have hsmall : deBruijnVolterraOscillation f (2 * (N : Real) + 1) < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hDN] using hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hDx]
  exact (deBruijnVolterraOscillation_antitoneOn hf heq hN1 hx1 hx).trans_lt hsmall

end

end Erdos1212Kernel
