import Erdos1212Kernel.DeBruijnG1KernelMajorant
import Erdos1212Kernel.DeBruijnF1ScaledDensity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnG1CentralDensity (u b v : Real) : Real :=
  (Set.Ioi (-Real.sqrt (deBruijnSaddleCurvature u))).indicator (deBruijnG1ScaledKernel u b) v

theorem deBruijnG1CentralDensity_measurable (u b : Real) : Measurable (deBruijnG1CentralDensity u b) :=
  (deBruijnG1ScaledKernel_measurable u b).indicator measurableSet_Ioi

theorem eventually_deBruijnG1CentralDensity_bound {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    ∀ᶠ u : Real in atTop, ∀ v : Real, |deBruijnG1CentralDensity u b v| ≤ deBruijnG1GaussianMajorant v := by
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_deBruijnSaddle.eventually_ge_atTop 2,
    tendsto_deBruijnSaddle_sqrt_curvature.eventually_ge_atTop 1] with u hu hξ hs
  intro v
  by_cases hv : v ∈ Set.Ioi (-Real.sqrt (deBruijnSaddleCurvature u))
  · rw [deBruijnG1CentralDensity, Set.indicator_of_mem hv]
    exact deBruijnG1ScaledKernel_bound hu hξ hs hb hv.le
  · rw [deBruijnG1CentralDensity, Set.indicator_of_notMem hv, abs_zero]
    unfold deBruijnG1GaussianMajorant
    positivity

theorem tendsto_deBruijnG1CentralDensity (b v : Real) :
    Tendsto (fun u : Real => deBruijnG1CentralDensity u b v) atTop (nhds (Real.exp (-v ^ 2 / 2))) := by
  apply (tendsto_deBruijnG1ScaledKernel b v).congr'
  filter_upwards [tendsto_deBruijnSaddle_sqrt_curvature.eventually_gt_atTop (-v)] with u hu
  have hv : v ∈ Set.Ioi (-Real.sqrt (deBruijnSaddleCurvature u)) := by change -Real.sqrt (deBruijnSaddleCurvature u) < v; linarith
  rw [deBruijnG1CentralDensity, Set.indicator_of_mem hv]

theorem tendsto_deBruijnG1CentralDensity_integral {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Tendsto (fun u : Real => ∫ v : Real, deBruijnG1CentralDensity u b v) atTop (nhds (Real.sqrt (2 * Real.pi))) := by
  have hbound : ∀ᶠ u : Real in atTop, ∀ᵐ v : Real, ‖deBruijnG1CentralDensity u b v‖ ≤ deBruijnG1GaussianMajorant v := by
    filter_upwards [eventually_deBruijnG1CentralDensity_bound hb] with u hu
    filter_upwards with v
    simpa only [Real.norm_eq_abs] using hu v
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence deBruijnG1GaussianMajorant
    (Filter.Eventually.of_forall (fun u : Real => (deBruijnG1CentralDensity_measurable u b).aestronglyMeasurable))
    hbound deBruijnG1GaussianMajorant_integrable (Filter.Eventually.of_forall (fun v => tendsto_deBruijnG1CentralDensity b v))
  rw [deBruijn_real_gaussian_integral] at h
  exact h

end

end Erdos1212Kernel
