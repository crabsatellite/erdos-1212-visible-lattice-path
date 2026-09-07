import Erdos1212Kernel.DeBruijnG1CentralTransport
import Erdos1212Kernel.DeBruijnG1LeftTailLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

theorem deBruijnG1_saddle_decomposition {u b : Real} (hu : 1 < u)
    (hξ : 2 ≤ deBruijnSaddle u) (hb : 0 ≤ b) :
    deBruijn1951G1 (u - 1 + b) = deBruijnG1LeftTail u b +
      (∫ x in Set.Ioi (deBruijnSaddle u - 1), deBruijnG1LaplaceDensity u b x) + deBruijnG1RegularPart u b := by
  rw [deBruijnG1_laplace_decomposition hu hb]
  have h := intervalIntegral.integral_interval_add_Ioi
    (deBruijnG1LaplaceDensity_integrable u b (by norm_num : (0 : Real) < 1))
    (deBruijnG1LaplaceDensity_integrable u b (by linarith : 0 < deBruijnSaddle u - 1))
  rw [← h]
  rfl

/-- Both original G1 integrals, with their original common saddle, including
the principal-value remainder and the whole left tail. -/
theorem tendsto_deBruijnG1_normalized {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Tendsto (fun u : Real => deBruijnG1Normalizer u b * deBruijn1951G1 (u - 1 + b))
      atTop (nhds (Real.sqrt (2 * Real.pi))) := by
  have h := ((tendsto_deBruijnG1_normalized_left hb.1).add (tendsto_deBruijnG1_central_integral hb)).add
    (tendsto_deBruijnG1_normalized_regular hb)
  simp only [zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_deBruijnSaddle.eventually_ge_atTop 2] with u hu hξ
  rw [deBruijnG1_saddle_decomposition hu hξ hb.1]
  ring

end

end Erdos1212Kernel
