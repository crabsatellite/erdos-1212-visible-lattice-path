import Erdos1212Kernel.DeBruijnG1CentralDensity
import Erdos1212Kernel.DeBruijnG1Normalization

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn_integral_translate_Ioi (f : Real → Real) (a c : Real) :
    (∫ x in Set.Ioi a, f (c + x)) = ∫ y in Set.Ioi (c + a), f y := by
  have hm : MeasurableEmbedding (fun x : Real => c + x) := (Homeomorph.addLeft c).isClosedEmbedding.measurableEmbedding
  have h := hm.setIntegral_map (μ := volume) f (Set.Ioi (c + a))
  rw [map_add_left_eq_self] at h
  have hp : (fun x : Real => c + x) ⁻¹' Set.Ioi (c + a) = Set.Ioi a := by ext x; simp
  rw [hp] at h
  exact h.symm

theorem deBruijn_integral_saddle_rescale (f : Real → Real) (ξ : Real) {s : Real} (hs : 0 < s) :
    (∫ v in Set.Ioi (-s), f (ξ + v / s)) = s * ∫ x in Set.Ioi (ξ - 1), f x := by
  have h := integral_comp_mul_left_Ioi (fun x : Real => f (ξ + x)) (-s) (inv_pos.mpr hs)
  have he : s⁻¹ * (-s) = (-1 : Real) := by field_simp
  rw [he, inv_inv, smul_eq_mul, deBruijn_integral_translate_Ioi] at h
  simpa only [div_eq_inv_mul, sub_eq_add_neg] using h

theorem deBruijnG1ScaledKernel_density_identity (u b v : Real) :
    deBruijnG1ScaledKernel u b v = (deBruijnSaddleHeight u * deBruijnSaddle u * Real.exp (-b * deBruijnSaddle u)) *
      deBruijnG1LaplaceDensity u b (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) := by
  have h := deBruijnG1LaplaceDensity_normalized u b (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u))
  rw [show deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u) - deBruijnSaddle u =
    v / Real.sqrt (deBruijnSaddleCurvature u) by ring] at h
  exact h.symm

theorem deBruijnG1CentralDensity_integral_rescale (u b : Real) :
    (∫ v : Real, deBruijnG1CentralDensity u b v) = deBruijnG1Normalizer u b *
      ∫ x in Set.Ioi (deBruijnSaddle u - 1), deBruijnG1LaplaceDensity u b x := by
  unfold deBruijnG1CentralDensity
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  calc
    _ = ∫ v in Set.Ioi (-Real.sqrt (deBruijnSaddleCurvature u)),
        (deBruijnSaddleHeight u * deBruijnSaddle u * Real.exp (-b * deBruijnSaddle u)) *
          deBruijnG1LaplaceDensity u b (deBruijnSaddle u + v / Real.sqrt (deBruijnSaddleCurvature u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _hv
      exact deBruijnG1ScaledKernel_density_identity u b v
    _ = (deBruijnSaddleHeight u * deBruijnSaddle u * Real.exp (-b * deBruijnSaddle u)) *
        (Real.sqrt (deBruijnSaddleCurvature u) * ∫ x in Set.Ioi (deBruijnSaddle u - 1), deBruijnG1LaplaceDensity u b x) := by
      rw [MeasureTheory.integral_const_mul, deBruijn_integral_saddle_rescale _ _ (Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u))]
    _ = _ := by unfold deBruijnG1Normalizer; ring

theorem tendsto_deBruijnG1_central_integral {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Tendsto (fun u : Real => deBruijnG1Normalizer u b *
      ∫ x in Set.Ioi (deBruijnSaddle u - 1), deBruijnG1LaplaceDensity u b x) atTop (nhds (Real.sqrt (2 * Real.pi))) := by
  apply (tendsto_deBruijnG1CentralDensity_integral hb).congr'
  filter_upwards with u
  exact deBruijnG1CentralDensity_integral_rescale u b

end

end Erdos1212Kernel
