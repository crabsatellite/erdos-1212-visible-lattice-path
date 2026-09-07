import Erdos1212Kernel.DeBruijnSaddleInverse
import Erdos1212Kernel.DeBruijn1951SaddleDisplay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem deBruijnSaddleMoment_source_density {s : Real} (hs : s ≠ 0) :
    s * deBruijnSaddleMoment s = (s * Real.exp s - Real.exp s + 1) / s := by
  rw [deBruijnSaddleMoment_eq_quot hs]
  field_simp
  <;> ring

/-- The actual eta=(exp(s)-1)/s substitution, not a substituted phase. -/
theorem deBruijnSaddleIntegral_change_variables {u : Real} (hu : 1 < u) :
    (∫ s in (0 : Real)..(deBruijnSaddle u), s * deBruijnSaddleMoment s) =
      ∫ η in (1 : Real)..u, deBruijnSaddle η := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : Real)) (b := deBruijnSaddle u) (g := deBruijnSaddle)
    deBruijnSaddleAverage_continuous.continuousOn
    (fun s _hs => deBruijnSaddleAverage_hasDerivAt s)
    (fun s _hs => (deBruijnSaddleMoment_pos s).le)
  rw [deBruijnSaddleAverage_zero, deBruijnSaddle_average hu] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (deBruijnSaddle_pos hu).le] at hs
  dsimp only [Function.comp_apply]
  rw [deBruijnSaddle_average_inverse hs.1]

/-- Literal de Bruijn 1951 (1.7), including both source endpoints. -/
theorem deBruijn1951_saddle_integral_formula {u : Real} (hu : 1 < u) :
    (∫ s in (0 : Real)..(deBruijnSaddle u), (s * Real.exp s - Real.exp s + 1) / s) =
      ∫ η in (1 : Real)..u, deBruijnSaddle η := by
  rw [← deBruijnSaddleIntegral_change_variables hu]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0 : Real)] with s hs _hmem
  exact (deBruijnSaddleMoment_source_density hs).symm

theorem deBruijn1951SaddleIntegral_eq_inverse_integral {u : Real} (hu : 1 < u) :
    deBruijn1951SaddleIntegral (deBruijnSaddle u) = ∫ η in (1 : Real)..u, deBruijnSaddle η :=
  deBruijn1951_saddle_integral_formula hu

end

end Erdos1212Kernel
