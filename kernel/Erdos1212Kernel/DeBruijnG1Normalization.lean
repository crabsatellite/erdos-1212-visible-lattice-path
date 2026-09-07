import Erdos1212Kernel.DeBruijnG1LaplaceDensity
import Erdos1212Kernel.DeBruijnG1HeightBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnG1Normalizer (u b : Real) : Real :=
  deBruijnSaddleHeight u * deBruijnSaddle u * Real.sqrt (deBruijnSaddleCurvature u) * Real.exp (-b * deBruijnSaddle u)

theorem deBruijnG1Normalizer_pos {u : Real} (hu : 1 < u) (b : Real) : 0 < deBruijnG1Normalizer u b := by
  have hH := deBruijnSaddleHeight_pos u
  have hξ := deBruijnSaddle_pos hu
  have hC := deBruijnSaddleCurvature_pos u
  unfold deBruijnG1Normalizer
  positivity

theorem deBruijnG1LaplaceDensity_normalized (u b x : Real) :
    (deBruijnSaddleHeight u * deBruijnSaddle u * Real.exp (-b * deBruijnSaddle u)) * deBruijnG1LaplaceDensity u b x =
      Real.exp (-(deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u))) *
        Real.exp (b * (x - deBruijnSaddle u)) * deBruijnSaddle u / x := by
  have he : deBruijnSaddleHeight u * Real.exp (-b * deBruijnSaddle u) * Real.exp (-deBruijnRealSaddlePhase u x) * Real.exp (b * x) =
      Real.exp (-(deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u))) * Real.exp (b * (x - deBruijnSaddle u)) := by
    rw [deBruijnSaddleHeight_eq_phase]
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (deBruijnSaddleHeight u * Real.exp (-b * deBruijnSaddle u) * Real.exp (-deBruijnRealSaddlePhase u x) * Real.exp (b * x)) *
        deBruijnSaddle u / x := by unfold deBruijnG1LaplaceDensity; ring
    _ = _ := by rw [he]

theorem deBruijnG1Normalizer_upper {u b : Real} (hu : 1 < u) (hb : 0 ≤ b) :
    deBruijnG1Normalizer u b ≤ 2 * u ^ 2 * deBruijnSaddleHeight u := by
  have hH := deBruijnSaddleHeight_pos u
  have hξ := deBruijnSaddle_pos hu
  have hs := Real.sqrt_nonneg (deBruijnSaddleCurvature u)
  have he : Real.exp (-b * deBruijnSaddle u) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) hξ.le)
  have hprod : deBruijnSaddle u * Real.sqrt (deBruijnSaddleCurvature u) ≤ 2 * u ^ 2 := by
    have h := mul_le_mul (deBruijnSaddle_le_two_mul hu) (deBruijnSaddle_sqrt_le_parameter hu) hs (show 0 ≤ 2 * u by linarith)
    nlinarith
  calc
    _ = (deBruijnSaddleHeight u * (deBruijnSaddle u * Real.sqrt (deBruijnSaddleCurvature u))) * Real.exp (-b * deBruijnSaddle u) := by
      unfold deBruijnG1Normalizer
      ring
    _ ≤ deBruijnSaddleHeight u * (deBruijnSaddle u * Real.sqrt (deBruijnSaddleCurvature u)) :=
      mul_le_of_le_one_right (mul_nonneg hH.le (mul_nonneg hξ.le hs)) he
    _ ≤ deBruijnSaddleHeight u * (2 * u ^ 2) := mul_le_mul_of_nonneg_left hprod hH.le
    _ = _ := by ring

def deBruijnG1RegularPart (u b : Real) : Real :=
  deBruijn1951NearIntegral (u - 1 + b) - deBruijn1951NegativeTail (u - 1 + b)

theorem deBruijnG1_laplace_decomposition {u b : Real} (hu : 1 < u) (hb : 0 ≤ b) :
    deBruijn1951G1 (u - 1 + b) = (∫ x in Set.Ioi (1 : Real), deBruijnG1LaplaceDensity u b x) + deBruijnG1RegularPart u b := by
  rw [deBruijn1951G1_eq_regularized (by linarith : -1 < u - 1 + b)]
  have hi : deBruijn1951PositiveTail (u - 1 + b) = ∫ x in Set.Ioi (1 : Real), deBruijnG1LaplaceDensity u b x := by
    unfold deBruijn1951PositiveTail
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    exact deBruijnG1LaplaceDensity_source u b x
  unfold deBruijn1951RegularizedAdjoint deBruijnG1RegularPart
  rw [hi]
  ring

end

end Erdos1212Kernel
