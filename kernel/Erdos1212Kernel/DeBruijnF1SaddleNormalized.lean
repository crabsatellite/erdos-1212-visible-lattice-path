import Erdos1212Kernel.DeBruijnF1VerticalLimit
import Erdos1212Kernel.DeBruijnF1TailLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1GaussianCoefficient : Real := Real.sqrt (2 * Real.pi) / (2 * Real.pi)

theorem deBruijnF1GaussianCoefficient_pos : 0 < deBruijnF1GaussianCoefficient := by
  unfold deBruijnF1GaussianCoefficient
  positivity

theorem tendsto_deBruijnF1Complex_normalized :
    Tendsto (fun u : Real => (Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1Complex (u : Complex) /
      (deBruijnSaddleHeight u : Complex)) atTop (nhds (deBruijnF1GaussianCoefficient : Complex)) := by
  have h := ((tendsto_deBruijnF1SaddleLower_normalized.neg.add tendsto_deBruijnF1SaddleVertical_normalized).add
    tendsto_deBruijnF1SaddleUpper_normalized).const_mul (1 / (2 * (Real.pi : Complex) * Complex.I))
  simp only [neg_zero, zero_add, add_zero] at h
  have hπ : (Real.pi : Complex) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : (1 / (2 * (Real.pi : Complex) * Complex.I)) * (Complex.I * (Real.sqrt (2 * Real.pi) : Complex)) =
      (deBruijnF1GaussianCoefficient : Complex) := by
    unfold deBruijnF1GaussianCoefficient
    push_cast
    field_simp [hπ, Complex.I_ne_zero]
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  rw [deBruijnF1_saddle_pieces hu]
  ring

def deBruijnF1Normalized (u : Real) : Real :=
  Real.sqrt (deBruijnSaddleCurvature u) * deBruijnF1 u / deBruijnSaddleHeight u

theorem tendsto_deBruijnF1Normalized :
    Tendsto deBruijnF1Normalized atTop (nhds deBruijnF1GaussianCoefficient) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp tendsto_deBruijnF1Complex_normalized
  simp only [Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards with u
  change (((Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1Complex (u : Complex) /
    (deBruijnSaddleHeight u : Complex)).re) = Real.sqrt (deBruijnSaddleCurvature u) * deBruijnF1 u / deBruijnSaddleHeight u
  rw [← deBruijnF1_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]

end

end Erdos1212Kernel
