import Erdos1212Kernel.DeBruijnG1HeightBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The literal exponent integral displayed in de Bruijn 1951 (1.6). -/
def deBruijn1951SaddleIntegral (x : Real) : Real :=
  ∫ s in (0 : Real)..x, (s * Real.exp s - Real.exp s + 1) / s

theorem deBruijn1951SaddleIntegral_eq (x : Real) :
    deBruijn1951SaddleIntegral x = Real.exp x - 1 - deBruijn1951ExpIntegral x := by
  calc
    _ = ∫ s in (0 : Real)..x, Real.exp s - deBruijnSaddleAverage s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (0 : Real)] with s hs _hmem
      rw [deBruijnSaddleAverage_eq_quot hs]
      field_simp <;> ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 x)
        (deBruijnSaddleAverage_continuous.intervalIntegrable 0 x), integral_exp,
        Real.exp_zero, ← deBruijnExpIntegral_eq_average_integral]

theorem deBruijn1951SaddleIntegral_saddle {u : Real} (hu : 1 < u) :
    deBruijn1951SaddleIntegral (deBruijnSaddle u) = u * deBruijnSaddle u - deBruijn1951ExpIntegral (deBruijnSaddle u) := by
  rw [deBruijn1951SaddleIntegral_eq, deBruijnSaddle_equation hu]

theorem deBruijn1951SaddleIntegral_height {u : Real} (hu : 1 < u) :
    Real.exp (-deBruijn1951SaddleIntegral (deBruijnSaddle u)) = deBruijnSaddleHeight u := by
  rw [deBruijn1951SaddleIntegral_saddle hu]
  unfold deBruijnSaddleHeight
  congr 1
  ring

end

end Erdos1212Kernel
