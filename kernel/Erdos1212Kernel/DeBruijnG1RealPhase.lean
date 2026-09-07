import Erdos1212Kernel.DeBruijnSaddleLocalGaussian
import Erdos1212Kernel.DeBruijnF1SaddlePieces

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnRealSaddlePhase (u x : Real) : Real := -u * x + deBruijn1951ExpIntegral x

theorem deBruijnExpIntegral_hasDerivAt_average (x : Real) :
    HasDerivAt deBruijn1951ExpIntegral (deBruijnSaddleAverage x) x := by
  have h := (deBruijnComplexExpIntegral_hasDerivAt (x : Complex)).real_of_complex
  simpa only [deBruijnComplexExpIntegral_ofReal, ← deBruijnSaddleAverage_ofReal, Complex.ofReal_re] using h

theorem deBruijnRealSaddlePhase_hasDerivAt (u x : Real) :
    HasDerivAt (deBruijnRealSaddlePhase u) (deBruijnSaddleAverage x - u) x := by
  have h := ((hasDerivAt_id x).const_mul (-u)).add (deBruijnExpIntegral_hasDerivAt_average x)
  apply h.congr_deriv
  simp only [mul_one]
  ring

theorem deBruijnRealSaddlePhase_continuous (u : Real) : Continuous (deBruijnRealSaddlePhase u) :=
  continuous_iff_continuousAt.mpr (fun x => (deBruijnRealSaddlePhase_hasDerivAt u x).continuousAt)

theorem deBruijnRealSaddlePhase_complex (u x : Real) :
    (deBruijnRealSaddlePhase u x : Complex) = deBruijnSaddlePhase u (x : Complex) := by
  rw [deBruijnSaddlePhase_ofReal]
  rfl

theorem deBruijnSaddleHeight_eq_phase (u : Real) :
    deBruijnSaddleHeight u = Real.exp (deBruijnRealSaddlePhase u (deBruijnSaddle u)) := rfl

def deBruijnG1CurvatureFloor (u : Real) : Real := Real.exp (-1) * deBruijnSaddleCurvature u

theorem deBruijnG1CurvatureFloor_pos (u : Real) : 0 < deBruijnG1CurvatureFloor u :=
  mul_pos (Real.exp_pos _) (deBruijnSaddleCurvature_pos u)

theorem deBruijnSaddleMoment_lower_near {u x : Real} (hx : deBruijnSaddle u - 1 ≤ x) :
    deBruijnG1CurvatureFloor u ≤ deBruijnSaddleMoment x := by
  have hi0 := (deBruijnSaddleMoment_intervalIntegrable (deBruijnSaddle u)).const_mul (Real.exp (-1))
  have hix := deBruijnSaddleMoment_intervalIntegrable x
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : Real) ≤ 1) hi0 hix (by
    intro t ht
    have he : t * deBruijnSaddle u - 1 ≤ t * x := by
      have hm := mul_le_mul_of_nonneg_left hx ht.1
      nlinarith [ht.2]
    have hE := Real.exp_le_exp.mpr he
    have hmult := mul_le_mul_of_nonneg_left hE ht.1
    rw [Real.exp_sub] at hmult
    have heq : Real.exp (t * deBruijnSaddle u) / Real.exp 1 = Real.exp (-1) * Real.exp (t * deBruijnSaddle u) := by
      rw [Real.exp_neg]
      ring
    rw [heq] at hmult
    nlinarith)
  rw [intervalIntegral.integral_const_mul] at h
  exact h

end

end Erdos1212Kernel
