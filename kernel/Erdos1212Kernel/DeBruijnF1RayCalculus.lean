import Erdos1212Kernel.DeBruijnComplexPhaseDerivative
import Erdos1212Kernel.DeBruijnComplexPhaseTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1RayPhase (x : Real) : Real :=
  (deBruijnComplexExpIntegral ((x : Complex) + (Real.pi : Complex) * Complex.I)).re

theorem deBruijnF1_upper_ray_ne_zero (x : Real) : (x : Complex) + (Real.pi : Complex) * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add, Complex.zero_im] at hi
  exact Real.pi_ne_zero hi

theorem deBruijnF1RayPhase_continuous : Continuous deBruijnF1RayPhase :=
  Complex.continuous_re.comp (deBruijnComplexExpIntegral_continuous.comp (Complex.continuous_ofReal.add continuous_const))

theorem deBruijnF1RayPhase_hasDerivAt (x : Real) :
    HasDerivAt deBruijnF1RayPhase (-(Real.exp x + 1) * x / (x ^ 2 + Real.pi ^ 2)) x := by
  have hs : HasDerivAt (fun z : Complex => z + (Real.pi : Complex) * Complex.I) 1 (x : Complex) :=
    (hasDerivAt_id (x : Complex)).add_const _
  have h := (deBruijnComplexExpIntegral_hasDerivAt_quot (deBruijnF1_upper_ray_ne_zero x)).comp (x : Complex) hs
  simp only [mul_one] at h
  have hr := h.real_of_complex
  apply hr.congr_deriv
  rw [Complex.exp_add_pi_mul_I, ← Complex.ofReal_exp]
  simp only [Complex.div_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
    zero_mul, sub_zero, add_zero, Complex.sub_im, Complex.neg_im, neg_zero, Complex.one_im,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, Complex.normSq_apply, zero_div]
  ring

theorem deBruijnF1RayPhase_derivative_bound {x : Real} (hx : Real.pi ≤ x) :
    -(Real.exp x + 1) * x / (x ^ 2 + Real.pi ^ 2) ≤ -x / 4 := by
  have hx0 : 0 ≤ x := Real.pi_pos.le.trans hx
  have hd : 0 < x ^ 2 + Real.pi ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos Real.pi_pos)
  have he : x ^ 2 / 2 ≤ Real.exp x + 1 := by nlinarith [Real.quadratic_le_exp_of_nonneg hx0]
  have hp : x ^ 2 + Real.pi ^ 2 ≤ 2 * x ^ 2 := by nlinarith [Real.pi_pos]
  have heMul := mul_le_mul_of_nonneg_right he hx0
  have hpMul := mul_le_mul_of_nonneg_left hp (show 0 ≤ x / 4 by positivity)
  rw [div_le_iff₀ hd]
  nlinarith

theorem deBruijnF1Ray_correctedPhase_hasDerivAt (x : Real) :
    HasDerivAt (fun t : Real => deBruijnF1RayPhase t + t ^ 2 / 8)
      (-(Real.exp x + 1) * x / (x ^ 2 + Real.pi ^ 2) + x / 4) x := by
  have h := (deBruijnF1RayPhase_hasDerivAt x).add (((hasDerivAt_id x).pow 2).div_const 8)
  apply h.congr_deriv
  simp only [id_eq, pow_one, mul_one]
  ring

theorem deBruijnF1Ray_correctedPhase_antitoneOn :
    AntitoneOn (fun x : Real => deBruijnF1RayPhase x + x ^ 2 / 8) (Set.Ici (Real.pi + 1)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (Real.pi + 1))
    (deBruijnF1RayPhase_continuous.add ((continuous_id.pow 2).div_const 8)).continuousOn
  · intro x _hx
    exact (deBruijnF1Ray_correctedPhase_hasDerivAt x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    change deriv (fun t : Real => deBruijnF1RayPhase t + t ^ 2 / 8) x ≤ 0
    rw [(deBruijnF1Ray_correctedPhase_hasDerivAt x).deriv]
    have h := deBruijnF1RayPhase_derivative_bound (by linarith [hx.out] : Real.pi ≤ x)
    linarith

end

end Erdos1212Kernel
