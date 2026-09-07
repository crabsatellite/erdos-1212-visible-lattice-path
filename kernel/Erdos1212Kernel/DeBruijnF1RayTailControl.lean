import Erdos1212Kernel.DeBruijnVerticalPhaseLoss
import Erdos1212Kernel.DeBruijnF1SaddlePieces

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1RayPhase_antitoneOn_nonnegative : AntitoneOn deBruijnF1RayPhase (Set.Ici (0 : Real)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real)) deBruijnF1RayPhase_continuous.continuousOn
  · intro x _hx
    exact (deBruijnF1RayPhase_hasDerivAt x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(deBruijnF1RayPhase_hasDerivAt x).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hx.le
    · positivity

theorem deBruijnF1_upper_ray_norm_eq (u x : Real) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)‖ =
      Real.exp (-u * x + deBruijnF1RayPhase x) := by
  unfold deBruijnF1Integrand deBruijnF1RayPhase
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, neg_zero, sub_zero, add_zero]

theorem deBruijnF1_lower_ray_norm_eq (u x : Real) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)‖ =
      Real.exp (-u * x + deBruijnF1RayPhase x) := by
  have h := deBruijnF1Integrand_conj (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)
  rw [Complex.conj_ofReal, deBruijnF1_ray_conj] at h
  rw [h, Complex.norm_conj]
  exact deBruijnF1_upper_ray_norm_eq u x

theorem deBruijnF1_upper_ray_decay (u : Real) {r x : Real} (hr : 0 ≤ r) (hrx : r ≤ x) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)‖ ≤
      ‖deBruijnF1Integrand (u : Complex) ((r : Complex) + (Real.pi : Complex) * Complex.I)‖ * Real.exp (-u * (x - r)) := by
  rw [deBruijnF1_upper_ray_norm_eq, deBruijnF1_upper_ray_norm_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := deBruijnF1RayPhase_antitoneOn_nonnegative hr (hr.trans hrx) hrx
  nlinarith

theorem deBruijnF1_lower_ray_decay (u : Real) {r x : Real} (hr : 0 ≤ r) (hrx : r ≤ x) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)‖ ≤
      ‖deBruijnF1Integrand (u : Complex) ((r : Complex) - (Real.pi : Complex) * Complex.I)‖ * Real.exp (-u * (x - r)) := by
  rw [deBruijnF1_lower_ray_norm_eq, deBruijnF1_lower_ray_norm_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := deBruijnF1RayPhase_antitoneOn_nonnegative hr (hr.trans hrx) hrx
  nlinarith

theorem deBruijnF1_upper_saddle_endpoint_bound (u : Real) :
    ‖deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + (Real.pi : Complex) * Complex.I)‖ ≤ deBruijnSaddleHeight u := by
  have h := deBruijnF1_vertical_ratio_bound u (y := Real.pi) (by rw [abs_of_pos Real.pi_pos])
  have hc : -(2 / Real.pi ^ 2) * Real.pi ^ 2 = (-2 : Real) := by field_simp
  rw [hc] at h
  have he : Real.exp (-2 * deBruijnSaddleCurvature u) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [deBruijnSaddleCurvature_pos u])
  have hb := h.trans he
  rw [norm_div, deBruijnF1Integrand_saddle_norm] at hb
  have h' := (div_le_iff₀ (deBruijnSaddleHeight_pos u)).mp hb
  simpa only [one_mul] using h'

theorem deBruijnF1_lower_saddle_endpoint_bound (u : Real) :
    ‖deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) - (Real.pi : Complex) * Complex.I)‖ ≤ deBruijnSaddleHeight u := by
  rw [deBruijnF1_lower_ray_norm_eq, ← deBruijnF1_upper_ray_norm_eq]
  exact deBruijnF1_upper_saddle_endpoint_bound u

theorem deBruijnF1_upper_saddle_tail_pointwise {u x : Real} (hu : 1 < u) (hx : deBruijnSaddle u ≤ x) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnSaddleHeight u * Real.exp (-u * (x - deBruijnSaddle u)) :=
  (deBruijnF1_upper_ray_decay u (deBruijnSaddle_pos hu).le hx).trans
    (mul_le_mul_of_nonneg_right (deBruijnF1_upper_saddle_endpoint_bound u) (Real.exp_pos _).le)

theorem deBruijnF1_lower_saddle_tail_pointwise {u x : Real} (hu : 1 < u) (hx : deBruijnSaddle u ≤ x) :
    ‖deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnSaddleHeight u * Real.exp (-u * (x - deBruijnSaddle u)) :=
  (deBruijnF1_lower_ray_decay u (deBruijnSaddle_pos hu).le hx).trans
    (mul_le_mul_of_nonneg_right (deBruijnF1_lower_saddle_endpoint_bound u) (Real.exp_pos _).le)

end

end Erdos1212Kernel
