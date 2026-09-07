import Erdos1212Kernel.DeBruijnF1ContourIntegrability

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijn_complex_norm_of_mem_ball_one {u v : Complex} (hv : v ∈ Metric.ball u 1) :
    ‖v‖ ≤ ‖u‖ + 1 := by
  have hd : ‖v - u‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hv
  have htri : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
    calc
      ‖v‖ = ‖(v - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

theorem deBruijnF1Integrand_norm_on_balls {u z : Complex} {M R : Real} (hu : ‖u‖ ≤ M) (hz : ‖z‖ ≤ R) :
    ‖deBruijnF1Integrand u z‖ ≤ Real.exp (M * R + R * Real.exp R) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hneg : (-u * z).re ≤ M * R := by
    calc
      _ ≤ ‖-u * z‖ := Complex.re_le_norm _
      _ = ‖u‖ * ‖z‖ := by rw [norm_mul, norm_neg]
      _ ≤ _ := mul_le_mul hu hz (norm_nonneg z) hM
  have hE : (deBruijnComplexExpIntegral z).re ≤ R * Real.exp R :=
    (Complex.re_le_norm _).trans ((deBruijnComplexExpIntegral_norm z).trans
      (mul_le_mul hz (Real.exp_le_exp.mpr hz) (Real.exp_pos _).le hR))
  unfold deBruijnF1Integrand
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [Complex.add_re]
  linarith

def deBruijnF1RayDerivativeMajorant (M x : Real) : Real :=
  deBruijnF1RayAmplitude M * (x + Real.pi) * Real.exp (-(1 / 16 : Real) * x ^ 2)

theorem deBruijnF1RayDerivativeMajorant_integrable (M : Real) :
    IntegrableOn (deBruijnF1RayDerivativeMajorant M) (Set.Ioi (0 : Real)) := by
  have h0 : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have h1 : IntegrableOn (fun x : Real => x * Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have hm := (h1.add (h0.const_mul Real.pi)).const_mul (deBruijnF1RayAmplitude M)
  apply hm.congr
  filter_upwards with x
  dsimp [deBruijnF1RayDerivativeMajorant]
  ring

theorem deBruijnF1_ray_derivative_bound {u z : Complex} {x M : Real} (hx : 0 ≤ x)
    (hz : ‖z‖ ≤ x + Real.pi)
    (hF : ‖deBruijnF1Integrand u z‖ ≤ deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2)) :
    ‖-z * deBruijnF1Integrand u z‖ ≤ deBruijnF1RayDerivativeMajorant M x := by
  rw [norm_mul, norm_neg]
  calc
    _ ≤ (x + Real.pi) * (deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2)) :=
      mul_le_mul hz hF (norm_nonneg _) (by linarith [Real.pi_pos])
    _ = _ := by unfold deBruijnF1RayDerivativeMajorant; ring

theorem deBruijnF1_vertical_derivative_bound {u : Complex} {M t : Real}
    (hu : ‖u‖ ≤ M) (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    ‖(-((t : Complex) * Complex.I) * deBruijnF1Integrand u ((t : Complex) * Complex.I)) * Complex.I‖ ≤
      Real.pi * Real.exp (M * Real.pi + Real.pi * Real.exp Real.pi) := by
  have hz : ‖(t : Complex) * Complex.I‖ ≤ Real.pi := by
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr ht
  have hF := deBruijnF1Integrand_norm_on_balls hu hz
  rw [norm_mul, Complex.norm_I, mul_one, norm_mul, norm_neg]
  exact mul_le_mul hz hF (norm_nonneg _) Real.pi_pos.le

end

end Erdos1212Kernel
