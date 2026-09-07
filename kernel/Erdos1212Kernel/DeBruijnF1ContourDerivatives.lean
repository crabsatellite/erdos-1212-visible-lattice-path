import Erdos1212Kernel.DeBruijnF1Contour
import Erdos1212Kernel.DeBruijnF1FamilyBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

private theorem f1_ray_integral_hasDerivAt (r : Real → Complex) (hr : Continuous r)
    (hi : ∀ u : Complex, IntegrableOn (fun x : Real => deBruijnF1Integrand u (r x)) (Set.Ioi (0 : Real)))
    (hn : ∀ x : Real, 0 ≤ x → ‖r x‖ ≤ x + Real.pi)
    (hb : ∀ (u : Complex) (x M : Real), 0 ≤ x → ‖u‖ ≤ M →
      ‖deBruijnF1Integrand u (r x)‖ ≤ deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2)) (u : Complex) :
    HasDerivAt (fun v : Complex => ∫ x in Set.Ioi (0 : Real), deBruijnF1Integrand v (r x))
      (∫ x in Set.Ioi (0 : Real), -r x * deBruijnF1Integrand u (r x)) u := by
  let F := fun v : Complex => fun x : Real => deBruijnF1Integrand v (r x)
  let F' := fun v : Complex => fun x : Real => -r x * deBruijnF1Integrand v (r x)
  have hmeas : ∀ᶠ v in nhds u, AEStronglyMeasurable (F v) (volume.restrict (Set.Ioi (0 : Real))) := by
    filter_upwards with v
    exact ((deBruijnF1Integrand_continuous v).comp hr).aestronglyMeasurable
  have hF'cont : Continuous (F' u) := hr.neg.mul ((deBruijnF1Integrand_continuous u).comp hr)
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : Real))), ∀ v ∈ Metric.ball u 1,
      ‖F' v x‖ ≤ deBruijnF1RayDerivativeMajorant (‖u‖ + 1) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro v hv
    exact deBruijnF1_ray_derivative_bound hx.le (hn x hx.le)
      (hb v x (‖u‖ + 1) hx.le (deBruijn_complex_norm_of_mem_ball_one hv))
  have hdiff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : Real))), ∀ v ∈ Metric.ball u 1,
      HasDerivAt (fun w : Complex => F w x) (F' v x) v := by
    filter_upwards with x
    intro v _hv
    exact deBruijnF1Integrand_hasDerivAt_parameter v (r x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : Real))) (F := F) (F' := F')
    (bound := deBruijnF1RayDerivativeMajorant (‖u‖ + 1)) (Metric.ball_mem_nhds u (by norm_num))
    hmeas (hi u) hF'cont.aestronglyMeasurable hbound (deBruijnF1RayDerivativeMajorant_integrable _) hdiff).2

theorem deBruijnF1UpperIntegral_hasDerivAt (u : Complex) :
    HasDerivAt deBruijnF1UpperIntegral
      (∫ x in Set.Ioi (0 : Real), -((x : Complex) + (Real.pi : Complex) * Complex.I) *
        deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) u := by
  exact f1_ray_integral_hasDerivAt (fun x : Real => (x : Complex) + (Real.pi : Complex) * Complex.I)
    (Complex.continuous_ofReal.add continuous_const) deBruijnF1_upper_ray_integrable
    (fun _x hx => deBruijnF1_upper_ray_norm hx)
    (fun _v _x _M hx hv => deBruijnF1Integrand_upper_ray_bound hx hv) u

theorem deBruijnF1LowerIntegral_hasDerivAt (u : Complex) :
    HasDerivAt deBruijnF1LowerIntegral
      (∫ x in Set.Ioi (0 : Real), -((x : Complex) - (Real.pi : Complex) * Complex.I) *
        deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) u := by
  exact f1_ray_integral_hasDerivAt (fun x : Real => (x : Complex) - (Real.pi : Complex) * Complex.I)
    (Complex.continuous_ofReal.sub continuous_const) deBruijnF1_lower_ray_integrable
    (fun _x hx => deBruijnF1_lower_ray_norm hx)
    (fun _v _x _M hx hv => deBruijnF1Integrand_lower_ray_bound hx hv) u

theorem deBruijnF1VerticalIntegral_hasDerivAt (u : Complex) :
    HasDerivAt deBruijnF1VerticalIntegral
      (∫ t in (-Real.pi)..Real.pi,
        (-((t : Complex) * Complex.I) * deBruijnF1Integrand u ((t : Complex) * Complex.I)) * Complex.I) u := by
  let F := fun v : Complex => fun t : Real => deBruijnF1Integrand v ((t : Complex) * Complex.I) * Complex.I
  let F' := fun v : Complex => fun t : Real =>
    (-((t : Complex) * Complex.I) * deBruijnF1Integrand v ((t : Complex) * Complex.I)) * Complex.I
  let B : Real := Real.pi * Real.exp ((‖u‖ + 1) * Real.pi + Real.pi * Real.exp Real.pi)
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hr : Continuous (fun t : Real => (t : Complex) * Complex.I) := Complex.continuous_ofReal.mul_const _
  have hmeas : ∀ᶠ v in nhds u, AEStronglyMeasurable (F v) (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    filter_upwards with v
    exact (((deBruijnF1Integrand_continuous v).comp hr).mul_const Complex.I).aestronglyMeasurable
  have hF'cont : Continuous (F' u) := (hr.neg.mul ((deBruijnF1Integrand_continuous u).comp hr)).mul_const Complex.I
  have hi : IntegrableOn (F u) (Set.Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp (deBruijnF1_vertical_integrable u)
  have hbi : IntegrableOn (fun _t : Real => B) (Set.Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp _root_.intervalIntegrable_const
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-Real.pi) Real.pi)), ∀ v ∈ Metric.ball u 1, ‖F' v t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro v hv
    exact deBruijnF1_vertical_derivative_bound (deBruijn_complex_norm_of_mem_ball_one hv) ⟨ht.1.le, ht.2⟩
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-Real.pi) Real.pi)), ∀ v ∈ Metric.ball u 1,
      HasDerivAt (fun w : Complex => F w t) (F' v t) v := by
    filter_upwards with t
    intro v _hv
    exact (deBruijnF1Integrand_hasDerivAt_parameter v ((t : Complex) * Complex.I)).mul_const Complex.I
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) (F := F) (F' := F') (bound := fun _t : Real => B)
    (Metric.ball_mem_nhds u (by norm_num)) hmeas hi hF'cont.aestronglyMeasurable hbound hbi hdiff).2
  change HasDerivAt (fun v : Complex => ∫ t in (-Real.pi)..Real.pi,
    deBruijnF1Integrand v ((t : Complex) * Complex.I) * Complex.I) _ u
  simpa only [intervalIntegral.integral_of_le hπ, F, F'] using h

end

end Erdos1212Kernel
