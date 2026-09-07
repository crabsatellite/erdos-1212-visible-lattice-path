import Erdos1212Kernel.DeBruijnF1RayCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1RayConstant : Real :=
  (2 * Real.pi + 1) * Real.exp (2 * Real.pi + 1) + (Real.pi + 1) ^ 2 / 8

theorem deBruijnF1_upper_ray_norm {x : Real} (hx : 0 ≤ x) :
    ‖(x : Complex) + (Real.pi : Complex) * Complex.I‖ ≤ x + Real.pi := by
  calc
    _ ≤ ‖(x : Complex)‖ + ‖(Real.pi : Complex) * Complex.I‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem deBruijnF1_lower_ray_norm {x : Real} (hx : 0 ≤ x) :
    ‖(x : Complex) - (Real.pi : Complex) * Complex.I‖ ≤ x + Real.pi := by
  calc
    _ ≤ ‖(x : Complex)‖ + ‖(Real.pi : Complex) * Complex.I‖ := norm_sub_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem deBruijnF1Ray_correctedPhase_small_bound {x : Real} (hx : 0 ≤ x) (hxR : x ≤ Real.pi + 1) :
    deBruijnF1RayPhase x + x ^ 2 / 8 ≤ deBruijnF1RayConstant := by
  have hn : ‖(x : Complex) + (Real.pi : Complex) * Complex.I‖ ≤ 2 * Real.pi + 1 :=
    (deBruijnF1_upper_ray_norm hx).trans (by linarith)
  have hB : 0 ≤ 2 * Real.pi + 1 := by linarith [Real.pi_pos]
  have hE := (deBruijnComplexExpIntegral_norm ((x : Complex) + (Real.pi : Complex) * Complex.I)).trans
    (mul_le_mul hn (Real.exp_le_exp.mpr hn) (Real.exp_pos _).le hB)
  have hRe := Complex.re_le_norm (deBruijnComplexExpIntegral ((x : Complex) + (Real.pi : Complex) * Complex.I))
  have hsq : x ^ 2 ≤ (Real.pi + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxR) (show 0 ≤ Real.pi + 1 + x by linarith [Real.pi_pos])]
  unfold deBruijnF1RayPhase deBruijnF1RayConstant
  linarith

/-- A global Gaussian upper bound for the original source phase on its
upper horizontal contour ray. It is a convergence bound, not a saddle
asymptotic or a replacement phase. -/
theorem deBruijnF1RayPhase_upper_bound {x : Real} (hx : 0 ≤ x) :
    deBruijnF1RayPhase x ≤ deBruijnF1RayConstant - x ^ 2 / 8 := by
  have h : deBruijnF1RayPhase x + x ^ 2 / 8 ≤ deBruijnF1RayConstant := by
    by_cases hxR : x ≤ Real.pi + 1
    · exact deBruijnF1Ray_correctedPhase_small_bound hx hxR
    · have hR : 0 ≤ Real.pi + 1 := by linarith [Real.pi_pos]
      have hmono := deBruijnF1Ray_correctedPhase_antitoneOn
        (show Real.pi + 1 ∈ Set.Ici (Real.pi + 1) by simp)
        (le_of_lt (lt_of_not_ge hxR)) (le_of_lt (lt_of_not_ge hxR))
      exact hmono.trans (deBruijnF1Ray_correctedPhase_small_bound hR le_rfl)
  linarith

theorem deBruijnF1_ray_conj (x : Real) :
    starRingEnd Complex ((x : Complex) + (Real.pi : Complex) * Complex.I) =
      (x : Complex) - (Real.pi : Complex) * Complex.I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]

theorem deBruijnF1_lower_ray_phase_re (x : Real) :
    (deBruijnComplexExpIntegral ((x : Complex) - (Real.pi : Complex) * Complex.I)).re = deBruijnF1RayPhase x := by
  have h := congrArg Complex.re (deBruijnComplexExpIntegral_conj ((x : Complex) + (Real.pi : Complex) * Complex.I))
  rw [deBruijnF1_ray_conj] at h
  simpa only [Complex.conj_re] using h

end

end Erdos1212Kernel
