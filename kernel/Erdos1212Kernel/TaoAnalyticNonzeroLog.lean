import Erdos1212Kernel.TaoZetaNearbyZeroPositivity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

/-- A nonvanishing holomorphic function on a disk has a normalized
holomorphic logarithm. The construction uses a primitive of `g'/g` and
does not assume a branch of the principal logarithm. -/
theorem exists_normalizedAnalyticLogOn_ball
    {g : Complex → Complex} {c : Complex} {R : Real}
    (hR : 0 < R) (hg : DifferentiableOn Complex g (ball c R))
    (hgn : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ H : Complex → Complex,
      H c = 0 ∧
      (∀ z ∈ ball c R, HasDerivAt H (logDeriv g z) z) ∧
      (∀ z ∈ ball c R, Complex.exp (H z) = g z / g c) := by
  have hderiv : DifferentiableOn Complex (deriv g) (ball c R) :=
    hg.deriv isOpen_ball
  have hlog : DifferentiableOn Complex (logDeriv g) (ball c R) := by
    intro z hz
    unfold logDeriv
    exact (hderiv z hz).div (hg z hz) (hgn z hz)
  obtain ⟨H, hHc, hH⟩ := hlog.isExactOn_ball.with_val_at c 0
  have hHdiff : DifferentiableOn Complex H (ball c R) := by
    intro z hz
    exact (hH z hz).differentiableAt.differentiableWithinAt
  let eH : Complex → Complex := fun z => Complex.exp (H z)
  have heHdiff : DifferentiableOn Complex eH (ball c R) := by
    intro z hz
    exact Complex.differentiableAt_exp.comp z (hH z hz).differentiableAt |>.differentiableWithinAt
  have heHnz : ∀ z ∈ ball c R, eH z ≠ 0 := fun z _hz => Complex.exp_ne_zero _
  have hlogEq : Set.EqOn (logDeriv eH) (logDeriv g) (ball c R) := by
    intro z hz
    change logDeriv (Complex.exp ∘ H) z = logDeriv g z
    rw [logDeriv_comp Complex.differentiableAt_exp (hH z hz).differentiableAt,
      Complex.logDeriv_exp, Pi.one_apply, one_mul, (hH z hz).deriv]
  obtain ⟨a, ha0, ha⟩ :=
    (logDeriv_eqOn_iff heHdiff hg isOpen_ball (convex_ball c R).isPreconnected
      hgn heHnz).mp hlogEq
  have hc : c ∈ ball c R := mem_ball_self hR
  have hac : a * g c = 1 := by
    have := ha hc
    simp only [eH, hHc, Complex.exp_zero, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hgc : g c ≠ 0 := hgn c hc
  have haeq : a = (g c)⁻¹ := by
    calc
      a = a * 1 := by ring
      _ = a * (g c * (g c)⁻¹) := by rw [mul_inv_cancel₀ hgc]
      _ = (a * g c) * (g c)⁻¹ := by ring
      _ = (g c)⁻¹ := by rw [hac, one_mul]
  refine ⟨H, hHc, hH, fun z hz => ?_⟩
  calc
    Complex.exp (H z) = a * g z := by
      simpa only [eH, Pi.smul_apply, smul_eq_mul] using ha hz
    _ = g z / g c := by rw [haeq, div_eq_mul_inv]; ring

theorem exists_normalizedAnalyticLogOn_ball_with_re
    {g : Complex → Complex} {c : Complex} {R : Real}
    (hR : 0 < R) (hg : DifferentiableOn Complex g (ball c R))
    (hgn : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ H : Complex → Complex,
      H c = 0 ∧
      (∀ z ∈ ball c R, HasDerivAt H (logDeriv g z) z) ∧
      (∀ z ∈ ball c R,
        (H z).re = Real.log ‖g z‖ - Real.log ‖g c‖) := by
  obtain ⟨H, hHc, hH, hExp⟩ := exists_normalizedAnalyticLogOn_ball hR hg hgn
  refine ⟨H, hHc, hH, fun z hz => ?_⟩
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr (hgn c (mem_ball_self hR))
  have hgz : 0 < ‖g z‖ := norm_pos_iff.mpr (hgn z hz)
  have hnorm := congrArg norm (hExp z hz)
  rw [Complex.norm_exp, norm_div] at hnorm
  have hlog := congrArg Real.log hnorm
  rw [Real.log_exp, Real.log_div hgz.ne' hgc.ne'] at hlog
  exact hlog

end

end Erdos1212Kernel
