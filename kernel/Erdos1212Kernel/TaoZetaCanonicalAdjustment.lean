import Erdos1212Kernel.TaoZetaFactorLogDerivative
import Mathlib.Analysis.Complex.CanonicalDecomposition

namespace Erdos1212Kernel

noncomputable section

open Metric ComplexConjugate

set_option maxHeartbeats 1900000

def taoShiftedCanonicalFactor (c : Complex) (R : Real) (ρ : Complex) :
    Complex → Complex :=
  fun z => Complex.canonicalFactor R (ρ - c) (z - c)

/-- The analytic numerator left after cancelling `(z-rho)` against the
pole of the shifted canonical factor. -/
def taoCanonicalAdjustment (c : Complex) (R : Real) (ρ : Complex) :
    Complex → Complex :=
  fun z => ((R : Complex) ^ 2 - conj (ρ - c) * (z - c)) / R

theorem sub_center_mem_ball_zero {c ρ : Complex} {R : Real}
    (hρ : ρ ∈ ball c R) : ρ - c ∈ ball 0 R := by
  rw [mem_ball, dist_zero_right]
  simpa only [Complex.dist_eq]
    using (show dist ρ c < R from mem_ball.mp hρ)

theorem sub_center_mem_closedBall_zero {c z : Complex} {R : Real}
    (hz : z ∈ closedBall c R) : z - c ∈ closedBall 0 R := by
  rw [mem_closedBall, dist_zero_right]
  simpa only [Complex.dist_eq]
    using (show dist z c ≤ R from mem_closedBall.mp hz)

theorem sub_center_mem_sphere_zero {c z : Complex} {R : Real}
    (hz : z ∈ sphere c R) : z - c ∈ sphere 0 R := by
  rw [mem_sphere, dist_zero_right]
  simpa only [Complex.dist_eq]
    using (show dist z c = R from mem_sphere.mp hz)

theorem taoCanonicalAdjustment_ne_zero {c ρ z : Complex} {R : Real}
    (hR : 0 < R) (hρ : ρ ∈ ball c R) (hz : z ∈ closedBall c R) :
    taoCanonicalAdjustment c R ρ z ≠ 0 := by
  let w := ρ - c
  let v := z - c
  have hw : ‖w‖ < R := by
    simpa only [w, mem_ball, dist_zero_right] using sub_center_mem_ball_zero hρ
  have hv : ‖v‖ ≤ R := by
    simpa only [v, mem_closedBall, dist_zero_right] using sub_center_mem_closedBall_zero hz
  have hprod : ‖conj w * v‖ < R * R := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hv (norm_nonneg w)).trans_lt
      (mul_lt_mul_of_pos_right hw hR)
  have hnum : (R : Complex) ^ 2 - conj w * v ≠ 0 := by
    intro hzero
    have heq : (R : Complex) ^ 2 = conj w * v := sub_eq_zero.mp hzero
    have hnorm := congrArg norm heq
    have hRnorm : ‖(R : Complex) ^ 2‖ = R * R := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      ring
    rw [hRnorm] at hnorm
    linarith
  unfold taoCanonicalAdjustment
  dsimp only [w, v] at hnum
  exact div_ne_zero hnum (by exact_mod_cast hR.ne')

theorem taoCanonicalAdjustment_eq_mul_shiftedFactor {c ρ z : Complex} {R : Real}
    (hR : 0 < R) (hzρ : z ≠ ρ) :
    taoCanonicalAdjustment c R ρ z =
      (z - ρ) * taoShiftedCanonicalFactor c R ρ z := by
  unfold taoCanonicalAdjustment taoShiftedCanonicalFactor Complex.canonicalFactor
  have hdiff : (z - c) - (ρ - c) = z - ρ := by ring
  rw [hdiff]
  field_simp [hR.ne', sub_ne_zero.mpr hzρ]
  <;> ring

theorem norm_taoCanonicalAdjustment_on_sphere {c ρ z : Complex} {R : Real}
    (hR : 0 < R) (hρ : ρ ∈ ball c R) (hz : z ∈ sphere c R) :
    ‖taoCanonicalAdjustment c R ρ z‖ = ‖z - ρ‖ := by
  have hzρ : z ≠ ρ := by
    intro h
    subst z
    have := (mem_ball.mp hρ)
    have := (mem_sphere.mp hz)
    linarith
  rw [taoCanonicalAdjustment_eq_mul_shiftedFactor hR hzρ, norm_mul]
  unfold taoShiftedCanonicalFactor
  rw [
    Complex.norm_canonicalFactor_eval_circle_eq_one
      (sub_center_mem_ball_zero hρ) (sub_center_mem_sphere_zero hz), mul_one]

theorem taoCanonicalAdjustment_apply_center {c ρ : Complex} {R : Real}
    (hR : 0 < R) :
    taoCanonicalAdjustment c R ρ c = R := by
  unfold taoCanonicalAdjustment
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hR.ne']

theorem norm_taoCanonicalAdjustment_apply_center {c ρ : Complex} {R : Real}
    (hR : 0 < R) :
    ‖taoCanonicalAdjustment c R ρ c‖ = R := by
  rw [taoCanonicalAdjustment_apply_center hR, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]

end

end Erdos1212Kernel
