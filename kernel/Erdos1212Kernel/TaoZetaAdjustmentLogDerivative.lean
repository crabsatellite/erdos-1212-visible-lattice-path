import Erdos1212Kernel.TaoZetaAdjustmentProduct

namespace Erdos1212Kernel

noncomputable section

open Metric
open ComplexConjugate

set_option maxHeartbeats 1900000

def taoZetaAdjustedKernel (c : Complex) (R : Real) (ρ : Complex) : Complex :=
  1 / (c - ρ) + conj (ρ - c) / (R : Complex) ^ 2

def taoZetaAdjustedReciprocalSum (c : Complex) (R : Real) : Complex :=
  ∑ ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset,
    ((taoZetaLocalDivisor c R ρ : Int) : Complex) *
      taoZetaAdjustedKernel c R ρ

theorem logDeriv_taoCanonicalAdjustment_center
    {c ρ : Complex} {R : Real} (hR : 0 < R) :
    logDeriv (taoCanonicalAdjustment c R ρ) c =
      -conj (ρ - c) / (R : Complex) ^ 2 := by
  unfold logDeriv taoCanonicalAdjustment
  simp only [Pi.div_apply]
  rw [show ((R : Complex) ^ 2 - conj (ρ - c) * (c - c)) / R = R by
    simpa only [taoCanonicalAdjustment] using taoCanonicalAdjustment_apply_center
      (c := c) (ρ := ρ) hR]
  have hlin : HasDerivAt (fun z : Complex => conj (ρ - c) * (z - c))
      (conj (ρ - c)) c := by
    simpa using ((hasDerivAt_id c).sub_const c).const_mul (conj (ρ - c))
  have hnum := (hasDerivAt_const c ((R : Complex) ^ 2)).sub hlin
  have hdiv := hnum.div_const (R : Complex)
  have hderiv :
      deriv (fun z : Complex =>
        ((R : Complex) ^ 2 - conj (ρ - c) * (z - c)) / R) c =
        -conj (ρ - c) / R := by
    simpa using hdiv.deriv
  rw [hderiv]
  field_simp [hR.ne']

theorem logDeriv_taoZetaAdjustmentProduct_eq
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R) :
    logDeriv (taoZetaAdjustmentProduct c R) c =
      ∑ ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset,
        ((taoZetaLocalDivisor c R ρ : Int) : Complex) *
          (-conj (ρ - c) / (R : Complex) ^ 2) := by
  let D := taoZetaLocalDivisor c R
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hcU : c ∈ closedBall c R := by simp [hR.le]
  have hfactor_ne (ρ : Complex) (hρ : ρ ∈ S) :
      (taoCanonicalAdjustment c R ρ c) ^ (D ρ) ≠ 0 := by
    have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
      simpa only [S, Set.Finite.mem_toFinset] using hρ
    have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free
      hAvoid hSphere hρsupport
    exact zpow_ne_zero _ (taoCanonicalAdjustment_ne_zero hR hρball hcU)
  have hfactor_diff (ρ : Complex) (hρ : ρ ∈ S) :
      DifferentiableAt Complex
        (fun z => (taoCanonicalAdjustment c R ρ z) ^ (D ρ)) c := by
    have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
      simpa only [S, Set.Finite.mem_toFinset] using hρ
    have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free
      hAvoid hSphere hρsupport
    have hne := taoCanonicalAdjustment_ne_zero hR hρball hcU
    have hadj : AnalyticAt Complex (taoCanonicalAdjustment c R ρ) c := by
      unfold taoCanonicalAdjustment
      fun_prop (disch := exact_mod_cast hR.ne')
    exact (hadj.zpow hne).differentiableAt
  unfold taoZetaAdjustmentProduct
  rw [logDeriv_prod (s := S)
    (f := fun ρ z => (taoCanonicalAdjustment c R ρ z) ^ (D ρ))
    (fun ρ hρ => hfactor_ne ρ hρ) (fun ρ hρ => hfactor_diff ρ hρ)]
  change (∑ ρ ∈ S,
      logDeriv (fun z => (taoCanonicalAdjustment c R ρ z) ^ (D ρ)) c) = _
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [logDeriv_fun_zpow]
  · rw [logDeriv_taoCanonicalAdjustment_center hR]
  · unfold taoCanonicalAdjustment
    fun_prop (disch := exact_mod_cast hR.ne')

theorem taoZetaDivisorReciprocalSum_sub_adjustmentLogDeriv
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R) :
    taoZetaDivisorReciprocalSum c R -
        logDeriv (taoZetaAdjustmentProduct c R) c =
      taoZetaAdjustedReciprocalSum c R := by
  rw [logDeriv_taoZetaAdjustmentProduct_eq hR hAvoid hSphere]
  unfold taoZetaDivisorReciprocalSum taoZetaAdjustedReciprocalSum
  unfold taoZetaAdjustedKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

end

end Erdos1212Kernel
