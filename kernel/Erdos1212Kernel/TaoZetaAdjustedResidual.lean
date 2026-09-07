import Erdos1212Kernel.TaoZetaAdjustmentLogDerivative

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem taoZetaLocalFactorProduct_analyticOnNhd
    {c : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1) :
    AnalyticOnNhd Complex (taoZetaLocalFactorProduct c R) (closedBall c R) := by
  let D := taoZetaLocalDivisor c R
  let φ := taoZetaLocalFactorProduct c R
  have hzetaAn : AnalyticOnNhd Complex riemannZeta (closedBall c R) :=
    analyticOn_riemannZeta.mono hAvoid
  have hzetaNF := hzetaAn.meromorphicNFOn
  have hDnonneg : 0 ≤ D := by
    simpa only [D, taoZetaLocalDivisor] using
      hzetaNF.divisor_nonneg_iff_analyticOnNhd.mpr hzetaAn
  have hφNF : MeromorphicNFOn φ (closedBall c R) := by
    unfold φ taoZetaLocalFactorProduct
    exact Function.FactorizedRational.meromorphicNFOn D _
  apply hφNF.divisor_nonneg_iff_analyticOnNhd.mp
  rw [show MeromorphicOn.divisor φ (closedBall c R) = D by
    unfold φ taoZetaLocalFactorProduct
    exact Function.FactorizedRational.divisor
      (by simpa only [D] using taoZetaLocalDivisor_support_finite c R)]
  exact hDnonneg

/-- Canonically adjusted zero-free residual whose boundary norm is
exactly the boundary norm of zeta. -/
theorem exists_taoZetaAdjustedResidual
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hSphere : ∀ z : Complex, riemannZeta z = 0 → dist z c ≠ R)
    (hcne : riemannZeta c ≠ 0) :
    ∃ G : Complex → Complex,
      AnalyticOnNhd Complex G (closedBall c R) ∧
      (∀ z ∈ closedBall c R, G z ≠ 0) ∧
      (∀ z ∈ sphere c R, ‖G z‖ = ‖riemannZeta z‖) ∧
      ‖riemannZeta c‖ ≤ ‖G c‖ ∧
      taoZetaLogDerivative c + taoZetaAdjustedReciprocalSum c R =
        -logDeriv G c := by
  obtain ⟨g, hg, hgn, hlocal, hdecomp⟩ :=
    exists_taoZetaLocalZeroFreeFactor_at_center hR hAvoid hcne
  let A := taoZetaAdjustmentProduct c R
  let φ := taoZetaLocalFactorProduct c R
  let G : Complex → Complex := fun z => g z * A z
  have hAAn := taoZetaAdjustmentProduct_analyticOnNhd hR hAvoid hSphere
  have hAnz : ∀ z ∈ closedBall c R, taoZetaAdjustmentProduct c R z ≠ 0 :=
    fun z hz => taoZetaAdjustmentProduct_ne_zero hR hAvoid hSphere hz
  have hφAn := taoZetaLocalFactorProduct_analyticOnNhd hAvoid
  have hprodAn : AnalyticOnNhd Complex (fun z => φ z * g z) (closedBall c R) :=
    hφAn.mul hg
  have hcU : c ∈ closedBall c R := by simp [hR.le]
  have hzetaAn := analyticOn_riemannZeta.mono hAvoid
  have hEqOn : Set.EqOn riemannZeta (fun z => φ z * g z) (closedBall c R) :=
    hzetaAn.eqOn_of_preconnected_of_eventuallyEq hprodAn
      (convex_closedBall c R).isPreconnected hcU
      (by simpa only [φ] using hlocal)
  refine ⟨G, hg.mul hAAn, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact mul_ne_zero (hgn ⟨z, hz⟩) (hAnz z hz)
  · intro z hz
    have hzclosed : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hboundary := norm_taoZetaAdjustmentProduct_on_sphere hR hAvoid hSphere hz
    have hzeta := hEqOn hzclosed
    dsimp only [G, A]
    rw [norm_mul, hboundary, ← norm_mul]
    rw [mul_comm]
    change riemannZeta z = taoZetaLocalFactorProduct c R z * g z at hzeta
    exact (congrArg norm hzeta).symm
  · have hcenter := norm_taoZetaLocalFactorProduct_le_adjustmentProduct_center
      hR hAvoid hSphere hcne
    have hzeta := hEqOn hcU
    change riemannZeta c = taoZetaLocalFactorProduct c R c * g c at hzeta
    calc
      ‖riemannZeta c‖ = ‖taoZetaLocalFactorProduct c R c * g c‖ := congrArg norm hzeta
      _ = ‖taoZetaLocalFactorProduct c R c‖ * ‖g c‖ := norm_mul _ _
      _ ≤ ‖taoZetaAdjustmentProduct c R c‖ * ‖g c‖ :=
        mul_le_mul_of_nonneg_right hcenter (norm_nonneg _)
      _ = ‖g c * taoZetaAdjustmentProduct c R c‖ := by rw [norm_mul, mul_comm]
      _ = ‖G c‖ := rfl
  · have hgCne : g c ≠ 0 := hgn ⟨c, hcU⟩
    have hACne : A c ≠ 0 := by
      simpa only [A] using hAnz c hcU
    have hlogG : logDeriv G c = logDeriv g c + logDeriv A c := by
      dsimp only [G]
      exact logDeriv_mul c hgCne hACne (hg c hcU).differentiableAt
        (hAAn c hcU).differentiableAt
    have hφlog : logDeriv φ c = taoZetaDivisorReciprocalSum c R := by
      simpa only [φ] using
        logDeriv_taoZetaLocalFactorProduct_eq_divisorSum hR.le hAvoid hcne
    have hadjust : taoZetaDivisorReciprocalSum c R - logDeriv A c =
        taoZetaAdjustedReciprocalSum c R := by
      simpa only [A] using
        taoZetaDivisorReciprocalSum_sub_adjustmentLogDeriv hR hAvoid hSphere
    rw [← hadjust, hdecomp, hφlog, hlogG]
    ring

theorem exists_taoZetaAdjustedResidual_norm_le
    {c : Complex} {R C : Real} (hR : 0 < R)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hSphere : ∀ z : Complex, riemannZeta z = 0 → dist z c ≠ R)
    (hcne : riemannZeta c ≠ 0)
    (hC : ∀ z ∈ sphere c R, ‖riemannZeta z‖ ≤ C) :
    ∃ G : Complex → Complex,
      AnalyticOnNhd Complex G (closedBall c R) ∧
      (∀ z ∈ closedBall c R, G z ≠ 0) ∧
      (∀ z ∈ closedBall c R, ‖G z‖ ≤ C) ∧
      ‖riemannZeta c‖ ≤ ‖G c‖ ∧
      taoZetaLogDerivative c + taoZetaAdjustedReciprocalSum c R =
        -logDeriv G c := by
  obtain ⟨G, hG, hGnz, hboundary, hcenter, hexact⟩ :=
    exists_taoZetaAdjustedResidual hR hAvoid hSphere hcne
  refine ⟨G, hG, hGnz, ?_, hcenter, hexact⟩
  intro z hz
  have hdiff : DiffContOnCl Complex G (ball c R) :=
    hG.differentiableOn.diffContOnCl_ball subset_rfl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
    (fun w hw => (hboundary w (frontier_ball_subset_sphere hw)).le.trans
      (hC w (frontier_ball_subset_sphere hw)))
  simpa only [closure_ball c hR.ne'] using hz

end

end Erdos1212Kernel
