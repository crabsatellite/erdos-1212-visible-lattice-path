import Erdos1212Kernel.TaoZetaRadiusSelection

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

def taoZetaAdjustmentProduct (c : Complex) (R : Real) : Complex → Complex :=
  fun z => ∏ ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset,
    (taoCanonicalAdjustment c R ρ z) ^ (taoZetaLocalDivisor c R ρ)

theorem taoZetaAdjustmentProduct_ne_zero
    {c z : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R)
    (hz : z ∈ closedBall c R) :
    taoZetaAdjustmentProduct c R z ≠ 0 := by
  unfold taoZetaAdjustmentProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
    simpa only [Set.Finite.mem_toFinset] using hρ
  have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free hAvoid hSphere hρsupport
  exact zpow_ne_zero _ (taoCanonicalAdjustment_ne_zero hR hρball hz)

theorem taoZetaAdjustmentProduct_analyticOnNhd
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R) :
    AnalyticOnNhd Complex (taoZetaAdjustmentProduct c R) (closedBall c R) := by
  intro z hz
  unfold taoZetaAdjustmentProduct
  apply Finset.analyticAt_fun_prod
  intro ρ hρ
  have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
    simpa only [Set.Finite.mem_toFinset] using hρ
  have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free hAvoid hSphere hρsupport
  have hne := taoCanonicalAdjustment_ne_zero hR hρball hz
  have hadj : AnalyticAt Complex (taoCanonicalAdjustment c R ρ) z := by
    unfold taoCanonicalAdjustment
    fun_prop (disch := exact_mod_cast hR.ne')
  exact hadj.zpow hne

theorem norm_taoZetaAdjustmentProduct_on_sphere
    {c z : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R)
    (hz : z ∈ sphere c R) :
    ‖taoZetaAdjustmentProduct c R z‖ =
      ‖taoZetaLocalFactorProduct c R z‖ := by
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hfactor (ρ : Complex) (hρ : ρ ∈ S) :
      ‖(taoCanonicalAdjustment c R ρ z) ^ (taoZetaLocalDivisor c R ρ)‖ =
        ‖(z - ρ) ^ (taoZetaLocalDivisor c R ρ)‖ := by
    have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
      simpa only [S, Set.Finite.mem_toFinset] using hρ
    have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free hAvoid hSphere hρsupport
    rw [Complex.norm_zpow, Complex.norm_zpow,
      norm_taoCanonicalAdjustment_on_sphere hR hρball hz]
  unfold taoZetaAdjustmentProduct
  rw [Complex.norm_prod]
  have hφeval := congrArg (fun f : Complex → Complex => f z)
    (taoZetaLocalFactorProduct_eq_finset_prod c R)
  simp only [Finset.prod_apply] at hφeval
  rw [hφeval, Complex.norm_prod]
  exact Finset.prod_congr rfl hfactor

theorem norm_taoZetaLocalFactorProduct_le_adjustmentProduct_center
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ w ∈ closedBall c R, w ≠ 1)
    (hSphere : ∀ w : Complex, riemannZeta w = 0 → dist w c ≠ R)
    (hcne : riemannZeta c ≠ 0) :
    ‖taoZetaLocalFactorProduct c R c‖ ≤ ‖taoZetaAdjustmentProduct c R c‖ := by
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hDc := taoZetaLocalDivisor_center_eq_zero hR.le hAvoid hcne
  have hDnonneg := taoZetaLocalDivisor_nonneg hAvoid
  have hfactor (ρ : Complex) (hρ : ρ ∈ S) :
      ‖(c - ρ) ^ (taoZetaLocalDivisor c R ρ)‖ ≤
        ‖(taoCanonicalAdjustment c R ρ c) ^ (taoZetaLocalDivisor c R ρ)‖ := by
    have hρsupport : ρ ∈ (taoZetaLocalDivisor c R).support := by
      simpa only [S, Set.Finite.mem_toFinset] using hρ
    have hρball := taoZetaLocalDivisor_support_mem_ball_of_sphere_free hAvoid hSphere hρsupport
    have hρc : ρ ≠ c := by
      intro heq
      subst ρ
      exact hρsupport hDc
    have hbase : ‖c - ρ‖ ≤ R := by
      have := mem_ball.mp hρball
      rw [Complex.dist_eq] at this
      simpa only [norm_sub_rev] using this.le
    rw [Complex.norm_zpow, Complex.norm_zpow,
      norm_taoCanonicalAdjustment_apply_center hR]
    exact zpow_le_zpow_left₀ (hDnonneg ρ) (norm_nonneg _) hbase
  have hφeval := congrArg (fun f : Complex → Complex => f c)
    (taoZetaLocalFactorProduct_eq_finset_prod c R)
  simp only [Finset.prod_apply] at hφeval
  unfold taoZetaAdjustmentProduct
  rw [hφeval, Complex.norm_prod, Complex.norm_prod]
  exact Finset.prod_le_prod (fun ρ hρ => norm_nonneg _)
    (fun ρ hρ => hfactor ρ hρ)

end

end Erdos1212Kernel
