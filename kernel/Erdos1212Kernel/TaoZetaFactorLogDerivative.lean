import Erdos1212Kernel.TaoZetaFactorAtCenter

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

def taoZetaDivisorReciprocalSum (c : Complex) (R : Real) : Complex :=
  ∑ ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset,
    ((taoZetaLocalDivisor c R ρ : Int) : Complex) / (c - ρ)

theorem taoZetaLocalFactorProduct_eq_finset_prod (c : Complex) (R : Real) :
    taoZetaLocalFactorProduct c R =
      ∏ ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset,
        (· - ρ) ^ (taoZetaLocalDivisor c R ρ) := by
  unfold taoZetaLocalFactorProduct
  apply finprod_eq_prod_of_mulSupport_subset
  intro ρ hρ
  have hDmem : ρ ∈ (taoZetaLocalDivisor c R).support := by
    show taoZetaLocalDivisor c R ρ ≠ 0
    intro hD
    apply hρ
    funext z
    change (z - ρ) ^ (taoZetaLocalDivisor c R ρ) = 1
    rw [hD]
    simp
  change ρ ∈ (taoZetaLocalDivisor_support_finite c R).toFinset
  rw [Set.Finite.mem_toFinset]
  exact hDmem

theorem taoZetaLocalDivisor_center_eq_zero {c : Complex} {R : Real}
    (hR : 0 ≤ R) (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hcne : riemannZeta c ≠ 0) :
    taoZetaLocalDivisor c R c = 0 := by
  have hcU : c ∈ closedBall c R := by simp [hR]
  unfold taoZetaLocalDivisor
  rw [MeromorphicOn.divisor_apply (analyticOn_riemannZeta.mono hAvoid).meromorphicOn hcU,
    (analyticOn_riemannZeta c (hAvoid c hcU)).meromorphicOrderAt_eq,
    (analyticOn_riemannZeta c (hAvoid c hcU)).analyticOrderAt_eq_zero.mpr hcne]
  simp

/-- Exact multiplicity-weighted logarithmic derivative of the local
zeta factor product at a nonzero center. -/
theorem logDeriv_taoZetaLocalFactorProduct_eq_divisorSum
    {c : Complex} {R : Real} (hR : 0 ≤ R)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hcne : riemannZeta c ≠ 0) :
    logDeriv (taoZetaLocalFactorProduct c R) c =
      taoZetaDivisorReciprocalSum c R := by
  let D := taoZetaLocalDivisor c R
  have hfinite : D.support.Finite := by
    simpa only [D] using taoZetaLocalDivisor_support_finite c R
  let S := (taoZetaLocalDivisor_support_finite c R).toFinset
  have hDc : D c = 0 := by
    simpa only [D] using taoZetaLocalDivisor_center_eq_zero hR hAvoid hcne
  have hfactor_ne (ρ : Complex) (hρ : ρ ∈ S) :
      ((c - ρ) : Complex) ^ (D ρ) ≠ 0 := by
    by_cases hρc : ρ = c
    · subst ρ
      rw [hDc]
      simp
    · exact zpow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hρc))
  have hfactor_diff (ρ : Complex) (hρ : ρ ∈ S) :
      DifferentiableAt Complex (fun z : Complex => (z - ρ) ^ (D ρ)) c := by
    by_cases hρc : ρ = c
    · subst ρ
      rw [hDc]
      simp
    · exact (differentiableAt_zpow.2 (Or.inl (sub_ne_zero.mpr (Ne.symm hρc)))).comp c
        (differentiableAt_id.sub_const ρ)
  rw [taoZetaLocalFactorProduct_eq_finset_prod]
  have hfun : (∏ ρ ∈ S, ((fun z : Complex => z - ρ) ^ (D ρ))) =
      (fun z => ∏ ρ ∈ S, (z - ρ) ^ (D ρ)) := by
    funext z
    simp
  dsimp only [S, D] at hfun
  rw [hfun]
  change logDeriv (fun z => ∏ ρ ∈ S, (z - ρ) ^ (D ρ)) c =
    taoZetaDivisorReciprocalSum c R
  rw [logDeriv_prod (s := S) (f := fun ρ z => (z - ρ) ^ (D ρ))
    (fun ρ hρ => hfactor_ne ρ hρ) (fun ρ hρ => hfactor_diff ρ hρ)]
  unfold taoZetaDivisorReciprocalSum
  change (∑ ρ ∈ S, logDeriv (fun z => (z - ρ) ^ (D ρ)) c) =
    ∑ ρ ∈ S, ((D ρ : Int) : Complex) / (c - ρ)
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [logDeriv_fun_zpow (by fun_prop : DifferentiableAt Complex (fun z : Complex => z - ρ) c)]
  unfold logDeriv
  simp only [Pi.div_apply]
  rw [deriv_sub_const]
  rw [show deriv (fun z : Complex => z) c = 1 by simpa using (deriv_id (x := c))]
  ring

/-- Exact nearby-zero expansion before the quantitative Borel bound on
the zero-free residual. -/
theorem exists_taoZetaNearbyExpansion_exact
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hcne : riemannZeta c ≠ 0) :
    ∃ g : Complex → Complex,
      AnalyticOnNhd Complex g (closedBall c R) ∧
      (∀ u : (closedBall c R : Set Complex), g u ≠ 0) ∧
      taoZetaLogDerivative c + taoZetaDivisorReciprocalSum c R =
        -logDeriv g c := by
  obtain ⟨g, hg, hgn, _hlocal, hdecomp⟩ :=
    exists_taoZetaLocalZeroFreeFactor_at_center hR hAvoid hcne
  refine ⟨g, hg, hgn, ?_⟩
  rw [hdecomp, logDeriv_taoZetaLocalFactorProduct_eq_divisorSum hR.le hAvoid hcne]
  ring

end

end Erdos1212Kernel
