import Erdos1212Kernel.TaoZetaDivisorFactor

namespace Erdos1212Kernel

noncomputable section

open Metric Filter
open scoped Topology

set_option maxHeartbeats 1900000

theorem eventuallyEq_nhdsNE_of_codiscreteWithin
    {f g : Complex → Complex} {U : Set Complex} {c : Complex}
    (hEq : f =ᶠ[codiscreteWithin U] g) (hc : c ∈ U) (hU : U ∈ 𝓝 c) :
    f =ᶠ[𝓝[≠] c] g := by
  rw [EventuallyEq, Filter.Eventually] at hEq ⊢
  have hcod := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hEq c hc
  have hUnhds : U ∈ 𝓝[≠] c := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨U, hU, Set.inter_subset_left⟩
  filter_upwards [hcod, hUnhds] with z hzEq hzU
  rcases hzEq with hzEq | hzComp
  · exact hzEq
  · exact False.elim (hzComp hzU)

/-- The multiplicity-preserving factor extraction is upgraded at an
interior nonzero center from codiscrete equality to actual local
equality, and hence to a logarithmic-derivative identity. -/
theorem exists_taoZetaLocalZeroFreeFactor_at_center
    {c : Complex} {R : Real} (hR : 0 < R)
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hcne : riemannZeta c ≠ 0) :
    ∃ g : Complex → Complex,
      AnalyticOnNhd Complex g (closedBall c R) ∧
      (∀ u : (closedBall c R : Set Complex), g u ≠ 0) ∧
      riemannZeta =ᶠ[𝓝 c]
        (fun z => taoZetaLocalFactorProduct c R z * g z) ∧
      taoZetaLogDerivative c =
        -(logDeriv (taoZetaLocalFactorProduct c R) c + logDeriv g c) := by
  obtain ⟨g, hg, hgn, hEq⟩ := exists_taoZetaLocalZeroFreeFactor hAvoid
  let D := taoZetaLocalDivisor c R
  let φ := taoZetaLocalFactorProduct c R
  have hcU : c ∈ closedBall c R := by simp [hR.le]
  have hDzero : D c = 0 := by
    unfold D taoZetaLocalDivisor
    rw [MeromorphicOn.divisor_apply (analyticOn_riemannZeta.mono hAvoid).meromorphicOn hcU,
      (analyticOn_riemannZeta c (hAvoid c hcU)).meromorphicOrderAt_eq,
      (analyticOn_riemannZeta c (hAvoid c hcU)).analyticOrderAt_eq_zero.mpr hcne]
    simp
  have hfinite : D.support.Finite := by
    simpa only [D] using taoZetaLocalDivisor_support_finite c R
  have hφNF : MeromorphicNFAt φ c := by
    unfold φ taoZetaLocalFactorProduct
    exact Function.FactorizedRational.meromorphicNFOn_univ D (by trivial)
  have hφorder : meromorphicOrderAt φ c = 0 := by
    unfold φ taoZetaLocalFactorProduct
    rw [Function.FactorizedRational.meromorphicOrderAt_eq D hfinite, hDzero]
    norm_num
  have hφan : AnalyticAt Complex φ c :=
    hφNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hφorder])
  have hφne : φ c ≠ 0 := hφNF.meromorphicOrderAt_eq_zero_iff.mp hφorder
  let p : Complex → Complex := fun z => φ z * g z
  have hpan : AnalyticAt Complex p c := hφan.mul (hg c hcU)
  have hcod : riemannZeta =ᶠ[codiscreteWithin (closedBall c R)] p := by
    simpa only [p, φ, Pi.smul_apply, smul_eq_mul] using hEq
  have hU : closedBall c R ∈ 𝓝 c :=
    Filter.mem_of_superset (ball_mem_nhds c hR) ball_subset_closedBall
  have hpunct := eventuallyEq_nhdsNE_of_codiscreteWithin hcod hcU hU
  have hfreq : ∃ᶠ z in 𝓝[≠] c, riemannZeta z = p z := hpunct.frequently
  have hzetaAn : AnalyticAt Complex riemannZeta c := analyticOn_riemannZeta c (hAvoid c hcU)
  have hlocal : riemannZeta =ᶠ[𝓝 c] p :=
    (hzetaAn.frequently_eq_iff_eventually_eq hpan).mp hfreq
  have hlogEq : logDeriv riemannZeta c = logDeriv p c := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hlocal.deriv_eq, hlocal.self_of_nhds]
  have hgc : g c ≠ 0 := hgn ⟨c, hcU⟩
  have hprod : logDeriv p c = logDeriv φ c + logDeriv g c := by
    unfold p
    exact logDeriv_mul c hφne hgc hφan.differentiableAt (hg c hcU).differentiableAt
  refine ⟨g, hg, hgn, ?_, ?_⟩
  · simpa only [p, φ] using hlocal
  · unfold taoZetaLogDerivative
    have htao : -deriv riemannZeta c / riemannZeta c = -logDeriv riemannZeta c := by
      unfold logDeriv
      simp only [Pi.div_apply]
      ring
    rw [htao, hlogEq, hprod]

end

end Erdos1212Kernel
