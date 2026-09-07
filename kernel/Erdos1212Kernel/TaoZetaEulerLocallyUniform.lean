import Erdos1212Kernel.TaoZetaEulerDomains

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 2000000

theorem taoZetaEulerApprox_tendstoUniformlyOn_compact {K : Set Complex}
    (hK : IsCompact K) (hre : ∀ s ∈ K, 0 < s.re) (hs1 : ∀ s ∈ K, s ≠ 1) :
    TendstoUniformlyOn (fun N s => taoZetaEulerApprox s N) taoZetaEulerLimit atTop K := by
  by_cases hKe : K = ∅
  · subst K
    simp [TendstoUniformlyOn]
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  obtain ⟨s₀, hs₀K, hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  let δ : Real := s₀.re
  have hδ : 0 < δ := hre s₀ hs₀K
  have hδle : ∀ s ∈ K, δ ≤ s.re := fun s hs => hmin hs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hC' : ∀ s ∈ K, ‖s‖ ≤ C := by
    intro s hs
    simpa only [Real.norm_eq_abs, abs_norm] using hC s hs
  have hC0 : 0 ≤ C := by
    obtain ⟨s, hs⟩ := hKne
    exact (norm_nonneg s).trans (hC' s hs)
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let D : Real := C * (1 + 1 / δ)
  have hD : 0 ≤ D := by unfold D; positivity
  have hpow : Tendsto (fun N : Nat => D * (N : Real) ^ (-δ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using tendsto_const_nhds.mul h
  have hsmall : ∀ᶠ N : Nat in atTop, D * (N : Real) ^ (-δ) ≤ ε :=
    ((tendsto_order.1 hpow).2 ε hε).mono (fun _ h => h.le)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hNsmall hN1
  intro s hsK
  rw [dist_eq_norm]
  have hbase := taoZetaEulerLimit_truncation_error (hre s hsK) (hs1 s hsK) N hN1
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN1
  have hsexp : (N : Real) ^ (-s.re) ≤ (N : Real) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hNreal (neg_le_neg (hδle s hsK))
  have hone : 1 + 1 / s.re ≤ 1 + 1 / δ := by
    have hinv := one_div_le_one_div_of_le hδ (hδle s hsK)
    linarith
  have hfactor : ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) ≤
      D * (N : Real) ^ (-δ) := by
    unfold D
    have hp1 := mul_le_mul (hC' s hsK) hsexp (Real.rpow_nonneg (by positivity) _) hC0
    have hone0 : 0 ≤ 1 + 1 / s.re := by positivity [hre s hsK]
    have hCN : 0 ≤ C * (N : Real) ^ (-δ) := mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _)
    have hp2 := mul_le_mul hp1 hone hone0 hCN
    nlinarith
  exact hbase.trans (hfactor.trans hNsmall)

theorem taoZetaEulerApprox_tendstoLocallyUniformlyOn_upper :
    TendstoLocallyUniformlyOn (fun N s => taoZetaEulerApprox s N) taoZetaEulerLimit atTop
      taoZetaUpperDomain := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact taoZetaUpperDomain_isOpen]
  intro K hKU hK
  exact taoZetaEulerApprox_tendstoUniformlyOn_compact hK
    (fun s hs => (hKU hs).1) (fun s hs h => by
      have him := (hKU hs).2
      rw [h] at him
      norm_num at him)

theorem taoZetaEulerApprox_tendstoLocallyUniformlyOn_lower :
    TendstoLocallyUniformlyOn (fun N s => taoZetaEulerApprox s N) taoZetaEulerLimit atTop
      taoZetaLowerDomain := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact taoZetaLowerDomain_isOpen]
  intro K hKU hK
  exact taoZetaEulerApprox_tendstoUniformlyOn_compact hK
    (fun s hs => (hKU hs).1) (fun s hs h => by
      have him := (hKU hs).2
      rw [h] at him
      norm_num at him)

end

end Erdos1212Kernel
