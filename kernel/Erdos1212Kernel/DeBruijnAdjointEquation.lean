import Erdos1212Kernel.DeBruijnAdjointIntegrationByParts

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijn1951AdjointMassCutoff_eq {u : Real} (hu : -1 < u) (δ : Real) :
    deBruijn1951AdjointMassCutoff u δ = deBruijn1951AdjointMass u -
      ∫ z in (-δ)..δ, deBruijn1951AdjointNumerator u z := by
  have hi := deBruijn1951AdjointNumerator_integrable_real hu
  have hleft : IntegrableOn (deBruijn1951AdjointNumerator u) (Set.Iic (-δ)) := hi.integrableOn
  have hright : IntegrableOn (deBruijn1951AdjointNumerator u) (Set.Ioi (-δ)) := hi.integrableOn
  have hright' : IntegrableOn (deBruijn1951AdjointNumerator u) (Set.Ioi δ) := hi.integrableOn
  have ht := integral_Iic_add_Ioi hleft hright
  have hs := intervalIntegral.integral_interval_add_Ioi hright hright'
  unfold deBruijn1951AdjointMassCutoff deBruijn1951AdjointMass
  linarith

theorem tendsto_deBruijn1951AdjointNumerator_small_interval (u : Real) :
    Tendsto (fun δ : Real => ∫ z in (-δ)..δ, deBruijn1951AdjointNumerator u z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hc := deBruijn1951AdjointNumerator_continuous u
  have hP : Continuous (fun x : Real => ∫ z in (0 : Real)..x, deBruijn1951AdjointNumerator u z) :=
    intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0
  have h0 := (hP.sub (hP.comp continuous_neg)).tendsto (0 : Real)
  simp only [Function.comp_apply, neg_zero, intervalIntegral.integral_same, sub_self] at h0
  apply (h0.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards with δ
  exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 δ) (hc.intervalIntegrable 0 (-δ))

theorem tendsto_deBruijn1951AdjointMassCutoff {u : Real} (hu : -1 < u) :
    Tendsto (deBruijn1951AdjointMassCutoff u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951AdjointMass u)) := by
  have h := (tendsto_const_nhds (x := deBruijn1951AdjointMass u)).sub
    (tendsto_deBruijn1951AdjointNumerator_small_interval u)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with δ
  exact (deBruijn1951AdjointMassCutoff_eq hu δ).symm

theorem deBruijn1951Adjoint_mass_balance {u : Real} (hu : 0 < u) :
    u * deBruijn1951AdjointMass (u - 1) = deBruijn1951G1 u - deBruijn1951G1 (u - 1) := by
  have hleft := (deBruijn1951_principalValue (by linarith : -1 < u)).sub
    (deBruijn1951_principalValue (by linarith : -1 < u - 1))
  have hc := deBruijn1951AdjointNumerator_continuous (u - 1)
  have hp : Tendsto (deBruijn1951AdjointNumerator (u - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deBruijn1951AdjointNumerator (u - 1) 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun δ : Real => deBruijn1951AdjointNumerator (u - 1) (-δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951AdjointNumerator (u - 1) 0)) := by
    have hcn : Continuous (fun δ : Real => deBruijn1951AdjointNumerator (u - 1) (-δ)) := hc.comp continuous_neg
    simpa only [neg_zero] using (hcn.tendsto (0 : Real)).mono_left
      (show nhdsWithin (0 : Real) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hright := (((tendsto_deBruijn1951AdjointMassCutoff (by linarith : -1 < u - 1)).const_mul u).add hp).sub hn
  simp only [add_sub_cancel_right] at hright
  have hr : Tendsto (fun δ : Real => deBruijn1951PVCutoff u δ - deBruijn1951PVCutoff (u - 1) δ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u * deBruijn1951AdjointMass (u - 1))) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (deBruijn1951Adjoint_cutoff_balance hu hδ).symm
  exact tendsto_nhds_unique hr hleft

/-- De Bruijn 1951, equation (2.7), for the G1 defined by the literal
principal value (2.9), with no auxiliary solution assumed. -/
theorem deBruijn1951G1_adjoint_equation {u : Real} (hu : 0 < u) :
    u * deriv deBruijn1951G1 (u - 1) = deBruijn1951G1 u - deBruijn1951G1 (u - 1) := by
  rw [(deBruijn1951G1_hasDerivAt (by linarith : -1 < u - 1)).deriv]
  exact deBruijn1951Adjoint_mass_balance hu

end

end Erdos1212Kernel
