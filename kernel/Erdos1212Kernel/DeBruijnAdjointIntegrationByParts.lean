import Erdos1212Kernel.DeBruijnAdjointRealAxis

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def deBruijn1951AdjointRealFlux (u z : Real) : Real :=
  u * deBruijn1951AdjointNumerator (u - 1) z - deBruijn1951AdjointDensity u z +
    deBruijn1951AdjointDensity (u - 1) z

theorem deBruijn1951AdjointRealFlux_integrable_positive {u δ : Real} (hu : 0 < u) (hδ : 0 < δ) :
    IntegrableOn (deBruijn1951AdjointRealFlux u) (Set.Ioi δ) := by
  have hA : IntegrableOn (deBruijn1951AdjointNumerator (u - 1)) (Set.Ioi δ) :=
    (deBruijn1951AdjointNumerator_integrable_real (by linarith : -1 < u - 1)).integrableOn
  exact ((hA.const_mul u).sub (deBruijn1951AdjointDensity_integrable_positive u hδ)).add
    (deBruijn1951AdjointDensity_integrable_positive (u - 1) hδ)

theorem deBruijn1951AdjointRealFlux_integrable_negative {u δ : Real} (hu : 0 < u) (hδ : 0 < δ) :
    IntegrableOn (deBruijn1951AdjointRealFlux u) (Set.Iic (-δ)) := by
  have hA : IntegrableOn (deBruijn1951AdjointNumerator (u - 1)) (Set.Iic (-δ)) :=
    (deBruijn1951AdjointNumerator_integrable_real (by linarith : -1 < u - 1)).integrableOn
  exact ((hA.const_mul u).sub (deBruijn1951AdjointDensity_integrable_negative (by linarith : -1 < u) hδ)).add
    (deBruijn1951AdjointDensity_integrable_negative (by linarith : -1 < u - 1) hδ)

theorem deBruijn1951AdjointRealFlux_integral_positive {u δ : Real} (hu : 0 < u) (hδ : 0 < δ) :
    (∫ z in Set.Ioi δ, deBruijn1951AdjointRealFlux u z) = -deBruijn1951AdjointNumerator (u - 1) δ := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (a := δ) (f := deBruijn1951AdjointNumerator (u - 1)) (f' := deBruijn1951AdjointRealFlux u)
    (deBruijn1951AdjointNumerator_continuous (u - 1)).continuousAt.continuousWithinAt
    (fun z hz => deBruijn1951AdjointNumerator_hasDerivAt_real u (by linarith [hz.out]))
    (deBruijn1951AdjointRealFlux_integrable_positive hu hδ) (tendsto_deBruijn1951AdjointNumerator_atTop (u - 1))
  simpa only [zero_sub] using h

theorem deBruijn1951AdjointRealFlux_integral_negative {u δ : Real} (hu : 0 < u) (hδ : 0 < δ) :
    (∫ z in Set.Iic (-δ), deBruijn1951AdjointRealFlux u z) = deBruijn1951AdjointNumerator (u - 1) (-δ) := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto
    (a := -δ) (f := deBruijn1951AdjointNumerator (u - 1)) (f' := deBruijn1951AdjointRealFlux u)
    (deBruijn1951AdjointNumerator_continuous (u - 1)).continuousAt.continuousWithinAt
    (fun z hz => deBruijn1951AdjointNumerator_hasDerivAt_real u (by linarith [hz.out]))
    (deBruijn1951AdjointRealFlux_integrable_negative hu hδ)
    (tendsto_deBruijn1951AdjointNumerator_atBot (by linarith : -1 < u - 1))
  simpa only [sub_zero] using h

def deBruijn1951AdjointMassCutoff (u δ : Real) : Real :=
  (∫ z in Set.Iic (-δ), deBruijn1951AdjointNumerator u z) +
    ∫ z in Set.Ioi δ, deBruijn1951AdjointNumerator u z

/-- Integration by parts on the actual source cutoff, before taking its
principal-value limit. Both finite boundary terms remain in the identity. -/
theorem deBruijn1951Adjoint_cutoff_balance {u δ : Real} (hu : 0 < u) (hδ : 0 < δ) :
    deBruijn1951PVCutoff u δ - deBruijn1951PVCutoff (u - 1) δ =
      u * deBruijn1951AdjointMassCutoff (u - 1) δ + deBruijn1951AdjointNumerator (u - 1) δ -
        deBruijn1951AdjointNumerator (u - 1) (-δ) := by
  have hAn : IntegrableOn (deBruijn1951AdjointNumerator (u - 1)) (Set.Iic (-δ)) :=
    (deBruijn1951AdjointNumerator_integrable_real (by linarith : -1 < u - 1)).integrableOn
  have hAp : IntegrableOn (deBruijn1951AdjointNumerator (u - 1)) (Set.Ioi δ) :=
    (deBruijn1951AdjointNumerator_integrable_real (by linarith : -1 < u - 1)).integrableOn
  have hDn := deBruijn1951AdjointDensity_integrable_negative (by linarith : -1 < u) hδ
  have hDp := deBruijn1951AdjointDensity_integrable_positive u hδ
  have hDn' := deBruijn1951AdjointDensity_integrable_negative (by linarith : -1 < u - 1) hδ
  have hDp' := deBruijn1951AdjointDensity_integrable_positive (u - 1) hδ
  have hn := deBruijn1951AdjointRealFlux_integral_negative hu hδ
  have hp := deBruijn1951AdjointRealFlux_integral_positive hu hδ
  have hFn : IntegrableOn (fun z : Real => u * deBruijn1951AdjointNumerator (u - 1) z -
      deBruijn1951AdjointDensity u z) (Set.Iic (-δ)) := (hAn.const_mul u).sub hDn
  have hFp : IntegrableOn (fun z : Real => u * deBruijn1951AdjointNumerator (u - 1) z -
      deBruijn1951AdjointDensity u z) (Set.Ioi δ) := (hAp.const_mul u).sub hDp
  unfold deBruijn1951AdjointRealFlux at hn hp
  rw [MeasureTheory.integral_add hFn hDn',
    MeasureTheory.integral_sub (hAn.const_mul u) hDn, MeasureTheory.integral_const_mul] at hn
  rw [MeasureTheory.integral_add hFp hDp',
    MeasureTheory.integral_sub (hAp.const_mul u) hDp, MeasureTheory.integral_const_mul] at hp
  rw [deBruijn1951PVCutoff_eq_density, deBruijn1951PVCutoff_eq_density]
  unfold deBruijn1951AdjointMassCutoff
  nlinarith [hn, hp]

end

end Erdos1212Kernel
