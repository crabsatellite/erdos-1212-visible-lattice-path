import Erdos1212Kernel.DeBruijnAdjointDensity
import Erdos1212Kernel.DeBruijnDickmanBoundaryKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijn1951BoundaryKernel_integrable_cut {a δ : Real} (ha : 0 < a) (hδ : 0 < δ) :
    IntegrableOn (deBruijn1951BoundaryKernel a) (Set.Ioi δ) := by
  by_cases hOne : 1 ≤ δ
  · exact (deBruijn1951BoundaryKernel_integrable ha).mono_set (Set.Ioi_subset_Ioi hOne)
  · have hδOne : δ ≤ 1 := (lt_of_not_ge hOne).le
    have hc : ContinuousOn (deBruijn1951BoundaryKernel a) (Set.Icc δ 1) := by
      apply (deBruijn1951BoundaryKernel_continuousOn a).mono
      intro x hx
      exact hδ.trans_le hx.1
    have hfinite : IntervalIntegrable (deBruijn1951BoundaryKernel a) volume δ 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le hδOne] using hc
    have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδOne).mp hfinite
    have hUnion := hIoc.union (deBruijn1951BoundaryKernel_integrable ha)
    simpa only [Set.Ioc_union_Ioi_eq_Ioi hδOne] using hUnion

theorem deBruijn1951AdjointDensity_integrable_negative {u δ : Real} (hu : -1 < u) (hδ : 0 < δ) :
    IntegrableOn (deBruijn1951AdjointDensity u) (Set.Iic (-δ)) := by
  apply ((Measure.measurePreserving_neg (volume : Measure Real)).integrableOn_comp_preimage
    (Homeomorph.neg Real).measurableEmbedding).mp
  have hpre : (fun x : Real => -x) ⁻¹' Set.Iic (-δ) = Set.Ici δ := by ext x; simp
  rw [hpre]
  change IntegrableOn (fun x : Real => deBruijn1951AdjointDensity u (-x)) (Set.Ici δ)
  have hfun : (fun x : Real => deBruijn1951AdjointDensity u (-x)) =
      (fun x : Real => -deBruijn1951BoundaryKernel (u + 1) x) := by
    funext x
    exact deBruijn1951AdjointDensity_neg u x
  rw [hfun]
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    (deBruijn1951BoundaryKernel_integrable_cut (by linarith : 0 < u + 1) hδ).neg

theorem deBruijn1951AdjointDensity_negative_integral (u δ : Real) :
    (∫ z in Set.Iic (-δ), deBruijn1951AdjointDensity u z) =
      -(∫ z in Set.Ioi δ, deBruijn1951BoundaryKernel (u + 1) z) := by
  rw [← integral_comp_neg_Ioi δ (deBruijn1951AdjointDensity u)]
  have hfun : (fun z : Real => deBruijn1951AdjointDensity u (-z)) =
      (fun z : Real => -deBruijn1951BoundaryKernel (u + 1) z) := by
    funext z
    exact deBruijn1951AdjointDensity_neg u z
  rw [hfun, MeasureTheory.integral_neg]

def deBruijn1951PVCutoff (u δ : Real) : Real :=
  (∫ z in Set.Iic (-δ), Real.exp (u * z - deBruijn1951ExpIntegral z) * (Real.exp z / z)) +
    ∫ z in Set.Ioi δ, Real.exp (u * z - deBruijn1951ExpIntegral z) * (Real.exp z / z)

theorem deBruijn1951PVCutoff_eq_density (u δ : Real) :
    deBruijn1951PVCutoff u δ =
      (∫ z in Set.Iic (-δ), deBruijn1951AdjointDensity u z) +
        ∫ z in Set.Ioi δ, deBruijn1951AdjointDensity u z := by
  simp only [deBruijn1951PVCutoff, deBruijn1951AdjointDensity_source]

end

end Erdos1212Kernel
