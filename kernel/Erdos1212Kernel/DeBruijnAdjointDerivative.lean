import Erdos1212Kernel.DeBruijnAdjointTailDerivatives

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijn1951AdjointNumerator_neg (u : Real) {z : Real} (hz : z ≠ 0) :
    deBruijn1951AdjointNumerator u (-z) = z * deBruijn1951BoundaryKernel (u + 1) z := by
  unfold deBruijn1951AdjointNumerator deBruijn1951BoundaryKernel deBruijn1951Phi
  rw [show (u + 1) * (-z) - deBruijn1951ExpIntegral (-z) =
      -(u + 1) * z + (-deBruijn1951ExpIntegral (-z)) by ring, Real.exp_add]
  field_simp

theorem deBruijn1951AdjointNumerator_reflected_tail_integrable {u : Real} (hu : -1 < u) :
    IntegrableOn (fun z : Real => deBruijn1951AdjointNumerator u (-z)) (Set.Ioi (1 : Real)) := by
  apply (deBruijn1951NegativeTail_integrable_derivative hu).1.congr_fun _ measurableSet_Ioi
  intro z hz
  exact (deBruijn1951AdjointNumerator_neg u (by linarith [hz.out])).symm

theorem deBruijn1951AdjointNumerator_reflected_integrable {u : Real} (hu : -1 < u) :
    IntegrableOn (fun z : Real => deBruijn1951AdjointNumerator u (-z)) (Set.Ioi (0 : Real)) := by
  have hnear : IntervalIntegrable (fun z : Real => deBruijn1951AdjointNumerator u (-z)) volume 0 1 :=
    ((deBruijn1951AdjointNumerator_continuous u).comp continuous_neg).intervalIntegrable 0 1
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : Real) ≤ 1)).mp hnear
  have hi := hIoc.union (deBruijn1951AdjointNumerator_reflected_tail_integrable hu)
  simpa only [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) ≤ 1)] using hi

theorem deBruijn1951AdjointNumerator_integrable_negative {u : Real} (hu : -1 < u) :
    IntegrableOn (deBruijn1951AdjointNumerator u) (Set.Iic (0 : Real)) := by
  apply ((Measure.measurePreserving_neg (volume : Measure Real)).integrableOn_comp_preimage
    (Homeomorph.neg Real).measurableEmbedding).mp
  have hpre : (fun x : Real => -x) ⁻¹' Set.Iic (0 : Real) = Set.Ici (0 : Real) := by ext x; simp
  rw [hpre]
  change IntegrableOn (fun x : Real => deBruijn1951AdjointNumerator u (-x)) (Set.Ici (0 : Real))
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    (deBruijn1951AdjointNumerator_reflected_integrable hu)

theorem deBruijn1951AdjointNumerator_integrable_real {u : Real} (hu : -1 < u) :
    Integrable (deBruijn1951AdjointNumerator u) := by
  have h := (deBruijn1951AdjointNumerator_integrable_negative hu).union
    (deBruijn1951AdjointNumerator_integrable u)
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h

def deBruijn1951AdjointMass (u : Real) : Real := ∫ z : Real, deBruijn1951AdjointNumerator u z

theorem deBruijn1951AdjointMass_decomposition {u : Real} (hu : -1 < u) :
    deBruijn1951AdjointMass u =
      (∫ z in (0 : Real)..1, deBruijn1951AdjointNumerator u z + deBruijn1951AdjointNumerator u (-z)) +
      (∫ z in Set.Ioi (1 : Real), deBruijn1951AdjointNumerator u z) +
      (∫ z in Set.Ioi (1 : Real), z * deBruijn1951BoundaryKernel (u + 1) z) := by
  have hp := deBruijn1951AdjointNumerator_integrable u
  have hn := deBruijn1951AdjointNumerator_reflected_integrable hu
  have hp1 := hp.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) ≤ 1))
  have hn1 := deBruijn1951AdjointNumerator_reflected_tail_integrable hu
  have hsp := intervalIntegral.integral_interval_add_Ioi hp hp1
  have hsn := intervalIntegral.integral_interval_add_Ioi hn hn1
  have hnearP : IntervalIntegrable (deBruijn1951AdjointNumerator u) volume 0 1 :=
    (deBruijn1951AdjointNumerator_continuous u).intervalIntegrable 0 1
  have hnearN : IntervalIntegrable (fun z : Real => deBruijn1951AdjointNumerator u (-z)) volume 0 1 :=
    ((deBruijn1951AdjointNumerator_continuous u).comp continuous_neg).intervalIntegrable 0 1
  have hreflection := integral_comp_neg_Ioi (0 : Real) (deBruijn1951AdjointNumerator u)
  simp only [neg_zero] at hreflection
  have htail : (∫ z in Set.Ioi (1 : Real), deBruijn1951AdjointNumerator u (-z)) =
      ∫ z in Set.Ioi (1 : Real), z * deBruijn1951BoundaryKernel (u + 1) z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    exact deBruijn1951AdjointNumerator_neg u (by linarith [hz.out])
  unfold deBruijn1951AdjointMass
  rw [← integral_Iic_add_Ioi (deBruijn1951AdjointNumerator_integrable_negative hu) hp,
    ← hreflection, ← hsp, ← hsn, htail,
    intervalIntegral.integral_add hnearP hnearN]
  ring

/-- Differentiation of the actual source principal value on its full domain.
The parameter derivative has no pole and is absolutely integrable. -/
theorem deBruijn1951G1_hasDerivAt {u : Real} (hu : -1 < u) :
    HasDerivAt deBruijn1951G1 (deBruijn1951AdjointMass u) u := by
  have h := ((deBruijn1951NearIntegral_hasDerivAt u).add (deBruijn1951PositiveTail_hasDerivAt u)).sub
    (deBruijn1951NegativeTail_hasDerivAt hu)
  simp only [sub_neg_eq_add] at h
  rw [← deBruijn1951AdjointMass_decomposition hu] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact deBruijn1951G1_eq_regularized hv

theorem deBruijn1951G1_continuousOn : ContinuousOn deBruijn1951G1 (Set.Ioi (-1 : Real)) := by
  intro u hu
  exact (deBruijn1951G1_hasDerivAt hu).continuousAt.continuousWithinAt

end

end Erdos1212Kernel
