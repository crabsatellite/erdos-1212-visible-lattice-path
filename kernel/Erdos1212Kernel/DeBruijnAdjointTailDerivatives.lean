import Erdos1212Kernel.DeBruijnAdjointParameterDerivatives
import Erdos1212Kernel.DeBruijnAdjointPrincipalValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijn1951PositiveTail_hasDerivAt (u : Real) :
    HasDerivAt deBruijn1951PositiveTail
      (∫ z in Set.Ioi (1 : Real), deBruijn1951AdjointNumerator u z) u := by
  let s := Set.Ioo (u - 1) (u + 1)
  let M := |u + 1| + 1
  let bound := fun z : Real => Real.exp (2 * M ^ 2) * Real.exp (-(1 / 8 : Real) * z ^ 2)
  have hs : s ∈ nhds u := Ioo_mem_nhds (by linarith) (by linarith)
  have hFmeas : ∀ᶠ v in nhds u,
      AEStronglyMeasurable (deBruijn1951AdjointDensity v) (volume.restrict (Set.Ioi (1 : Real))) := by
    filter_upwards with v
    exact ((deBruijn1951AdjointNumerator_continuous v).measurable.div measurable_id).aestronglyMeasurable
  have hFint := deBruijn1951AdjointDensity_integrable_positive u (show (0 : Real) < 1 by norm_num)
  have hgauss : IntegrableOn (fun z : Real => Real.exp (-(1 / 8 : Real) * z ^ 2)) (Set.Ioi (1 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 8)).integrableOn
  have hboundInt : IntegrableOn bound (Set.Ioi (1 : Real)) := hgauss.const_mul _
  have hbound : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : Real))), ∀ v ∈ s,
      ‖deBruijn1951AdjointNumerator v z‖ ≤ bound z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    intro v hv
    have hp : 0 ≤ deBruijn1951AdjointNumerator v z := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hp]
    exact deBruijn1951AdjointNumerator_gaussian_bound (by linarith [hz.out]) (deBruijn1951_parameter_abs_le hv)
  have hdiff : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : Real))), ∀ v ∈ s,
      HasDerivAt (fun w => deBruijn1951AdjointDensity w z) (deBruijn1951AdjointNumerator v z) v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    intro v _hv
    exact deBruijn1951AdjointDensity_hasDerivAt_parameter v (by linarith [hz.out])
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : Real))) (F := deBruijn1951AdjointDensity)
    (F' := deBruijn1951AdjointNumerator) (bound := bound) hs hFmeas hFint
    (deBruijn1951AdjointNumerator_continuous u).aestronglyMeasurable hbound hboundInt hdiff).2

theorem deBruijn1951BoundaryKernel_hasDerivAt_parameter (u z : Real) :
    HasDerivAt (fun v : Real => deBruijn1951BoundaryKernel (v + 1) z)
      (-z * deBruijn1951BoundaryKernel (u + 1) z) u := by
  have hinner : HasDerivAt (fun v : Real => -(v + 1) * z) (-z) u := by
    simpa only [Pi.neg_apply, id_eq, neg_one_mul] using ((hasDerivAt_id u).add_const 1).neg.mul_const z
  exact (hinner.exp.mul_const (deBruijn1951Phi z)).congr_deriv (by unfold deBruijn1951BoundaryKernel; ring)

theorem deBruijn1951NegativeTail_integrable_derivative {u : Real} (hu : -1 < u) :
    IntegrableOn (fun z : Real => z * deBruijn1951BoundaryKernel (u + 1) z) (Set.Ioi (1 : Real)) ∧
    HasDerivAt deBruijn1951NegativeTail
      (-(∫ z in Set.Ioi (1 : Real), z * deBruijn1951BoundaryKernel (u + 1) z)) u := by
  let s := Set.Ioo ((u - 1) / 2) (u + 1)
  let b := (u + 1) / 2
  let bound := fun z : Real => deBruijn1951Phi 1 * (z * Real.exp (-b * z))
  let F := fun v z : Real => deBruijn1951BoundaryKernel (v + 1) z
  let F' := fun v z : Real => -z * deBruijn1951BoundaryKernel (v + 1) z
  have hb : 0 < b := by dsimp [b]; linarith
  have hs : s ∈ nhds u := Ioo_mem_nhds (by linarith) (by linarith)
  have hFcont (v : Real) : ContinuousOn (F v) (Set.Ioi (1 : Real)) := by
    apply (deBruijn1951BoundaryKernel_continuousOn (v + 1)).mono
    intro z hz
    change (0 : Real) < z
    linarith [hz.out]
  have hFmeas : ∀ᶠ v in nhds u, AEStronglyMeasurable (F v) (volume.restrict (Set.Ioi (1 : Real))) := by
    filter_upwards with v
    exact (hFcont v).aestronglyMeasurable measurableSet_Ioi
  have hFint : IntegrableOn (F u) (Set.Ioi (1 : Real)) :=
    deBruijn1951BoundaryKernel_integrable (by linarith)
  have hF'meas : AEStronglyMeasurable (F' u) (volume.restrict (Set.Ioi (1 : Real))) :=
    (continuous_neg.continuousOn.mul (hFcont u)).aestronglyMeasurable measurableSet_Ioi
  have hbase0 : IntegrableOn (fun z : Real => z * Real.exp (-b * z)) (Set.Ioi (0 : Real)) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : Real)) (p := (1 : Real)) (by norm_num) le_rfl hb
  have hboundInt : IntegrableOn bound (Set.Ioi (1 : Real)) :=
    (hbase0.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) ≤ 1))).const_mul _
  have hbound : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : Real))), ∀ v ∈ s, ‖F' v z‖ ≤ bound z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    intro v hv
    have hzPos : 0 < z := by linarith [hz.out]
    have hphi := deBruijn1951Phi_pos hzPos
    have hphiLe := (deBruijn1951Phi_bounds (show 1 ≤ z from hz.le)).2
    have hvLower : b ≤ v + 1 := by dsimp [s] at hv; dsimp [b]; linarith [hv.1]
    have he : Real.exp (-(v + 1) * z) ≤ Real.exp (-b * z) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hnonpos : F' v z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hzPos.le) (mul_nonneg (Real.exp_pos _).le hphi.le)
    rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
    change -(-z * (Real.exp (-(v + 1) * z) * deBruijn1951Phi z)) ≤
      deBruijn1951Phi 1 * (z * Real.exp (-b * z))
    calc
      _ = z * Real.exp (-(v + 1) * z) * deBruijn1951Phi z := by ring
      _ ≤ z * Real.exp (-b * z) * deBruijn1951Phi z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hzPos.le) hphi.le
      _ ≤ z * Real.exp (-b * z) * deBruijn1951Phi 1 :=
        mul_le_mul_of_nonneg_left hphiLe (mul_nonneg hzPos.le (Real.exp_pos _).le)
      _ = _ := by ring
  have hdiff : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : Real))), ∀ v ∈ s,
      HasDerivAt (fun w => F w z) (F' v z) v := by
    filter_upwards with z
    intro v _hv
    exact deBruijn1951BoundaryKernel_hasDerivAt_parameter v z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : Real))) (F := F) (F' := F') (bound := bound)
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  constructor
  · apply h.1.neg.congr
    filter_upwards with z
    dsimp [F']
    ring
  · simpa only [F', neg_mul, MeasureTheory.integral_neg] using h.2

theorem deBruijn1951NegativeTail_hasDerivAt {u : Real} (hu : -1 < u) :
    HasDerivAt deBruijn1951NegativeTail
      (-(∫ z in Set.Ioi (1 : Real), z * deBruijn1951BoundaryKernel (u + 1) z)) u :=
  (deBruijn1951NegativeTail_integrable_derivative hu).2

end

end Erdos1212Kernel
