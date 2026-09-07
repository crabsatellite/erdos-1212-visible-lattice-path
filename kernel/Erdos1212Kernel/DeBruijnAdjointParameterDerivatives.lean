import Erdos1212Kernel.DeBruijnAdjointCancellation
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem deBruijn1951_parameter_abs_le {u v : Real}
    (hv : v ∈ Set.Ioo (u - 1) (u + 1)) : |v + 1| ≤ |u + 1| + 1 := by
  have hd : |v - u| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
  calc
    |v + 1| = |(u + 1) + (v - u)| := by congr 1; ring
    _ ≤ |u + 1| + |v - u| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl hd

theorem deBruijn1951AdjointNumerator_near_bound {u z M : Real}
    (hM : |u + 1| ≤ M) (hz : |z| ≤ 1) :
    deBruijn1951AdjointNumerator u z ≤ Real.exp (M + Real.exp 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hT : 0 ≤ M + Real.exp 1 := add_nonneg hM0 (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |(u + 1) * z - deBruijn1951ExpIntegral z| := le_abs_self _
    _ ≤ (M + Real.exp 1) * |z| := deBruijn1951_exponent_abs_le hM hz
    _ ≤ M + Real.exp 1 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hT

theorem deBruijn1951AdjointNumerator_hasDerivAt_parameter (u z : Real) :
    HasDerivAt (fun v : Real => deBruijn1951AdjointNumerator v z)
      (deBruijn1951AdjointNumerator u z * z) u := by
  have h := ((((hasDerivAt_id u).add_const 1).mul_const z).sub_const (deBruijn1951ExpIntegral z)).exp
  simpa only [one_mul, deBruijn1951AdjointNumerator] using h

theorem deBruijn1951AdjointDensity_hasDerivAt_parameter (u : Real) {z : Real} (hz : z ≠ 0) :
    HasDerivAt (fun v : Real => deBruijn1951AdjointDensity v z)
      (deBruijn1951AdjointNumerator u z) u := by
  have h := (deBruijn1951AdjointNumerator_hasDerivAt_parameter u z).div_const z
  simpa only [deBruijn1951AdjointDensity, mul_div_cancel_right₀ _ hz] using h

theorem deBruijn1951SymmetricDensity_hasDerivAt_parameter (u : Real) {z : Real} (hz : z ≠ 0) :
    HasDerivAt (fun v : Real => deBruijn1951SymmetricDensity v z)
      (deBruijn1951AdjointNumerator u z + deBruijn1951AdjointNumerator u (-z)) u := by
  have h := ((deBruijn1951AdjointNumerator_hasDerivAt_parameter u z).sub
    (deBruijn1951AdjointNumerator_hasDerivAt_parameter u (-z))).div_const z
  apply h.congr_deriv
  field_simp
  <;> ring

theorem deBruijn1951NearIntegral_hasDerivAt (u : Real) :
    HasDerivAt deBruijn1951NearIntegral
      (∫ z in (0 : Real)..1, deBruijn1951AdjointNumerator u z + deBruijn1951AdjointNumerator u (-z)) u := by
  let s := Set.Ioo (u - 1) (u + 1)
  let M := |u + 1| + 1
  let bound := fun _z : Real => 2 * Real.exp (M + Real.exp 1)
  let F' := fun v z : Real => deBruijn1951AdjointNumerator v z + deBruijn1951AdjointNumerator v (-z)
  have hs : s ∈ nhds u := Ioo_mem_nhds (by linarith) (by linarith)
  have hFmeas : ∀ᶠ v in nhds u,
      AEStronglyMeasurable (deBruijn1951SymmetricDensity v) (volume.restrict (Set.Ioc (0 : Real) 1)) := by
    filter_upwards with v
    exact (deBruijn1951SymmetricDensity_measurable v).aestronglyMeasurable
  have hFint : IntegrableOn (deBruijn1951SymmetricDensity u) (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (deBruijn1951SymmetricDensity_intervalIntegrable u)
  have hF'cont : Continuous (F' u) :=
    (deBruijn1951AdjointNumerator_continuous u).add
      ((deBruijn1951AdjointNumerator_continuous u).comp continuous_neg)
  have hboundInt : IntegrableOn bound (Set.Ioc (0 : Real) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp _root_.intervalIntegrable_const
  have hbound : ∀ᵐ z ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ v ∈ s, ‖F' v z‖ ≤ bound z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    intro v hv
    have hM : |v + 1| ≤ M := deBruijn1951_parameter_abs_le hv
    have hzAbs : |z| ≤ 1 := by simpa only [abs_of_pos hz.1] using hz.2
    have hnAbs : |-z| ≤ 1 := by simpa only [abs_neg] using hzAbs
    have hnonneg : 0 ≤ F' v z := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg]
    have hp := deBruijn1951AdjointNumerator_near_bound hM hzAbs
    have hn := deBruijn1951AdjointNumerator_near_bound hM hnAbs
    change deBruijn1951AdjointNumerator v z + deBruijn1951AdjointNumerator v (-z) ≤ 2 * Real.exp (M + Real.exp 1)
    linarith
  have hdiff : ∀ᵐ z ∂(volume.restrict (Set.Ioc (0 : Real) 1)), ∀ v ∈ s,
      HasDerivAt (fun w => deBruijn1951SymmetricDensity w z) (F' v z) v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    intro v _hv
    exact deBruijn1951SymmetricDensity_hasDerivAt_parameter v hz.1.ne'
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : Real) 1)) (F := deBruijn1951SymmetricDensity)
    (F' := F') (bound := bound) hs hFmeas hFint hF'cont.aestronglyMeasurable hbound hboundInt hdiff).2
  change HasDerivAt (fun v => ∫ z in (0 : Real)..1, deBruijn1951SymmetricDensity v z) _ u
  simpa only [intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num), F'] using h

end

end Erdos1212Kernel
