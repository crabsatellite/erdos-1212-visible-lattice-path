import Erdos1212Kernel.DeBruijnExpIntegralBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijn1951AdjointNumerator (u z : Real) : Real :=
  Real.exp ((u + 1) * z - deBruijn1951ExpIntegral z)

def deBruijn1951AdjointDensity (u z : Real) : Real := deBruijn1951AdjointNumerator u z / z

def deBruijn1951SymmetricDensity (u z : Real) : Real :=
  (deBruijn1951AdjointNumerator u z - deBruijn1951AdjointNumerator u (-z)) / z

theorem deBruijn1951AdjointDensity_source (u z : Real) :
    deBruijn1951AdjointDensity u z =
      Real.exp (u * z - deBruijn1951ExpIntegral z) * (Real.exp z / z) := by
  unfold deBruijn1951AdjointDensity deBruijn1951AdjointNumerator
  rw [show (u + 1) * z - deBruijn1951ExpIntegral z = (u * z - deBruijn1951ExpIntegral z) + z by ring,
    Real.exp_add]
  ring

theorem deBruijn1951AdjointDensity_neg (u z : Real) :
    deBruijn1951AdjointDensity u (-z) = -deBruijn1951BoundaryKernel (u + 1) z := by
  unfold deBruijn1951AdjointDensity deBruijn1951AdjointNumerator deBruijn1951BoundaryKernel deBruijn1951Phi
  rw [show (u + 1) * (-z) - deBruijn1951ExpIntegral (-z) =
      -(u + 1) * z + (-deBruijn1951ExpIntegral (-z)) by ring, Real.exp_add]
  ring

theorem deBruijn1951AdjointNumerator_continuous (u : Real) :
    Continuous (deBruijn1951AdjointNumerator u) :=
  Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub deBruijn1951ExpIntegral_continuous)

theorem deBruijn1951AdjointDensity_continuousAt (u : Real) {z : Real} (hz : z ≠ 0) :
    ContinuousAt (deBruijn1951AdjointDensity u) z :=
  (deBruijn1951AdjointNumerator_continuous u).continuousAt.div continuousAt_id hz

theorem deBruijn1951AdjointNumerator_gaussian_bound
    {u z M : Real} (hz : 0 ≤ z) (hM : |u + 1| ≤ M) :
    deBruijn1951AdjointNumerator u z ≤ Real.exp (2 * M ^ 2) * Real.exp (-(1 / 8 : Real) * z ^ 2) := by
  have hphase := deBruijn1951ExpIntegral_quadratic_lower hz
  have hu : u + 1 ≤ M := (le_abs_self (u + 1)).trans hM
  have hmul := mul_le_mul_of_nonneg_right hu hz
  unfold deBruijn1951AdjointNumerator
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (z - 4 * M)]

theorem deBruijn1951AdjointNumerator_integrable (u : Real) :
    IntegrableOn (deBruijn1951AdjointNumerator u) (Set.Ioi (0 : Real)) := by
  have hgauss : IntegrableOn (fun z : Real => Real.exp (-(1 / 8 : Real) * z ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 8)).integrableOn
  have hg := hgauss.const_mul (Real.exp (2 * |u + 1| ^ 2))
  apply hg.mono' (deBruijn1951AdjointNumerator_continuous u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hzPos : 0 < z := hz
  have hnonneg : 0 ≤ deBruijn1951AdjointNumerator u z := (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnonneg]
  exact deBruijn1951AdjointNumerator_gaussian_bound hzPos.le le_rfl

theorem deBruijn1951AdjointDensity_integrable_positive (u : Real) {δ : Real} (hδ : 0 < δ) :
    IntegrableOn (deBruijn1951AdjointDensity u) (Set.Ioi δ) := by
  have hnum := (deBruijn1951AdjointNumerator_integrable u).mono_set (Set.Ioi_subset_Ioi hδ.le)
  apply (hnum.const_mul δ⁻¹).mono'
  · have hc : ContinuousOn (deBruijn1951AdjointDensity u) (Set.Ioi δ) := by
      intro z hz
      exact (deBruijn1951AdjointDensity_continuousAt u (by linarith [hz.out] : z ≠ 0)).continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzPos : 0 < z := hδ.trans hz
    have hp : 0 < deBruijn1951AdjointNumerator u z := Real.exp_pos _
    unfold deBruijn1951AdjointDensity
    rw [Real.norm_of_nonneg (div_pos hp hzPos).le]
    have h := div_le_div_of_nonneg_left hp.le hδ (show δ ≤ z from hz.le)
    simpa only [div_eq_mul_inv, mul_comm] using h

end

end Erdos1212Kernel
