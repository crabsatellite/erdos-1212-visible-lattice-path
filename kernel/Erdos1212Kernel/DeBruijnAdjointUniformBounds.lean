import Erdos1212Kernel.DeBruijnAdjointPrincipalValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def deBruijn1951GaussianMass : Real := ∫ z in Set.Ioi (1 : Real), Real.exp (-(1 / 8 : Real) * z ^ 2)

theorem deBruijn1951GaussianMass_nonneg : 0 ≤ deBruijn1951GaussianMass := by
  exact integral_nonneg (fun _z => (Real.exp_pos _).le)

theorem deBruijn1951PositiveTail_nonneg (u : Real) : 0 ≤ deBruijn1951PositiveTail u := by
  unfold deBruijn1951PositiveTail
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact div_nonneg (show 0 ≤ deBruijn1951AdjointNumerator u z from (Real.exp_pos _).le)
    (show 0 ≤ z by linarith [hz.out])

theorem deBruijn1951PositiveTail_bound {u M : Real} (hM : |u + 1| ≤ M) :
    deBruijn1951PositiveTail u ≤ Real.exp (2 * M ^ 2) * deBruijn1951GaussianMass := by
  have hgauss : IntegrableOn (fun z : Real => Real.exp (-(1 / 8 : Real) * z ^ 2)) (Set.Ioi (1 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 8)).integrableOn
  have hmajor : IntegrableOn (fun z : Real => Real.exp (2 * M ^ 2) * Real.exp (-(1 / 8 : Real) * z ^ 2))
      (Set.Ioi (1 : Real)) := hgauss.const_mul _
  have hi := setIntegral_mono_on
    (deBruijn1951AdjointDensity_integrable_positive u (show (0 : Real) < 1 by norm_num)) hmajor measurableSet_Ioi
    (show ∀ z ∈ Set.Ioi (1 : Real), deBruijn1951AdjointDensity u z ≤
      Real.exp (2 * M ^ 2) * Real.exp (-(1 / 8 : Real) * z ^ 2) from by
      intro z hz
      have hzOne : 1 ≤ z := (show 1 < z from hz).le
      have hp : 0 ≤ deBruijn1951AdjointNumerator u z := (Real.exp_pos _).le
      exact (div_le_self hp hzOne).trans (deBruijn1951AdjointNumerator_gaussian_bound (by linarith) hM))
  rw [MeasureTheory.integral_const_mul] at hi
  exact hi

def deBruijn1951RegularPartBound : Real :=
  deBruijn1951NearBound 1 + Real.exp (2 * (1 : Real) ^ 2) * deBruijn1951GaussianMass

theorem deBruijn1951RegularPartBound_nonneg : 0 ≤ deBruijn1951RegularPartBound := by
  have hg := deBruijn1951GaussianMass_nonneg
  unfold deBruijn1951RegularPartBound deBruijn1951NearBound
  positivity

theorem deBruijn1951RegularPart_bound {a : Real} (ha : a ∈ Set.Ioc (0 : Real) 1) :
    |deBruijn1951NearIntegral (a - 1) + deBruijn1951PositiveTail (a - 1)| ≤ deBruijn1951RegularPartBound := by
  have hM : |a - 1 + 1| ≤ (1 : Real) := by rw [sub_add_cancel, abs_of_pos ha.1]; exact ha.2
  have hn := deBruijn1951NearIntegral_abs_le hM
  have hp := deBruijn1951PositiveTail_bound hM
  have hpAbs : |deBruijn1951PositiveTail (a - 1)| ≤
      Real.exp (2 * (1 : Real) ^ 2) * deBruijn1951GaussianMass := by
    rw [abs_of_nonneg (deBruijn1951PositiveTail_nonneg _)]
    exact hp
  exact (abs_add_le _ _).trans (add_le_add hn hpAbs)

end

end Erdos1212Kernel
