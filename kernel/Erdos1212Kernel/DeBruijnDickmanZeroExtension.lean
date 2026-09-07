import Erdos1212Kernel.IwaniecDickmanPositivity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- The literal zero extension required in de Bruijn 1951, Section 2.
This is distinct from the totalization used to construct the positive-domain rho. -/
def deBruijnRho (s : Real) : Real := (Set.Ici (0 : Real)).indicator iwaniecDickman s

theorem deBruijnRho_eq_dickman {s : Real} (hs : 0 ≤ s) : deBruijnRho s = iwaniecDickman s := by
  exact Set.indicator_of_mem hs _

theorem deBruijnRho_eq_zero {s : Real} (hs : s < 0) : deBruijnRho s = 0 := by
  exact Set.indicator_of_notMem (not_le.mpr hs) _

theorem deBruijnRho_initial {s : Real} (hs : s ∈ Set.Icc (0 : Real) 1) : deBruijnRho s = 1 := by
  rw [deBruijnRho_eq_dickman hs.1, iwaniecDickman_initial hs.2]

theorem deBruijnRho_measurable : Measurable deBruijnRho :=
  iwaniecDickman_continuous.measurable.indicator measurableSet_Ici

theorem deBruijnRho_abs_le_one (s : Real) : |deBruijnRho s| ≤ 1 := by
  by_cases hs : 0 ≤ s
  · rw [deBruijnRho_eq_dickman hs, abs_of_pos (iwaniecDickman_pos hs)]
    exact iwaniecDickman_le_one hs
  · rw [deBruijnRho_eq_zero (lt_of_not_ge hs)]
    norm_num

theorem deBruijnRho_intervalIntegrable (a b : Real) : IntervalIntegrable deBruijnRho volume a b := by
  have hc : IntervalIntegrable (fun _s : Real => (1 : Real)) volume a b := intervalIntegrable_const
  apply hc.mono_fun' deBruijnRho_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using deBruijnRho_abs_le_one s)

theorem deBruijnRho_integral_nonpositive {a b : Real} (hab : a ≤ b) (hb : b ≤ 0) :
    (∫ x in a..b, deBruijnRho x) = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [volume.ae_ne (0 : Real)] with x hx hmem
  rw [Set.uIoc_of_le hab] at hmem
  have hxNeg : x < 0 := lt_of_le_of_ne (hmem.2.trans hb) hx
  exact deBruijnRho_eq_zero hxNeg

theorem deBruijnRho_integral_initial {u : Real} (hu : u ∈ Set.Icc (0 : Real) 1) :
    (∫ x in (0 : Real)..u, deBruijnRho x) = u := by
  have heq : (∫ x in (0 : Real)..u, deBruijnRho x) = ∫ _x in (0 : Real)..u, (1 : Real) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hu.1] at hx
    exact deBruijnRho_initial ⟨hx.1, hx.2.trans hu.2⟩
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using heq

theorem deBruijnRho_window_identity (u : Real) :
    u * deBruijnRho u = ∫ x in (u - 1)..u, deBruijnRho x := by
  by_cases huHigh : 1 ≤ u
  · rw [deBruijnRho_eq_dickman (by linarith : 0 ≤ u), iwaniecDickman_window_identity huHigh]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (show u - 1 ≤ u by linarith)] at hx
    exact (deBruijnRho_eq_dickman (by linarith [hx.1] : 0 ≤ x)).symm
  · by_cases huLow : u ≤ 0
    · rw [deBruijnRho_integral_nonpositive (by linarith) huLow]
      rcases huLow.eq_or_lt with rfl | hneg
      · simp
      · rw [deBruijnRho_eq_zero hneg, mul_zero]
    · have hu : u ∈ Set.Icc (0 : Real) 1 := ⟨(lt_of_not_ge huLow).le, (lt_of_not_ge huHigh).le⟩
      rw [deBruijnRho_initial hu, mul_one]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (deBruijnRho_intervalIntegrable (u - 1) 0) (deBruijnRho_intervalIntegrable 0 u)
      rw [deBruijnRho_integral_nonpositive (by linarith [hu.2]) (by norm_num),
        deBruijnRho_integral_initial hu, zero_add] at hsplit
      exact hsplit

/-- Equation (2.1), including negative u and the discontinuity at zero,
for the actual source zero extension. -/
theorem deBruijnRho_convolution_identity (u : Real) :
    u * deBruijnRho u = ∫ t in (0 : Real)..1, deBruijnRho (u - t) := by
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  exact deBruijnRho_window_identity u

theorem deBruijnRho_continuousOn_positive : ContinuousOn deBruijnRho (Set.Ioi (0 : Real)) := by
  apply iwaniecDickman_continuous.continuousOn.congr
  intro s hs
  exact deBruijnRho_eq_dickman hs.le

end

end Erdos1212Kernel
