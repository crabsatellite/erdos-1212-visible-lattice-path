import Erdos1212Kernel.DeBruijnDickmanZeroExtension

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- De Bruijn 1950 (4.4), with the support convention (1.2). -/
def deBruijnRhoVolterraKernel (x t : Real) : Real :=
  (Set.Icc (0 : Real) 1).indicator (fun t => deBruijnRho (x - t) / (x * deBruijnRho x)) t

theorem deBruijnRhoVolterraKernel_source (x : Real) {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    deBruijnRhoVolterraKernel x t = deBruijnRho (x - t) / (x * deBruijnRho x) :=
  Set.indicator_of_mem ht _

theorem deBruijnRhoVolterraKernel_zero (x : Real) {t : Real} (ht : t ∉ Set.Icc (0 : Real) 1) :
    deBruijnRhoVolterraKernel x t = 0 := Set.indicator_of_notMem ht _

theorem deBruijnRhoVolterraKernel_eq_dickman {x t : Real} (hx : 1 ≤ x) (ht : t ∈ Set.Icc (0 : Real) 1) :
    deBruijnRhoVolterraKernel x t = iwaniecDickman (x - t) / (x * iwaniecDickman x) := by
  rw [deBruijnRhoVolterraKernel_source x ht,
    deBruijnRho_eq_dickman (by linarith [ht.2] : 0 ≤ x - t),
    deBruijnRho_eq_dickman (by linarith : 0 ≤ x)]

theorem deBruijnRhoVolterraKernel_continuousOn {x : Real} (hx : 1 ≤ x) :
    ContinuousOn (deBruijnRhoVolterraKernel x) (Set.Icc (0 : Real) 1) := by
  have hc : Continuous (fun t : Real => iwaniecDickman (x - t) / (x * iwaniecDickman x)) :=
    (iwaniecDickman_continuous.comp (continuous_const.sub continuous_id)).div_const _
  apply hc.continuousOn.congr
  intro t ht
  exact deBruijnRhoVolterraKernel_eq_dickman hx ht

theorem deBruijnRhoVolterraKernel_intervalIntegrable {x : Real} (hx : 1 ≤ x) :
    IntervalIntegrable (deBruijnRhoVolterraKernel x) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using deBruijnRhoVolterraKernel_continuousOn hx

theorem deBruijnRhoVolterraKernel_pos {x t : Real} (hx : 1 ≤ x) (ht : t ∈ Set.Icc (0 : Real) 1) :
    0 < deBruijnRhoVolterraKernel x t := by
  rw [deBruijnRhoVolterraKernel_eq_dickman hx ht]
  exact div_pos (iwaniecDickman_pos (by linarith [ht.2]))
    (mul_pos (by linarith) (iwaniecDickman_pos (by linarith)))

theorem deBruijnRhoVolterraKernel_nonneg {x : Real} (hx : 1 ≤ x) (t : Real) :
    0 ≤ deBruijnRhoVolterraKernel x t := by
  by_cases ht : t ∈ Set.Icc (0 : Real) 1
  · exact (deBruijnRhoVolterraKernel_pos hx ht).le
  · rw [deBruijnRhoVolterraKernel_zero x ht]

theorem deBruijnRhoVolterraKernel_integral {x : Real} (hx : 1 ≤ x) :
    (∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t) = 1 := by
  have heq : (∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t) =
      ∫ t in (0 : Real)..1, deBruijnRho (x - t) / (x * deBruijnRho x) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
    exact deBruijnRhoVolterraKernel_source x ht
  rw [heq, intervalIntegral.integral_div, ← deBruijnRho_convolution_identity x,
    deBruijnRho_eq_dickman (by linarith : 0 ≤ x)]
  exact div_self (mul_ne_zero (by linarith) (iwaniecDickman_pos (by linarith)).ne')

theorem deBruijnRhoVolterraKernel_lower {x t : Real} (hx : 1 ≤ x) (ht : t ∈ Set.Icc (0 : Real) 1) :
    1 / x ≤ deBruijnRhoVolterraKernel x t := by
  have hxPos : 0 < x := by linarith
  have hp := iwaniecDickman_pos hxPos.le
  have hmono := iwaniecDickman_antitoneOn (by linarith [ht.2] : 0 ≤ x - t) hxPos.le (by linarith [ht.1] : x - t ≤ x)
  rw [deBruijnRhoVolterraKernel_eq_dickman hx ht]
  calc
    1 / x = iwaniecDickman x / (x * iwaniecDickman x) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hmono (mul_pos hxPos hp).le

theorem deBruijnRhoVolterraKernel_monotoneOn {x : Real} (hx : 1 ≤ x) :
    MonotoneOn (deBruijnRhoVolterraKernel x) (Set.Icc (0 : Real) 1) := by
  intro s hs t ht hst
  rw [deBruijnRhoVolterraKernel_eq_dickman hx hs, deBruijnRhoVolterraKernel_eq_dickman hx ht]
  apply div_le_div_of_nonneg_right
  · exact iwaniecDickman_antitoneOn (by linarith [ht.2] : 0 ≤ x - t)
      (by linarith [hs.2] : 0 ≤ x - s) (by linarith)
  · exact (mul_pos (by linarith : 0 < x) (iwaniecDickman_pos (by linarith))).le

end

end Erdos1212Kernel
