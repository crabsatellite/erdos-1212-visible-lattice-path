import Erdos1212Kernel.TaoShiftDifferenceCalculus

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1500000

theorem taoShiftDifference_integral_bounds (g : Real → Real) {L U h x δ D : Real}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hc : ContinuousOn g (Set.Icc L U))
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |g t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |g t| ≤ D) (hx : x ∈ Set.Icc L (U - h)) :
    h * δ ≤ |∫ t in x..x + h, g t| ∧ |∫ t in x..x + h, g t| ≤ h * D := by
  have hsub := taoShiftDifference_subinterval hh hx
  have hle : x ≤ x + h := by linarith
  have hc' := hc.mono hsub
  have hint : IntervalIntegrable g volume x (x + h) := hc'.intervalIntegrable_of_Icc hle
  have habsint : IntervalIntegrable (fun t => |g t|) volume x (x + h) :=
    hc'.abs.intervalIntegrable_of_Icc hle
  have hconst (c : Real) : (∫ _t in x..x + h, c) = h * c := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, show x + h - x = h by ring]
  constructor
  · rcases taoShiftDifference_derivative_sign g hδ hc hlow with hp | hn
    · have hmono := intervalIntegral.integral_mono_on hle (intervalIntegrable_const) hint
        (fun t ht => hp t (hsub ht))
      rw [hconst δ] at hmono
      exact hmono.trans (le_abs_self _)
    · have hmono := intervalIntegral.integral_mono_on hle hint (intervalIntegrable_const)
        (fun t ht => hn t (hsub ht))
      rw [hconst (-δ)] at hmono
      have habs := neg_le_abs (∫ t in x..x + h, g t)
      nlinarith
  · have hmono := intervalIntegral.integral_mono_on hle habsint (intervalIntegrable_const)
      (fun t ht => hhigh t (hsub ht))
    rw [hconst D] at hmono
    exact (intervalIntegral.abs_integral_le_integral_abs hle).trans hmono

/-- The original FTC transport preserves both derivative bounds and the
factor h, including h=0, with no extension beyond the overlap interval. -/
theorem taoShiftDifference_bounds (f f' : Real → Real) {L U h x δ D : Real}
    (hδ : 0 < δ) (hh : 0 ≤ h)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Set.Icc L U))
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ D) (hx : x ∈ Set.Icc L (U - h)) :
    h * δ ≤ |taoShiftDifference f h x| ∧ |taoShiftDifference f h x| ≤ h * D := by
  rw [taoShiftDifference_eq_integral f f' hh hf hc hx]
  exact taoShiftDifference_integral_bounds f' hδ hh hc hlow hhigh hx

end

end Erdos1212Kernel
