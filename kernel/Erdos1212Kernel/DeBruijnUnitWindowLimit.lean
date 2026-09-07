import Erdos1212Kernel.DeBruijnF1SaddlePieces

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

/-- A genuine unit-window integral limit, retaining the moving endpoints. -/
theorem deBruijn_unit_window_integral_limit {f : Real → Real} {L : Real}
    (hf : Tendsto f atTop (nhds L))
    (hi : ∀ᶠ a : Real in atTop, IntervalIntegrable f volume (a - 1) a) :
    Tendsto (fun a : Real => ∫ x in (a - 1)..a, f x) atTop (nhds L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hf (ε / 2) (half_pos hε)
  obtain ⟨B, hB⟩ := eventually_atTop.mp hi
  refine ⟨max (A + 1) B, fun a ha => ?_⟩
  have haA : A + 1 ≤ a := (le_max_left _ _).trans ha
  have haB : B ≤ a := (le_max_right _ _).trans ha
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := a - 1) (b := a) (C := ε / 2)
    (f := fun x : Real => f x - L) (by
      intro x hx
      rw [Set.uIoc_of_le (by linarith : a - 1 ≤ a)] at hx
      have hxA : A ≤ x := by linarith [hx.1]
      simpa only [Real.norm_eq_abs, Real.dist_eq] using (hA x hxA).le)
  rw [intervalIntegral.integral_sub (hB a haB) _root_.intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, show a - (a - 1) = 1 by ring, one_mul, abs_one, mul_one] at hn
  rw [Real.norm_eq_abs] at hn
  rw [Real.dist_eq]
  exact hn.trans_lt (by linarith)

end

end Erdos1212Kernel
