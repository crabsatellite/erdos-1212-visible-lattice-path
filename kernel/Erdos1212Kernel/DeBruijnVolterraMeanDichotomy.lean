import Erdos1212Kernel.DeBruijnVolterraWindowMean

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnVolterraWindowMean_deriv_bound {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n x : Real} (hn : 1 ≤ n) (hx : x ∈ Set.Ioo n (n + 2)) :
    |deriv (deBruijnVolterraWindowMean f) x| ≤ deBruijnVolterraOscillation f n := by
  rw [(deBruijnVolterraWindowMean_hasDerivAt hf (by linarith [hx.1] : 1 < x)).deriv]
  have hb := deBruijnVolterraWindow_future_bounds hf heq hn x (by linarith [hx.1])
  have hb' := deBruijnVolterraWindow_future_bounds hf heq hn (x - 1) (by linarith [hx.1])
  apply abs_le.mpr
  unfold deBruijnVolterraOscillation
  constructor <;> linarith [hb.1, hb.2, hb'.1, hb'.2]

theorem deBruijnVolterraWindowMean_lipschitz {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n x y : Real} (hn : 1 ≤ n) (hx : x ∈ Set.Icc n (n + 2)) (hy : y ∈ Set.Icc n (n + 2)) :
    |deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMean f y| ≤ deBruijnVolterraOscillation f n * |x - y| := by
  have hc := deBruijnVolterraWindowMean_continuousOn_segment hf hn
  have hd : DifferentiableOn Real (deBruijnVolterraWindowMean f) (interior (Set.Icc n (n + 2))) := by
    intro z hz
    rw [interior_Icc] at hz
    exact (deBruijnVolterraWindowMean_hasDerivAt hf (by linarith [hz.1])).differentiableAt.differentiableWithinAt
  have hbound : ∀ z ∈ interior (Set.Icc n (n + 2)),
      |deriv (deBruijnVolterraWindowMean f) z| ≤ deBruijnVolterraOscillation f n := by
    intro z hz
    rw [interior_Icc] at hz
    exact deBruijnVolterraWindowMean_deriv_bound hf heq hn hz
  have ordered : ∀ x ∈ Set.Icc n (n + 2), ∀ y ∈ Set.Icc n (n + 2), x ≤ y →
      |deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMean f y| ≤ deBruijnVolterraOscillation f n * (y - x) := by
    intro x hx y hy hxy
    have hup := (convex_Icc n (n + 2)).image_sub_le_mul_sub_of_deriv_le hc hd
      (fun z hz => (abs_le.mp (hbound z hz)).2) x hx y hy hxy
    have hlo := (convex_Icc n (n + 2)).mul_sub_le_image_sub_of_le_deriv hc hd
      (fun z hz => (abs_le.mp (hbound z hz)).1) x hx y hy hxy
    apply abs_le.mpr
    constructor <;> nlinarith
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    convert ordered x hx y hy hxy using 1 <;> ring
  · rw [abs_sub_comm (deBruijnVolterraWindowMean f x) (deBruijnVolterraWindowMean f y), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact ordered y hy x hx hyx

/-- The exact low-mean/high-mean unit-window dichotomy of 1950 Lemma 1.
The effective extrema and the source quarter-oscillation are unchanged. -/
theorem deBruijnVolterra_mean_dichotomy {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n : Real} (hn : 1 ≤ n) :
    ∃ y ∈ Set.Icc (n + 1) (n + 2),
      (∀ x ∈ Set.Icc (y - 1) y, deBruijnVolterraWindowMean f x ≤
        deBruijnVolterraWindowMax f n - deBruijnVolterraOscillation f n / 4) ∨
      (∀ x ∈ Set.Icc (y - 1) y, deBruijnVolterraWindowMin f n +
        deBruijnVolterraOscillation f n / 4 ≤ deBruijnVolterraWindowMean f x) := by
  by_cases hlow : ∃ y ∈ Set.Icc (n + 1) (n + 2), ∀ x ∈ Set.Icc (y - 1) y,
      deBruijnVolterraWindowMean f x ≤ deBruijnVolterraWindowMax f n - deBruijnVolterraOscillation f n / 4
  · obtain ⟨y, hy, hmean⟩ := hlow
    exact ⟨y, hy, Or.inl hmean⟩
  · have hnot : ¬ ∀ x ∈ Set.Icc (n + 3 / 2 - 1) (n + 3 / 2),
        deBruijnVolterraWindowMean f x ≤ deBruijnVolterraWindowMax f n - deBruijnVolterraOscillation f n / 4 := by
      intro h
      exact hlow ⟨n + 3 / 2, ⟨by linarith, by linarith⟩, h⟩
    push_neg at hnot
    obtain ⟨x₀, hx₀, hmean₀⟩ := hnot
    have hx₀n : x₀ ∈ Set.Icc n (n + 2) := ⟨by linarith [hx₀.1], by linarith [hx₀.2]⟩
    refine ⟨x₀ + 1 / 2, ⟨by linarith [hx₀.1], by linarith [hx₀.2]⟩, Or.inr ?_⟩
    intro x hx
    have hxn : x ∈ Set.Icc n (n + 2) := ⟨by linarith [hx₀.1, hx.1], by linarith [hx₀.2, hx.2]⟩
    have hd : |x - x₀| ≤ (1 / 2 : Real) := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hLip := (deBruijnVolterraWindowMean_lipschitz hf heq hn hxn hx₀n).trans
      (mul_le_mul_of_nonneg_left hd (deBruijnVolterraOscillation_nonneg hf hn))
    have hb := (abs_le.mp hLip).1
    unfold deBruijnVolterraOscillation at hmean₀ hb ⊢
    linarith

end

end Erdos1212Kernel
