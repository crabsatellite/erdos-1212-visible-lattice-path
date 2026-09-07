import Erdos1212Kernel.DeBruijnVolterraWindowContraction
import Erdos1212Kernel.DeBruijnVolterraMeanDichotomy

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem deBruijnVolterra_upper_bad_point {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n x γ : Real} (hn : 1 ≤ n) (hx : x ∈ Set.Icc n (n + 2)) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4))
    (hmean : deBruijnVolterraWindowMean f x ≤ deBruijnVolterraWindowMax f n - deBruijnVolterraOscillation f n / 4)
    (hbad : deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMean f x < γ * deBruijnVolterraOscillation f x) :
    deBruijnVolterraOscillation f (n + 2) ≤ (3 / (4 * (1 - γ))) * deBruijnVolterraOscillation f n := by
  have hx1 : 1 ≤ x := hn.trans hx.1
  have hn2 : 1 ≤ n + 2 := by linarith
  have hpos : 0 < 1 - γ := by linarith [hγ.2]
  have hM := deBruijnVolterraWindowMax_antitoneOn hf heq hx1 hn2 hx.2
  have hm := deBruijnVolterraWindowMin_monotoneOn hf heq hn hx1 hx.1
  have hm2 := deBruijnVolterraWindowMin_monotoneOn hf heq hn hn2 (by linarith)
  have hMs := mul_le_mul_of_nonneg_left hM hpos.le
  have hms := mul_le_mul_of_nonneg_left hm hγ.1.le
  have hm2s := mul_le_mul_of_nonneg_left hm2 hpos.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 4 * (1 - γ) by positivity)).mpr
  unfold deBruijnVolterraOscillation at hmean hbad ⊢
  nlinarith

theorem deBruijnVolterra_lower_bad_point {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n x γ : Real} (hn : 1 ≤ n) (hx : x ∈ Set.Icc n (n + 2)) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4))
    (hmean : deBruijnVolterraWindowMin f n + deBruijnVolterraOscillation f n / 4 ≤ deBruijnVolterraWindowMean f x)
    (hbad : deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMin f x < γ * deBruijnVolterraOscillation f x) :
    deBruijnVolterraOscillation f (n + 2) ≤ (3 / (4 * (1 - γ))) * deBruijnVolterraOscillation f n := by
  have hx1 : 1 ≤ x := hn.trans hx.1
  have hn2 : 1 ≤ n + 2 := by linarith
  have hpos : 0 < 1 - γ := by linarith [hγ.2]
  have hm := deBruijnVolterraWindowMin_monotoneOn hf heq hx1 hn2 hx.2
  have hM := deBruijnVolterraWindowMax_antitoneOn hf heq hn hx1 hx.1
  have hM2 := deBruijnVolterraWindowMax_antitoneOn hf heq hn hn2 (by linarith)
  have hms := mul_le_mul_of_nonneg_left hm hpos.le
  have hMs := mul_le_mul_of_nonneg_left hM hγ.1.le
  have hM2s := mul_le_mul_of_nonneg_left hM2 hpos.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 4 * (1 - γ) by positivity)).mpr
  unfold deBruijnVolterraOscillation at hmean hbad ⊢
  nlinarith

/-- The source's two-step oscillation estimate (2.12), with the literal
rho-kernel value eta=gamma/(n+2). Both alternatives are produced from the
equation, not supplied as a dichotomy or contraction premise. -/
theorem deBruijnVolterra_two_step_contraction {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n γ : Real} (hn : 1 ≤ n) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4)) :
    deBruijnVolterraOscillation f (n + 2) ≤
      max (3 / (4 * (1 - γ))) (1 - γ / (n + 2)) * deBruijnVolterraOscillation f n := by
  have hD := deBruijnVolterraOscillation_nonneg hf hn
  have hgoodCoef := mul_le_mul_of_nonneg_right
    (le_max_right (3 / (4 * (1 - γ))) (1 - γ / (n + 2))) hD
  have hbadCoef := mul_le_mul_of_nonneg_right
    (le_max_left (3 / (4 * (1 - γ))) (1 - γ / (n + 2))) hD
  obtain ⟨y, hy, hlow | hhigh⟩ := deBruijnVolterra_mean_dichotomy hf heq hn
  · by_cases hgood : ∀ x ∈ Set.Icc (y - 1) y,
        γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMean f x
    · exact (deBruijnVolterra_upper_good_window hf heq hn hy hγ hgood).trans hgoodCoef
    · push_neg at hgood
      obtain ⟨x, hx, hbad⟩ := hgood
      have hxn : x ∈ Set.Icc n (n + 2) := ⟨by linarith [hy.1, hx.1], hx.2.trans hy.2⟩
      exact (deBruijnVolterra_upper_bad_point hf heq hn hxn hγ (hlow x hx) hbad).trans hbadCoef
  · by_cases hgood : ∀ x ∈ Set.Icc (y - 1) y,
        γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMin f x
    · exact (deBruijnVolterra_lower_good_window hf heq hn hy hγ hgood).trans hgoodCoef
    · push_neg at hgood
      obtain ⟨x, hx, hbad⟩ := hgood
      have hxn : x ∈ Set.Icc n (n + 2) := ⟨by linarith [hy.1, hx.1], hx.2.trans hy.2⟩
      exact (deBruijnVolterra_lower_bad_point hf heq hn hxn hγ (hhigh x hx) hbad).trans hbadCoef

theorem deBruijnRhoSolutionRatio_two_step_contraction {F : Real → Real}
    (hc : ContinuousOn F (Set.Ici (0 : Real)))
    (heq : ∀ x : Real, 1 ≤ x → x * F x = ∫ t in (0 : Real)..1, F (x - t))
    {n γ : Real} (hn : 1 ≤ n) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4)) :
    deBruijnVolterraOscillation (deBruijnRhoSolutionRatio F) (n + 2) ≤
      max (3 / (4 * (1 - γ))) (1 - γ / (n + 2)) * deBruijnVolterraOscillation (deBruijnRhoSolutionRatio F) n :=
  deBruijnVolterra_two_step_contraction (deBruijnRhoSolutionRatio_continuousOn hc)
    (deBruijnRhoSolutionRatio_equation heq) hn hγ

end

end Erdos1212Kernel
