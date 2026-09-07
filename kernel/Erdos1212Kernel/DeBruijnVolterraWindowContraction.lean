import Erdos1212Kernel.DeBruijnVolterraPointContraction

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnVolterraWindowMax_le_of_bound {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {y C : Real} (hy : 1 ≤ y)
    (hb : ∀ x ∈ Set.Icc (y - 1) y, f x ≤ C) : deBruijnVolterraWindowMax f y ≤ C := by
  letI : NeZero (volume.restrict (Set.Icc (y - 1) y)) := ⟨deBruijnVolterraWindow_measure_ne_zero y⟩
  apply essSup_le_of_ae_le C _ (deBruijnVolterraWindow_boundedBelow hf hy).isCoboundedUnder_le
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hb x hx

theorem deBruijnVolterraWindowMin_ge_of_bound {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {y C : Real} (hy : 1 ≤ y)
    (hb : ∀ x ∈ Set.Icc (y - 1) y, C ≤ f x) : C ≤ deBruijnVolterraWindowMin f y := by
  letI : NeZero (volume.restrict (Set.Icc (y - 1) y)) := ⟨deBruijnVolterraWindow_measure_ne_zero y⟩
  apply le_essInf_of_ae_le C _ (deBruijnVolterraWindow_boundedAbove hf hy).isCoboundedUnder_ge
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hb x hx

theorem deBruijnVolterra_upper_good_window {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n y γ : Real} (hn : 1 ≤ n) (hy : y ∈ Set.Icc (n + 1) (n + 2)) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4))
    (hgood : ∀ x ∈ Set.Icc (y - 1) y,
      γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMean f x) :
    deBruijnVolterraOscillation f (n + 2) ≤ (1 - γ / (n + 2)) * deBruijnVolterraOscillation f n := by
  let η := γ / (n + 2)
  have hη0 : 0 ≤ η := div_nonneg hγ.1.le (by linarith)
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_iff₀ (show 0 < n + 2 by linarith)]
    linarith [hγ.2]
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hym1 : 1 ≤ y - 1 := by linarith [hy.1]
  have hpoint : ∀ x ∈ Set.Icc (y - 1) y,
      f x ≤ (1 - η) * deBruijnVolterraWindowMax f (y - 1) + η * deBruijnVolterraWindowMin f y := by
    intro x hx
    have hx1 : 1 ≤ x := hym1.trans hx.1
    have hηx : η ≤ γ / x := div_le_div_of_nonneg_left hγ.1.le (by linarith) (hx.2.trans hy.2)
    have hp := deBruijnVolterra_upper_point_contraction hf heq hx1 (hgood x hx)
    have hmul := mul_le_mul_of_nonneg_right hηx (deBruijnVolterraOscillation_nonneg hf hx1)
    have hMx := deBruijnVolterraWindowMax_antitoneOn hf heq hym1 hx1 hx.1
    have hmx := deBruijnVolterraWindowMin_monotoneOn hf heq hx1 hy1 hx.2
    have hscaledM := mul_le_mul_of_nonneg_left hMx (sub_nonneg.mpr hη1)
    have hscaledm := mul_le_mul_of_nonneg_left hmx hη0
    unfold deBruijnVolterraOscillation at hp hmul
    nlinarith
  have hMy := deBruijnVolterraWindowMax_le_of_bound hf hy1 hpoint
  have hM := deBruijnVolterraWindowMax_antitoneOn hf heq hn hym1 (by linarith [hy.1])
  have hm := deBruijnVolterraWindowMin_monotoneOn hf heq hn hy1 (by linarith [hy.1])
  have hMscaled := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hη1)
  have hmscaled := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hη1)
  have hD := deBruijnVolterraOscillation_antitoneOn hf heq hy1 (by linarith : 1 ≤ n + 2) hy.2
  change deBruijnVolterraOscillation f (n + 2) ≤ (1 - η) * deBruijnVolterraOscillation f n
  unfold deBruijnVolterraOscillation at hD ⊢
  nlinarith

theorem deBruijnVolterra_lower_good_window {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {n y γ : Real} (hn : 1 ≤ n) (hy : y ∈ Set.Icc (n + 1) (n + 2)) (hγ : γ ∈ Set.Ioo (0 : Real) (1 / 4))
    (hgood : ∀ x ∈ Set.Icc (y - 1) y,
      γ * deBruijnVolterraOscillation f x ≤ deBruijnVolterraWindowMean f x - deBruijnVolterraWindowMin f x) :
    deBruijnVolterraOscillation f (n + 2) ≤ (1 - γ / (n + 2)) * deBruijnVolterraOscillation f n := by
  let η := γ / (n + 2)
  have hη0 : 0 ≤ η := div_nonneg hγ.1.le (by linarith)
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_iff₀ (show 0 < n + 2 by linarith)]
    linarith [hγ.2]
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hym1 : 1 ≤ y - 1 := by linarith [hy.1]
  have hpoint : ∀ x ∈ Set.Icc (y - 1) y,
      (1 - η) * deBruijnVolterraWindowMin f (y - 1) + η * deBruijnVolterraWindowMax f y ≤ f x := by
    intro x hx
    have hx1 : 1 ≤ x := hym1.trans hx.1
    have hηx : η ≤ γ / x := div_le_div_of_nonneg_left hγ.1.le (by linarith) (hx.2.trans hy.2)
    have hp := deBruijnVolterra_lower_point_contraction hf heq hx1 (hgood x hx)
    have hmul := mul_le_mul_of_nonneg_right hηx (deBruijnVolterraOscillation_nonneg hf hx1)
    have hmx := deBruijnVolterraWindowMin_monotoneOn hf heq hym1 hx1 hx.1
    have hMx := deBruijnVolterraWindowMax_antitoneOn hf heq hx1 hy1 hx.2
    have hscaledm := mul_le_mul_of_nonneg_left hmx (sub_nonneg.mpr hη1)
    have hscaledM := mul_le_mul_of_nonneg_left hMx hη0
    unfold deBruijnVolterraOscillation at hp hmul
    nlinarith
  have hmy := deBruijnVolterraWindowMin_ge_of_bound hf hy1 hpoint
  have hM := deBruijnVolterraWindowMax_antitoneOn hf heq hn hy1 (by linarith [hy.1])
  have hm := deBruijnVolterraWindowMin_monotoneOn hf heq hn hym1 (by linarith [hy.1])
  have hMscaled := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hη1)
  have hmscaled := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hη1)
  have hD := deBruijnVolterraOscillation_antitoneOn hf heq hy1 (by linarith : 1 ≤ n + 2) hy.2
  change deBruijnVolterraOscillation f (n + 2) ≤ (1 - η) * deBruijnVolterraOscillation f n
  unfold deBruijnVolterraOscillation at hD ⊢
  nlinarith

end

end Erdos1212Kernel
