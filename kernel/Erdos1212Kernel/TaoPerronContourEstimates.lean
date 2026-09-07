import Erdos1212Kernel.TaoPerronHorizontalBoundaryBound

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 600000

theorem taoPerron_vertical_intervalIntegrable
    {β H x : Real} (hβ : 0 < β) (hβ1 : β ≠ 1) (hH : 0 ≤ H) (hx : 0 < x)
    (hnz : ∀ t ∈ Icc (-H) H, riemannZeta ((β : Complex) + (t : Complex) * I) ≠ 0) :
    IntervalIntegrable (fun t : Real =>
      taoPerronFullIntegrand x ((β : Complex) + (t : Complex) * I)) volume (-H) H := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (-H) H := by simpa only [uIcc_of_le (neg_le_self hH)] using ht
  let s : Complex := (β : Complex) + (t : Complex) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    exact hβ1 hr
  have hs0 : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hsplus : s + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hout := continuousAt_taoPerronFullIntegrand hx hs1 (hnz t ht') hs0 hsplus
  have hline : Continuous (fun u : Real => (β : Complex) + (u : Complex) * I) := by fun_prop
  exact (hout.comp (f := fun u : Real => (β : Complex) + (u : Complex) * I)
    hline.continuousAt).continuousWithinAt

theorem taoPerron_left_integral_bound_of_holomorphic
    {δ B H x : Real} (hδ : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (hH : 0 ≤ H) (hx : 0 < x)
    (hstrip : ∀ t : Real, |t| ≤ H →
      taoZetaPoleRemoved (((1 - δ : Real) : Complex) + (t : Complex) * I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved
        (((1 - δ : Real) : Complex) + (t : Complex) * I)‖ ≤ B) :
    ‖∫ t : Real in (-H)..H,
      taoPerronFullIntegrand x (((1 - δ : Real) : Complex) + (t : Complex) * I)‖ ≤
        (1 / δ + B) * x ^ (1 - δ) * (Real.pi / (1 - δ)) := by
  let β : Real := 1 - δ
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hdata (t : Real) (ht : |t| ≤ H) :
      riemannZeta ((β : Complex) + (t : Complex) * I) ≠ 0 ∧
      ‖taoZetaLogDerivative ((β : Complex) + (t : Complex) * I)‖ ≤ 1 / δ + B := by
    obtain ⟨hHnz, hHbound⟩ := hstrip t ht
    let s : Complex := (β : Complex) + (t : Complex) * I
    have hs1 : s ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      simp [s] at hr
      linarith
    have hnz : riemannZeta s ≠ 0 := by
      intro h
      rw [taoZetaPoleRemoved_of_ne_one hs1, h, mul_zero] at hHnz
      exact hHnz rfl
    have hdist : δ ≤ ‖s - 1‖ := by
      simpa [s, β, abs_of_pos hδ] using Complex.abs_re_le_norm (s - 1)
    have hpole := one_div_le_one_div_of_le hδ hdist
    exact ⟨hnz, (norm_taoZetaLogDerivative_le_of_poleRemoved_bound hs1 hnz hHbound).trans
      (add_le_add hpole le_rfl)⟩
  have hint := taoPerron_vertical_intervalIntegrable hβ hβ1.ne hH hx
    (fun t ht => (hdata t (abs_le.mpr ht)).1)
  apply norm_intervalIntegral_le_const_mul_pi_div hH (by positivity) hβ hint
  intro t ht
  have hlog := (hdata t (abs_le.mpr ht)).2
  have hk := norm_taoPerronAnalyticFactor_vertical_le (t := t) hx hβ
  have hm := mul_le_mul hlog hk (norm_nonneg _) (by positivity : 0 ≤ 1 / δ + B)
  simpa only [taoPerronFullIntegrand, norm_mul, one_div, mul_assoc] using hm

theorem taoPerron_truncated_right_error_of_strip
    {δ C L H x : Real} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (hH : 0 < H) (hx : 1 ≤ x)
    (hstrip : ∀ t u : Real, |t| ≤ H → 1 - δ ≤ u → u ≤ 1 + δ →
      taoZetaPoleRemoved ((u : Complex) + (t : Complex) * I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved ((u : Complex) + (t : Complex) * I)‖ ≤ C * L ^ 2) :
    ‖(∫ t : Real in (-H)..H,
        taoPerronFullIntegrand x (((1 + δ : Real) : Complex) + (t : Complex) * I)) -
        (x : Complex) * (Real.pi : Complex)‖ ≤
      (1 / δ + C * L ^ 2) * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
        4 * δ * (1 / H + C * L ^ 2) * x ^ (1 + δ) * (1 / H ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβ0 : 0 < 1 - δ := by linarith
  have hβ1 : 1 - δ < 1 := by linarith
  have hσ : 1 < 1 + δ := by linarith
  have hzero : ∀ s ∈ Icc (1 - δ) (1 + δ) ×ℂ Icc (-H) H,
      s = 1 ∨ riemannZeta s ≠ 0 := by
    intro s hs
    rcases eq_or_ne s 1 with hs1 | hs1
    · exact Or.inl hs1
    · right
      have hmem := Complex.mem_reProdIm.mp hs
      have hHnz := (hstrip s.im s.re (abs_le.mpr hmem.2) hmem.1.1 hmem.1.2).1
      rw [Complex.re_add_im, taoZetaPoleRemoved_of_ne_one hs1] at hHnz
      exact (mul_ne_zero_iff.mp hHnz).2
  have hboundary := taoPerronFullIntegrand_rectangle_boundary hβ0 hβ1 hσ hH hx0 hzero
  have hleft := taoPerron_left_integral_bound_of_holomorphic hδ hδ1
    (mul_nonneg hC (sq_nonneg L)) hH.le hx0
    (fun t ht => hstrip t (1 - δ) ht le_rfl (by linarith))
  have hhorizontal := taoPerron_horizontal_boundary_bound_of_strip hδ hC hH hx hstrip
  let V (u : Real) : Complex := ∫ t : Real in (-H)..H,
    taoPerronFullIntegrand x ((u : Complex) + (t : Complex) * I)
  let E : Complex := (∫ u : Real in (1 - δ)..(1 + δ),
      taoPerronFullIntegrand x ((u : Complex) + ((-H : Real) : Complex) * I)) -
    ∫ u : Real in (1 - δ)..(1 + δ),
      taoPerronFullIntegrand x ((u : Complex) + (H : Complex) * I)
  have hboundary' : E + I * V (1 + δ) - I * V (1 - δ) = (x : Complex) * Real.pi * I :=
    hboundary
  have hidentity : V (1 + δ) - (x : Complex) * Real.pi = V (1 - δ) + I * E := by
    have hm := congrArg (fun z : Complex => -I * z) hboundary'
    simp only [mul_sub, mul_add, neg_mul, ← mul_assoc, I_mul_I, neg_neg, one_mul] at hm
    have hIR : -(I * (x : Complex) * Real.pi * I) = (x : Complex) * Real.pi := by
      calc
        _ = -((x : Complex) * Real.pi * (I * I)) := by ring
        _ = _ := by rw [I_mul_I]; ring
    rw [hIR] at hm
    linear_combination hm
  change ‖V (1 + δ) - (x : Complex) * Real.pi‖ ≤ _
  rw [hidentity]
  calc
    ‖V (1 - δ) + I * E‖ ≤ ‖V (1 - δ)‖ + ‖I * E‖ := norm_add_le _ _
    _ = ‖V (1 - δ)‖ + ‖E‖ := by rw [norm_mul, norm_I, one_mul]
    _ ≤ _ := add_le_add hleft hhorizontal

end

end Erdos1212Kernel
