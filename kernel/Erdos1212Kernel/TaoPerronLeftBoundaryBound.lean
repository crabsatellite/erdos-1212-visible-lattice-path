import Erdos1212Kernel.TaoPNTFixedContourGlobalLogDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 1900000

theorem integral_inv_sq_add_sq_neg_le_pi_div
    {β H : Real} (hβ : 0 < β) :
    (∫ t : Real in (-H)..H, (β ^ 2 + t ^ 2)⁻¹) ≤ Real.pi / β := by
  rw [integral_inv_sq_add_sq hβ.ne']
  have hdiff : Real.arctan (H / β) - Real.arctan (-H / β) ≤ Real.pi := by
    have htop := Real.arctan_lt_pi_div_two (H / β)
    have hbot := Real.neg_pi_div_two_lt_arctan (-H / β)
    linarith
  have hbinv : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ.le
  calc
    β⁻¹ * (Real.arctan (H / β) - Real.arctan (-H / β)) ≤
        β⁻¹ * Real.pi := mul_le_mul_of_nonneg_left hdiff hbinv
    _ = Real.pi / β := by ring

theorem norm_intervalIntegral_le_const_mul_pi_div
    {f : Real → Complex} {A β H : Real}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hβ : 0 < β)
    (hf : IntervalIntegrable f volume (-H) H)
    (hbound : ∀ t ∈ Set.Icc (-H) H,
      ‖f t‖ ≤ A * (β ^ 2 + t ^ 2)⁻¹) :
    ‖∫ t : Real in (-H)..H, f t‖ ≤ A * (Real.pi / β) := by
  have hmajor : IntervalIntegrable
      (fun t : Real => A * (β ^ 2 + t ^ 2)⁻¹) volume (-H) H := by
    apply Continuous.intervalIntegrable
    have hden : ∀ t : Real, β ^ 2 + t ^ 2 ≠ 0 := by
      intro t
      have : 0 < β ^ 2 + t ^ 2 := by nlinarith [sq_pos_of_pos hβ, sq_nonneg t]
      exact this.ne'
    have hc : Continuous (fun t : Real => β ^ 2 + t ^ 2) := by fun_prop
    exact continuous_const.mul (hc.inv₀ hden)
  calc
    ‖∫ t : Real in (-H)..H, f t‖ ≤
        ∫ t : Real in (-H)..H, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ t : Real in (-H)..H, A * (β ^ 2 + t ^ 2)⁻¹ :=
      intervalIntegral.integral_mono_on (by linarith) hf.norm hmajor hbound
    _ = A * ∫ t : Real in (-H)..H, (β ^ 2 + t ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A * (Real.pi / β) :=
      mul_le_mul_of_nonneg_left (integral_inv_sq_add_sq_neg_le_pi_div hβ) hA

theorem continuousAt_taoPerronFullIntegrand
    {x : Real} (hx : 0 < x) {s : Complex}
    (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0)
    (hs0 : s ≠ 0) (hsplus : s + 1 ≠ 0) :
    ContinuousAt (taoPerronFullIntegrand x) s := by
  have hzAn : AnalyticAt Complex riemannZeta s :=
    analyticOn_riemannZeta s (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs1)
  have hlog : ContinuousAt taoZetaLogDerivative s := by
    unfold taoZetaLogDerivative
    exact hzAn.deriv.continuousAt.neg.div hzAn.continuousAt hzeta
  have hfactor :=
    (differentiableAt_taoPerronAnalyticFactor hx hs0 hsplus).continuousAt
  unfold taoPerronFullIntegrand
  exact hlog.mul hfactor

theorem exists_taoPerron_left_boundary_pointwise_bound :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧ 0 ≤ H₀ ∧
      ∀ H t x : Real,
        H₀ ≤ H → |t| ≤ H → 0 < x →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        0 < β ∧ β < 1 ∧
          (‖taoPerronFullIntegrand x
              ((β : Complex) + (t : Complex) * Complex.I)‖ ≤
            C * L ^ 2 * x ^ β * (β ^ 2 + t ^ 2)⁻¹) ∧
          riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, C, H₁, hd, hC, hlog⟩ :=
    exists_taoPNT_fixed_left_global_logDerivative_log_sq
  let H₀ : Real := max H₁ 0
  have hH₀ : 0 ≤ H₀ := le_max_right _ _
  refine ⟨d, C, H₀, hd, hC, hH₀, ?_⟩
  intro H t x hH ht hx
  let L : Real := Real.log (3 + H)
  let β : Real := 1 - d / L
  have hH1 : H₁ ≤ H := (le_max_left H₁ 0).trans hH
  obtain ⟨hβ, hβ1, hL, hzeta⟩ := hlog H t hH1 ht
  have hfactor := norm_taoPerronAnalyticFactor_vertical_le
    (x := x) (σ := β) (t := t) hx hβ
  refine ⟨hβ, hβ1, ?_, hzeta⟩
  change ‖taoPerronFullIntegrand x
      ((β : Complex) + (t : Complex) * Complex.I)‖ ≤
    C * L ^ 2 * x ^ β * (β ^ 2 + t ^ 2)⁻¹
  unfold taoPerronFullIntegrand
  rw [norm_mul]
  calc
    ‖taoZetaLogDerivative (↑β + ↑t * Complex.I)‖ *
        ‖taoPerronAnalyticFactor x (↑β + ↑t * Complex.I)‖ ≤
      (C * L ^ 2) * (x ^ β * (1 / (β ^ 2 + t ^ 2))) := by
        exact mul_le_mul hL hfactor (norm_nonneg _) (by positivity)
    _ = C * L ^ 2 * x ^ β * (β ^ 2 + t ^ 2)⁻¹ := by
      rw [one_div]
      ring

theorem exists_taoPerron_left_boundary_integral_bound :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧ 0 ≤ H₀ ∧
      ∀ H x : Real,
        H₀ ≤ H → 0 < x →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        ‖∫ t : Real in (-H)..H,
            taoPerronFullIntegrand x
              ((β : Complex) + (t : Complex) * Complex.I)‖ ≤
          C * L ^ 2 * x ^ β * (Real.pi / β) := by
  obtain ⟨d, C, H₀, hd, hC, hH₀, hpoint⟩ :=
    exists_taoPerron_left_boundary_pointwise_bound
  refine ⟨d, C, H₀, hd, hC, hH₀, ?_⟩
  intro H x hH hx
  let L : Real := Real.log (3 + H)
  let β : Real := 1 - d / L
  have hH0 : 0 ≤ H := hH₀.trans hH
  have hdata (t : Real) (ht : t ∈ Set.Icc (-H) H) :=
    hpoint H t x hH (abs_le.mpr ht) hx
  have hzeroMem : (0 : Real) ∈ Set.Icc (-H) H := ⟨by linarith, hH0⟩
  have hβ : 0 < β := (hdata 0 hzeroMem).1
  have hf : IntervalIntegrable (fun t : Real =>
      taoPerronFullIntegrand x
        ((β : Complex) + (t : Complex) * Complex.I)) volume (-H) H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htIcc : t ∈ Set.Icc (-H) H := by
      rwa [Set.uIcc_of_le (by linarith)] at ht
    have hdt := hdata t htIcc
    have hβ0 : 0 < β := hdt.1
    have hβ1 : β < 1 := hdt.2.1
    have hzeta := hdt.2.2.2
    let s : Complex := (β : Complex) + (t : Complex) * Complex.I
    have hs1 : s ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hs0 : s ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hsplus : s + 1 ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hline : Continuous (fun u : Real =>
        (β : Complex) + (u : Complex) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have houter := continuousAt_taoPerronFullIntegrand hx hs1
      (by simpa only [s] using hzeta) hs0 hsplus
    have hcomp : ContinuousAt
        (taoPerronFullIntegrand x ∘ fun u : Real =>
          (β : Complex) + (u : Complex) * Complex.I) t :=
      houter.comp (f := fun u : Real =>
        (β : Complex) + (u : Complex) * Complex.I) hline.continuousAt
    simpa only [Function.comp_apply, s] using hcomp.continuousWithinAt
  apply norm_intervalIntegral_le_const_mul_pi_div hH0
    (mul_nonneg (mul_nonneg hC.le (sq_nonneg L)) (Real.rpow_nonneg hx.le _)) hβ hf
  intro t ht
  simpa only [L, β, mul_assoc] using (hdata t ht).2.2.1

end

end Erdos1212Kernel
