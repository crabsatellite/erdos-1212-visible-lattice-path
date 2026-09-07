import Erdos1212Kernel.TaoPerronContourEstimates

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 600000

def taoPerronRightLineConstant (σ : Real) : Real :=
  (Real.log 4 + 4) * (1 + 1 / (σ - 1))

theorem taoPerronRightLineConstant_pos {σ : Real} (hσ : 1 < σ) :
    0 < taoPerronRightLineConstant σ := by
  unfold taoPerronRightLineConstant
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hd : 0 < σ - 1 := by linarith
  positivity

theorem norm_taoZetaLogDerivative_right_line {σ : Real} (hσ : 1 < σ) (t : Real) :
    ‖taoZetaLogDerivative ((σ : Complex) + (t : Complex) * I)‖ ≤
      taoPerronRightLineConstant σ := by
  have hs : 1 < ((σ : Complex) + (t : Complex) * I).re := by simpa using hσ
  rw [taoZetaLogDerivative_eq_vonMangoldtLSeries hs]
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  rw [hsum.norm.tsum_eq_zero_add]
  simp only [LSeries.term_zero, norm_zero, zero_add]
  have heq : (∑' n : Nat,
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
        ((σ : Complex) + (t : Complex) * I) (n + 1)‖) =
      ∑' n : Nat, ArithmeticFunction.vonMangoldt (n + 1) *
        ((n + 1 : Nat) : Real) ^ (-σ) := by
    apply tsum_congr
    intro n
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hre : ((σ : Complex) + (t : Complex) * I).re = σ := by simp
    rw [hre, div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
  rw [heq]
  exact taoVonMangoldt_dirichlet_tsum_le hσ

theorem norm_taoPerronFullIntegrand_right_line {σ x : Real}
    (hσ : 1 < σ) (hx : 0 < x) (t : Real) :
    ‖taoPerronFullIntegrand x ((σ : Complex) + (t : Complex) * I)‖ ≤
      (taoPerronRightLineConstant σ * x ^ σ) * (1 + t ^ 2)⁻¹ := by
  have hlog := norm_taoZetaLogDerivative_right_line hσ t
  have hk := norm_taoPerronAnalyticFactor_vertical_le (t := t) hx (by linarith : 0 < σ)
  have hinv : 1 / (σ ^ 2 + t ^ 2) ≤ (1 + t ^ 2)⁻¹ := by
    rw [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hk' := hk.trans (mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hx.le _))
  have hm := mul_le_mul hlog hk' (norm_nonneg _)
    (taoPerronRightLineConstant_pos hσ).le
  simpa only [taoPerronFullIntegrand, norm_mul, mul_assoc] using hm

theorem integrable_taoPerronFullIntegrand_right_line {σ x : Real}
    (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : Real => taoPerronFullIntegrand x ((σ : Complex) + (t : Complex) * I)) := by
  have hmajor := integrable_inv_one_add_sq.const_mul (taoPerronRightLineConstant σ * x ^ σ)
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    let s : Complex := (σ : Complex) + (t : Complex) * I
    have hsre : s.re = σ := by simp [s]
    have hs1 : s ≠ 1 := by
      intro h; have hh := congrArg Complex.re h; rw [hsre] at hh; norm_num at hh; linarith
    have hs0 : s ≠ 0 := by
      intro h; have hh := congrArg Complex.re h; rw [hsre] at hh; norm_num at hh; linarith
    have hsp : s + 1 ≠ 0 := by
      intro h; have hh := congrArg Complex.re h; simp [hsre] at hh; linarith
    have hnz := riemannZeta_ne_zero_of_one_lt_re (s := s) (by rwa [hsre])
    have hout := continuousAt_taoPerronFullIntegrand hx hs1 hnz hs0 hsp
    exact hout.comp (f := fun u : Real => (σ : Complex) + (u : Complex) * I) (by fun_prop)
  · filter_upwards with t
    exact norm_taoPerronFullIntegrand_right_line hσ hx t

theorem tao_abs_arctan_le_abs (q : Real) : |Real.arctan q| ≤ |q| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := q) (C := 1) (f := fun t : Real => (1 + t ^ 2)⁻¹) (by
      intro t _ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t]))
  simpa only [integral_inv_one_add_sq, Real.arctan_zero, sub_zero, one_mul,
    Real.norm_eq_abs] using hb

theorem tao_integral_tail_inv_one_add_sq {H : Real} (hH : 0 < H) :
    (∫ t : Real in (Ioc (-H) H)ᶜ, (1 + t ^ 2)⁻¹) ≤ 2 / H := by
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
    integrable_inv_one_add_sq.integrableOn integrable_inv_one_add_sq.integrableOn,
    integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq, Real.arctan_neg]
  have hsmall : Real.arctan H⁻¹ ≤ 1 / H := by
    exact (le_abs_self _).trans (by simpa [abs_of_pos hH] using tao_abs_arctan_le_abs H⁻¹)
  rw [Real.arctan_inv_of_pos hH] at hsmall
  calc
    -Real.arctan H + Real.pi / 2 + (Real.pi / 2 - Real.arctan H) =
        2 * (Real.pi / 2 - Real.arctan H) := by ring
    _ ≤ 2 * (1 / H) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = 2 / H := by ring

theorem taoPerron_right_line_tail_bound {σ x H : Real}
    (hσ : 1 < σ) (hx : 0 < x) (hH : 0 < H) :
    ‖(∫ t : Real, taoPerronFullIntegrand x ((σ : Complex) + (t : Complex) * I)) -
      ∫ t : Real in (-H)..H,
        taoPerronFullIntegrand x ((σ : Complex) + (t : Complex) * I)‖ ≤
      (taoPerronRightLineConstant σ * x ^ σ) * (2 / H) := by
  have hint := integrable_taoPerronFullIntegrand_right_line hσ hx
  rw [intervalIntegral.integral_of_le (by linarith), ← setIntegral_compl measurableSet_Ioc hint]
  have hmajor := (integrable_inv_one_add_sq.const_mul
    (taoPerronRightLineConstant σ * x ^ σ)).integrableOn (s := (Ioc (-H) H)ᶜ)
  calc
    _ ≤ ∫ t : Real in (Ioc (-H) H)ᶜ,
        (taoPerronRightLineConstant σ * x ^ σ) * (1 + t ^ 2)⁻¹ := by
      apply norm_integral_le_of_norm_le hmajor
      exact Filter.Eventually.of_forall (norm_taoPerronFullIntegrand_right_line hσ hx)
    _ = (taoPerronRightLineConstant σ * x ^ σ) *
        ∫ t : Real in (Ioc (-H) H)ᶜ, (1 + t ^ 2)⁻¹ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (tao_integral_tail_inv_one_add_sq hH) (by
      exact mul_nonneg (taoPerronRightLineConstant_pos hσ).le (Real.rpow_nonneg hx.le _))

end

end Erdos1212Kernel
