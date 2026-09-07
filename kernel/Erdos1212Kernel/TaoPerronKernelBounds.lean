import Erdos1212Kernel.TaoBorelOffCenter

namespace Erdos1212Kernel

noncomputable section

open Complex

set_option maxHeartbeats 1900000

theorem norm_taoPerronAnalyticFactor_eq
    {x : Real} (hx : 0 < x) (s : Complex) :
    ‖taoPerronAnalyticFactor x s‖ =
      x ^ s.re * ‖taoRieszMellinKernel s‖ := by
  unfold taoPerronAnalyticFactor
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem norm_taoRieszMellinKernel_vertical_le
    {σ t : Real} (hσ : 0 < σ) :
    ‖taoRieszMellinKernel ((σ : Complex) + (t : Complex) * I)‖ ≤
      1 / (σ ^ 2 + t ^ 2) := by
  let z : Complex := (σ : Complex) + (t : Complex) * I
  have hzNormSq : ‖z‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, normSq_apply]
    ring
  have hplus : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + 1))).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [z, normSq_apply]
    nlinarith
  have hz : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
    linarith
  have hz1 : z + 1 ≠ 0 := by
    intro hz1
    have hre := congrArg Complex.re hz1
    simp [z] at hre
    linarith
  have hdenpos : 0 < ‖z‖ * ‖z + 1‖ := by positivity
  unfold taoRieszMellinKernel
  rw [norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (by positivity : 0 < σ ^ 2 + t ^ 2) (calc
    σ ^ 2 + t ^ 2 = ‖z‖ ^ 2 := hzNormSq.symm
    _ ≤ ‖z‖ * ‖z + 1‖ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hplus (norm_nonneg z))

theorem norm_taoRieszMellinKernel_le_inv_im_sq
    {s : Complex} (him : s.im ≠ 0) :
    ‖taoRieszMellinKernel s‖ ≤ 1 / s.im ^ 2 := by
  have hs : s ≠ 0 := by
    intro hs
    subst s
    simp at him
  have hs1 : s + 1 ≠ 0 := by
    intro hs1
    have hi := congrArg Complex.im hs1
    simp at hi
    exact him hi
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s + 1‖ := by
    simpa using Complex.abs_im_le_norm (s + 1)
  have hden : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs, pow_two]
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  unfold taoRieszMellinKernel
  rw [norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero him) hden

theorem norm_taoPerronAnalyticFactor_vertical_le
    {x σ t : Real} (hx : 0 < x) (hσ : 0 < σ) :
    ‖taoPerronAnalyticFactor x ((σ : Complex) + (t : Complex) * I)‖ ≤
      x ^ σ * (1 / (σ ^ 2 + t ^ 2)) := by
  rw [norm_taoPerronAnalyticFactor_eq hx]
  simp only [add_re, Complex.ofReal_re, mul_re, Complex.ofReal_im, I_re,
    I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact mul_le_mul_of_nonneg_left
    (norm_taoRieszMellinKernel_vertical_le hσ) (Real.rpow_nonneg hx.le _)

theorem norm_taoPerronAnalyticFactor_horizontal_le
    {x u T : Real} (hx : 0 < x) (hT : T ≠ 0) :
    ‖taoPerronAnalyticFactor x ((u : Complex) + (T : Complex) * I)‖ ≤
      x ^ u * (1 / T ^ 2) := by
  rw [norm_taoPerronAnalyticFactor_eq hx]
  simp only [add_re, Complex.ofReal_re, mul_re, Complex.ofReal_im, I_re,
    I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hk := norm_taoRieszMellinKernel_le_inv_im_sq
    (s := ((u : Complex) + (T : Complex) * I)) (by simpa using hT)
  simp only [add_im, Complex.ofReal_im, mul_im, Complex.ofReal_re, I_im,
    I_re, zero_mul, mul_one, zero_add, add_zero] at hk
  exact mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hx.le _)

end

end Erdos1212Kernel
