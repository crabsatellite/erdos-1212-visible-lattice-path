import Erdos1212Kernel.TaoZetaPoleRemovedOffCenter

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

theorem norm_taoZetaPoleRemoved_le_high_disk
    {t α R U : Real}
    (hU : U = taoLogFrequency t)
    (hU4 : 4 ≤ U) (hlogU : 1 ≤ Real.log U)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hα1 : 1 ≤ α)
    (hleft : 1 - taoZeroFreeBaseRadius U / 4 ≤ α - R)
    (hright : α + R ≤ 2)
    (hnear : ∀ V ∈ Set.Icc (U - 1) (U + 1),
      TaoLittlewoodFinalFrequencyConditions V ∧
      4 ≤ V ∧ 1 ≤ Real.log V ∧
      taoZeroFreeBaseRadius U / 4 ≤
        taoLittlewoodWidth V (taoLittlewoodR V) ∧
      Real.log V ≤ 2 * Real.log U)
    {z : Complex}
    (hz : z ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R) :
    ‖taoZetaPoleRemoved z‖ ≤
      (2 : Real) ^ 52 * U * (Real.log U) ^ 2 := by
  let c : Complex := (α : Complex) + (t : Complex) * Complex.I
  have hdist : dist z c < R := mem_ball.mp hz
  have hfreqDist : |taoLogFrequency z.im - U| < 1 := by
    have hbase := abs_taoLogFrequency_sub_le_dist_imaginary_centers z α t
    rw [← hU] at hbase
    exact hbase.trans_lt (hdist.trans_le hR1)
  have hVmem : taoLogFrequency z.im ∈ Set.Icc (U - 1) (U + 1) := by
    rw [Set.mem_Icc]
    rw [abs_lt] at hfreqDist
    constructor <;> linarith
  obtain ⟨hcond, hV4, hlogV, hwidth, hlogCompare⟩ :=
    hnear (taoLogFrequency z.im) hVmem
  have hreDist := abs_re_sub_le_dist z c
  have hcre : c.re = α := by simp [c]
  rw [hcre] at hreDist
  have hzLower : 1 - taoLittlewoodWidth (taoLogFrequency z.im)
      (taoLittlewoodR (taoLogFrequency z.im)) ≤ z.re := by
    have hzre : α - R < z.re := by
      have habs : |z.re - α| < R := hreDist.trans_lt hdist
      rw [abs_lt] at habs
      linarith
    linarith
  have hzUpper : z.re ≤ 2 := by
    have hzre : z.re < α + R := by
      have := lt_of_le_of_lt hreDist hdist
      rw [abs_lt] at this
      linarith
    linarith
  have hzeta : ‖riemannZeta z‖ ≤
      (2 : Real) ^ 48 * (Real.log U) ^ 2 := by
    have hzeta0 := riemannZeta_norm_le_two_sided_littlewood_log_sq
      z.im z.re hcond hV4 hlogV hzLower hzUpper
    have hzeta1 : ‖riemannZeta z‖ ≤ (2 : Real) ^ 46 *
        (Real.log (taoLogFrequency z.im)) ^ 2 := by
      simpa only [Complex.re_add_im] using hzeta0
    have hlogU0 : 0 ≤ Real.log U := by linarith
    have hlogV0 : 0 ≤ Real.log (taoLogFrequency z.im) := by linarith
    have hsq : (Real.log (taoLogFrequency z.im)) ^ 2 ≤
        4 * (Real.log U) ^ 2 := by nlinarith
    calc
      _ ≤ (2 : Real) ^ 46 *
          (Real.log (taoLogFrequency z.im)) ^ 2 := hzeta1
      _ ≤ (2 : Real) ^ 46 * (4 * (Real.log U) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (2 : Real) ^ 48 * (Real.log U) ^ 2 := by ring
  have hα2 : α ≤ 2 := by linarith
  have hαsub : |α - 1| ≤ 1 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ α - 1)]
    linarith
  have htU : |t| = (2 * Real.pi) * U := by
    rw [hU]
    unfold taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hcNorm : ‖c - 1‖ ≤ 1 + 8 * U := by
    calc
      ‖c - 1‖ ≤ |(c - 1).re| + |(c - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |α - 1| + |t| := by simp [c]
      _ ≤ 1 + (2 * Real.pi) * U := by rw [htU]; linarith
      _ ≤ 1 + 8 * U := by
        have hpi := Real.pi_le_four
        nlinarith

  have hzDistOne : ‖z - 1‖ ≤ 10 * U := by
    have hzc : ‖z - c‖ < R := by simpa only [Complex.dist_eq] using hdist
    calc
      ‖z - 1‖ ≤ ‖z - c‖ + ‖c - 1‖ := by
        have := norm_add_le (z - c) (c - 1)
        convert this using 1 <;> ring
      _ ≤ R + (1 + 8 * U) := add_le_add hzc.le hcNorm
      _ ≤ 10 * U := by linarith
  by_cases hz1 : z = 1
  · subst z
    rw [taoZetaPoleRemoved_one, norm_one]
    have hlogSq : 1 ≤ (Real.log U) ^ 2 := one_le_pow₀ hlogU
    have hUpos : 0 < U := by linarith
    nlinarith
  · have hprod := norm_taoZetaPoleRemoved_le_of_ne_one hz1 hzeta hzDistOne
    calc
      _ ≤ (10 * U) * ((2 : Real) ^ 48 * (Real.log U) ^ 2) := hprod
      _ ≤ (2 : Real) ^ 52 * U * (Real.log U) ^ 2 := by
        have hU0 : 0 ≤ U := by linarith
        have hlogSq0 : 0 ≤ (Real.log U) ^ 2 := sq_nonneg _
        nlinarith

theorem norm_logDeriv_taoZetaPoleRemoved_le_high_disk
    {t α R U : Real} {z : Complex}
    (hU : U = taoLogFrequency t)
    (hU4 : 4 ≤ U) (hlogU : 1 ≤ Real.log U)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hα : 1 < α)
    (hleft : 1 - taoZeroFreeBaseRadius U / 4 ≤ α - R)
    (hright : α + R ≤ 2)
    (hnear : ∀ V ∈ Set.Icc (U - 1) (U + 1),
      TaoLittlewoodFinalFrequencyConditions V ∧
      4 ≤ V ∧ 1 ≤ Real.log V ∧
      taoZeroFreeBaseRadius U / 4 ≤
        taoLittlewoodWidth V (taoLittlewoodR V) ∧
      Real.log V ≤ 2 * Real.log U)
    (hHnz : ∀ w ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R,
      taoZetaPoleRemoved w ≠ 0)
    (hz : z ∈ ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3)) :
    ‖logDeriv taoZetaPoleRemoved z‖ ≤
      24 * (1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
        Real.log (α - 1) +
        4 * Real.log (1 + 1 / (α - 1))) / R := by
  apply norm_logDeriv_taoZetaPoleRemoved_le_off_center hα hR hz hHnz
  intro w hw
  exact norm_taoZetaPoleRemoved_le_high_disk hU hU4 hlogU hR hR1
    hα.le hleft hright hnear hw

end

end Erdos1212Kernel
