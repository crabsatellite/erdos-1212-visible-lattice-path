import Erdos1212Kernel.TaoZetaRightLogSq

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

def taoZeroFreeBaseRadius (T : Real) : Real :=
  Real.log (Real.log T) / (100 * Real.log T)

theorem taoZeroFreeBaseRadius_pos {T : Real} (hL : 1 < Real.log T) :
    0 < taoZeroFreeBaseRadius T := by
  unfold taoZeroFreeBaseRadius
  exact div_pos (Real.log_pos hL) (mul_pos (by norm_num) (by linarith))

theorem taoZeroFreeBaseRadius_quarter_le_one_div_four_hundred
    {T : Real} (hL : 1 < Real.log T)
    (hll : 1 ≤ Real.log (Real.log T)) :
    taoZeroFreeBaseRadius T / 4 ≤ 1 / 400 := by
  let L := Real.log T
  let l := Real.log L
  have hLpos : 0 < L := by unfold L; linarith
  have hlpos : 0 < l := by unfold l; linarith
  have hlogLle : l ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    dsimp only [l]
    linarith
  unfold taoZeroFreeBaseRadius
  change l / (100 * L) / 4 ≤ 1 / 400
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity : 0 < (100 * L) * 4)
    (by norm_num : (0 : Real) < 400)).2
  nlinarith

theorem taoZeroFreeBaseRadius_le_littlewoodWidth
    {T : Real} (hT : 1 < T) (hL : 1 < Real.log T)
    (hll : 1 ≤ Real.log (Real.log T)) :
    taoZeroFreeBaseRadius T ≤
      taoLittlewoodWidth T (taoLittlewoodR T) := by
  let L := Real.log T
  let l := Real.log L
  have hLp : 0 < L := by unfold L; linarith
  have hlp : 0 < l := by unfold l; linarith
  have hx0 : 0 ≤ 8 * L / l := by positivity
  have hRlt : (taoLittlewoodR T : Real) < 8 * L / l + 1 := by
    unfold taoLittlewoodR
    simpa only [L, l] using Nat.ceil_lt_add_one hx0
  have hRle : (taoLittlewoodR T : Real) ≤ 9 * L := by
    have hdiv : 8 * L / l ≤ 8 * L := by
      exact div_le_self (by positivity) hll
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hden : (taoLittlewoodR T : Real) * Real.log 2 ≤ 100 * L := by
    have hmul := mul_le_mul hRle hlog2le (by positivity)
      (by positivity : (0 : Real) ≤ 9 * L)
    nlinarith
  have hRone := taoLittlewoodR_one hT hL
  have hdenpos : 0 < (taoLittlewoodR T : Real) * Real.log 2 :=
    mul_pos (by exact_mod_cast hRone) hlog2
  unfold taoZeroFreeBaseRadius taoLittlewoodWidth
  exact div_le_div_of_nonneg_left hlp.le hdenpos hden

theorem exists_taoZeroFreeRadius
    (c : Complex) {T : Real} (hL : 1 < Real.log T) :
    ∃ R ∈ Set.Ioo (taoZeroFreeBaseRadius T / 8)
        (taoZeroFreeBaseRadius T / 4),
      ∀ ρ : Complex, riemannZeta ρ = 0 → dist ρ c ≠ R := by
  have hq := taoZeroFreeBaseRadius_pos hL
  exact exists_zetaZeroFreeSphereRadius c (by linarith)

theorem closedBall_avoids_one_of_radius_lt_abs_imaginary
    {σ t R : Real} (hR : R < |t|) :
    ∀ z ∈ closedBall ((σ : Complex) + (t : Complex) * Complex.I) R,
      z ≠ 1 := by
  intro z hz hzone
  subst z
  have him := Complex.abs_im_le_norm
    ((1 : Complex) - ((σ : Complex) + (t : Complex) * Complex.I))
  have hdist := mem_closedBall.mp hz
  rw [Complex.dist_eq] at hdist
  have him' : |t| ≤
      ‖(1 : Complex) - ((σ : Complex) + (t : Complex) * Complex.I)‖ := by
    convert him using 1 <;> simp
  linarith

theorem abs_re_sub_le_dist (z c : Complex) :
    |z.re - c.re| ≤ dist z c := by
  rw [Complex.dist_eq]
  simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - c)

theorem riemannZeta_norm_le_on_littlewood_disk_sphere
    {t σ R T : Real}
    (hTpos : 0 < T) (hlogT : 0 ≤ Real.log T)
    (hσlower : 1 ≤ σ) (hσupper : σ ≤ 3 / 2)
    (hRpos : 0 < R) (hRhalf : R ≤ 1 / 2)
    (hconditions : ∀ z ∈ sphere
      ((σ : Complex) + (t : Complex) * Complex.I) R,
      TaoLittlewoodFinalFrequencyConditions (taoLogFrequency z.im))
    (hfrequency4 : ∀ z ∈ sphere
      ((σ : Complex) + (t : Complex) * Complex.I) R,
      4 ≤ taoLogFrequency z.im)
    (hfrequencyLog : ∀ z ∈ sphere
      ((σ : Complex) + (t : Complex) * Complex.I) R,
      1 ≤ Real.log (taoLogFrequency z.im))
    (hwidth : ∀ z ∈ sphere
      ((σ : Complex) + (t : Complex) * Complex.I) R,
      R ≤ taoLittlewoodWidth (taoLogFrequency z.im)
        (taoLittlewoodR (taoLogFrequency z.im)))
    (hlogCompare : ∀ z ∈ sphere
      ((σ : Complex) + (t : Complex) * Complex.I) R,
      Real.log (taoLogFrequency z.im) ≤ 2 * Real.log T) :
    ∀ z ∈ sphere ((σ : Complex) + (t : Complex) * Complex.I) R,
      ‖riemannZeta z‖ ≤ (2 : Real) ^ 48 * (Real.log T) ^ 2 := by
  intro z hz
  let c : Complex := (σ : Complex) + (t : Complex) * Complex.I
  have hdist : dist z c = R := mem_sphere.mp hz
  have hre := abs_re_sub_le_dist z c
  rw [hdist] at hre
  have hcre : c.re = σ := by simp [c]
  have hzlower : 1 - R ≤ z.re := by
    rw [hcre] at hre
    have habs := (abs_le.mp hre).1
    linarith
  have hzupper : z.re ≤ 2 := by
    rw [hcre] at hre
    have habs := (abs_le.mp hre).2
    linarith
  have hlower : 1 - taoLittlewoodWidth (taoLogFrequency z.im)
      (taoLittlewoodR (taoLogFrequency z.im)) ≤ z.re := by
    linarith [hwidth z hz]
  have hpoint := riemannZeta_norm_le_two_sided_littlewood_log_sq
    z.im z.re (hconditions z hz) (hfrequency4 z hz) (hfrequencyLog z hz)
    hlower hzupper
  have hzrepr : ((z.re : Complex) + (z.im : Complex) * Complex.I) = z := by
    apply Complex.ext <;> simp
  rw [hzrepr] at hpoint
  have hlogsq : (Real.log (taoLogFrequency z.im)) ^ 2 ≤
      (2 * Real.log T) ^ 2 := by
    exact pow_le_pow_left₀ (Real.log_nonneg (by
      have := hfrequency4 z hz
      linarith)) (hlogCompare z hz) 2
  calc
    ‖riemannZeta z‖ ≤ (2 : Real) ^ 46 *
        (Real.log (taoLogFrequency z.im)) ^ 2 := hpoint
    _ ≤ (2 : Real) ^ 46 * (2 * Real.log T) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq (by positivity)
    _ = (2 : Real) ^ 48 * (Real.log T) ^ 2 := by norm_num; ring

end

end Erdos1212Kernel
