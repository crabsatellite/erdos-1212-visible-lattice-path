import Erdos1212Kernel.TaoLittlewoodScaledRadius

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 700000

theorem exists_taoAdjustedResidual_of_radius_and_nearby_conditions
    (y η q : Real) (hη : 0 < η) (hq : 0 < q)
    (hL : 1 < Real.log (taoLogFrequency y))
    (hqhalf : q / 4 ≤ 1 / 2) (hηhalf : η ≤ 1 / 2) (hqimag : q / 4 < |y|)
    (hnear : ∀ U ∈ Set.Icc (taoLogFrequency y - 1) (taoLogFrequency y + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧ 4 ≤ U ∧ 1 ≤ Real.log U ∧
      q / 4 ≤ taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency y)) :
    ∃ R : Real, ∃ G : Complex → Complex,
      R ∈ Set.Ioo (q / 8) (q / 4) ∧
      (∀ z ∈ closedBall (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R, G z ≠ 0) ∧
      taoZetaLogDerivative (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R =
        -logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) ∧
      ‖logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I)‖ ≤
        4 * (1 + Real.log ((2 : Real) ^ 48 * (Real.log (taoLogFrequency y)) ^ 2) +
          4 * Real.log (1 + 1 / η)) / R := by
  let T := taoLogFrequency y
  let σ := 1 + η
  let c : Complex := (σ : Complex) + (y : Complex) * Complex.I
  let C : Real := (2 : Real) ^ 48 * (Real.log T) ^ 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hy : y ≠ 0 := by intro hy; subst y; simp at hqimag; linarith
  have hT : 0 < T := taoLogFrequency_pos hy
  obtain ⟨R, hR, hSphere⟩ := exists_zetaZeroFreeSphereRadius c (show q / 8 < q / 4 by linarith)
  have hRpos : 0 < R := by linarith [hR.1]
  have hRhalf : R ≤ 1 / 2 := hR.2.le.trans hqhalf
  have hAvoid : ∀ z ∈ closedBall c R, z ≠ 1 :=
    closedBall_avoids_one_of_radius_lt_abs_imaginary (hR.2.trans hqimag)
  have hnearAt (z : Complex) (hz : z ∈ sphere c R) :
      TaoLittlewoodFinalFrequencyConditions (taoLogFrequency z.im) ∧
      4 ≤ taoLogFrequency z.im ∧ 1 ≤ Real.log (taoLogFrequency z.im) ∧
      q / 4 ≤ taoLittlewoodWidth (taoLogFrequency z.im) (taoLittlewoodR (taoLogFrequency z.im)) ∧
      Real.log (taoLogFrequency z.im) ≤ 2 * Real.log T := by
    have hf := abs_taoLogFrequency_sub_le_dist_imaginary_centers z σ y
    rw [mem_sphere.mp hz] at hf
    have habs : |taoLogFrequency z.im - T| ≤ 1 := hf.trans (by linarith)
    apply hnear
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  have hBoundary : ∀ z ∈ sphere c R, ‖riemannZeta z‖ ≤ C := by
    apply riemannZeta_norm_le_on_littlewood_disk_sphere hT
      (show 0 ≤ Real.log T by dsimp [T]; linarith) hσ.le
      (show σ ≤ 3 / 2 by dsimp [σ]; linarith) hRpos hRhalf
    · intro z hz; exact (hnearAt z hz).1
    · intro z hz; exact (hnearAt z hz).2.1
    · intro z hz; exact (hnearAt z hz).2.2.1
    · intro z hz; exact hR.2.le.trans (hnearAt z hz).2.2.2.1
    · intro z hz; exact (hnearAt z hz).2.2.2.2
  obtain ⟨G, _hG, hGnz, _hGupper, _hcenter, hexact, hbound⟩ :=
    exists_taoZetaAdjustedResidual_logDeriv_bound σ y R C hσ hRpos hAvoid hSphere hBoundary
  refine ⟨R, G, hR, hGnz, hexact, ?_⟩
  simpa only [σ, C, T, add_sub_cancel_left] using hbound

theorem taoCanonicalResidual_raw_le_scaled_linear
    {a η D T R : Real} (ha : 0 < a) (hD : 0 < D)
    (hL : 1 < Real.log T) (hll : 1 ≤ Real.log (Real.log T))
    (hR : D * taoZeroFreeBaseRadius T / 8 < R)
    (hη : a / Real.log T ≤ η) :
    4 * (1 + Real.log ((2 : Real) ^ 48 * (Real.log T) ^ 2) +
      4 * Real.log (1 + 1 / η)) / R ≤
        (taoCanonicalResidualConstant a / D) * Real.log T := by
  have hscaled : taoZeroFreeBaseRadius T / 8 < R / D := by
    apply (lt_div_iff₀ hD).mpr
    nlinarith only [hR]
  have ht := div_le_div_of_nonneg_right
    (taoCanonicalResidual_raw_le_linear ha hL hll hscaled hη) hD.le
  convert ht using 1 <;> field_simp <;> ring

theorem exists_taoScaledAdjustedResidual_common_shift
    (D y η a : Real) (hD : 0 < D) (ha : 0 < a)
    (hL : 1 < Real.log (taoLogFrequency y))
    (hll : 1 ≤ Real.log (Real.log (taoLogFrequency y)))
    (hqhalf : D * taoZeroFreeBaseRadius (taoLogFrequency y) / 4 ≤ 1 / 2)
    (hηhalf : η ≤ 1 / 2)
    (hqimag : D * taoZeroFreeBaseRadius (taoLogFrequency y) / 4 < |y|)
    (hηlower : a / Real.log (taoLogFrequency y) ≤ η)
    (hnear : ∀ U ∈ Set.Icc (taoLogFrequency y - 1) (taoLogFrequency y + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧ 4 ≤ U ∧ 1 ≤ Real.log U ∧
      D * taoZeroFreeBaseRadius (taoLogFrequency y) / 4 ≤ taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency y)) :
    ∃ R : Real, ∃ G : Complex → Complex,
      R ∈ Set.Ioo (D * taoZeroFreeBaseRadius (taoLogFrequency y) / 8)
        (D * taoZeroFreeBaseRadius (taoLogFrequency y) / 4) ∧
      (∀ z ∈ closedBall (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R, G z ≠ 0) ∧
      taoZetaLogDerivative (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) +
        taoZetaAdjustedReciprocalSum (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R =
        -logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) ∧
      ‖logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I)‖ ≤
        (taoCanonicalResidualConstant a / D) * Real.log (taoLogFrequency y) := by
  have hη : 0 < η := (div_pos ha (by linarith)).trans_le hηlower
  have hq : 0 < D * taoZeroFreeBaseRadius (taoLogFrequency y) :=
    mul_pos hD (taoZeroFreeBaseRadius_pos hL)
  obtain ⟨R, G, hR, hG, heq, hraw⟩ := exists_taoAdjustedResidual_of_radius_and_nearby_conditions
    y η (D * taoZeroFreeBaseRadius (taoLogFrequency y)) hη hq hL hqhalf hηhalf hqimag hnear
  exact ⟨R, G, hR, hG, heq, hraw.trans
    (taoCanonicalResidual_raw_le_scaled_linear ha hD hL hll hR.1 hηlower)⟩

end

end Erdos1212Kernel
