import Erdos1212Kernel.TaoZetaNearbyFrequency

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

/-- One high-frequency adjusted residual, with the radius selected from
the canonical conservative Littlewood scale and every boundary point
handled by the two-sided log-squared zeta bound. -/
theorem exists_taoCanonicalAdjustedResidual_of_nearby_conditions
    (a t : Real) (ha : 0 < a)
    (hL : 1 < Real.log (taoLogFrequency t))
    (hqhalf : taoZeroFreeBaseRadius (taoLogFrequency t) / 4 ≤ 1 / 2)
    (hahalf : a / Real.log (taoLogFrequency t) ≤ 1 / 2)
    (hqimag : taoZeroFreeBaseRadius (taoLogFrequency t) / 4 < |t|)
    (hnear : ∀ U ∈ Set.Icc (taoLogFrequency t - 1)
        (taoLogFrequency t + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius (taoLogFrequency t) / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency t)) :
    ∃ R : Real, ∃ G : Complex → Complex,
      R ∈ Set.Ioo (taoZeroFreeBaseRadius (taoLogFrequency t) / 8)
        (taoZeroFreeBaseRadius (taoLogFrequency t) / 4) ∧
      (∀ ρ : Complex, riemannZeta ρ = 0 →
        dist ρ
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I) ≠ R) ∧
      AnalyticOnNhd Complex G
        (closedBall
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I) R) ∧
      (∀ z ∈ closedBall
        (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
          (t : Complex) * Complex.I) R, G z ≠ 0) ∧
      taoZetaLogDerivative
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I) +
          taoZetaAdjustedReciprocalSum
            (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
              (t : Complex) * Complex.I) R =
        -logDeriv G
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I) ∧
      ‖logDeriv G
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I)‖ ≤
        4 * (1 + Real.log
            ((2 : Real) ^ 48 * (Real.log (taoLogFrequency t)) ^ 2) +
          4 * Real.log
            (1 + 1 / ((1 + a / Real.log (taoLogFrequency t)) - 1))) / R := by
  let T : Real := taoLogFrequency t
  let L : Real := Real.log T
  let σ : Real := 1 + a / L
  let C : Real := (2 : Real) ^ 48 * L ^ 2
  let c : Complex := (σ : Complex) + (t : Complex) * Complex.I
  have hqpos := taoZeroFreeBaseRadius_pos hL
  have ht : t ≠ 0 := by
    intro ht
    subst t
    norm_num at hqimag
    linarith
  have hTpos : 0 < T := by simpa only [T] using taoLogFrequency_pos ht
  have hLpos : 0 < L := by unfold L; linarith
  have hσ1 : 1 < σ := by unfold σ; have := div_pos ha hLpos; linarith
  have hσupper : σ ≤ 3 / 2 := by unfold σ; linarith
  obtain ⟨R, hRmem, hSphere⟩ := exists_taoZeroFreeRadius c hL
  have hRpos : 0 < R := by linarith [hRmem.1]
  have hRhalf : R ≤ 1 / 2 := hRmem.2.le.trans hqhalf
  have hAvoid : ∀ z ∈ closedBall c R, z ≠ 1 := by
    exact closedBall_avoids_one_of_radius_lt_abs_imaginary
      (hRmem.2.trans hqimag)
  have hnearAt (z : Complex) (hz : z ∈ sphere c R) :
      TaoLittlewoodFinalFrequencyConditions (taoLogFrequency z.im) ∧
      4 ≤ taoLogFrequency z.im ∧
      1 ≤ Real.log (taoLogFrequency z.im) ∧
      taoZeroFreeBaseRadius T / 4 ≤
        taoLittlewoodWidth (taoLogFrequency z.im)
          (taoLittlewoodR (taoLogFrequency z.im)) ∧
      Real.log (taoLogFrequency z.im) ≤ 2 * Real.log T := by
    have hfreq := abs_taoLogFrequency_sub_le_dist_imaginary_centers z σ t
    rw [mem_sphere.mp hz] at hfreq
    have hnearOne : |taoLogFrequency z.im - T| ≤ 1 := by
      exact hfreq.trans (hRmem.2.le.trans (hqhalf.trans (by norm_num)))
    have hUmem : taoLogFrequency z.im ∈ Set.Icc (T - 1) (T + 1) := by
      rw [Set.mem_Icc]
      rcases abs_le.mp hnearOne with ⟨hl, hu⟩
      constructor <;> linarith
    simpa only [T] using hnear (taoLogFrequency z.im) (by simpa only [T] using hUmem)
  have hBoundary : ∀ z ∈ sphere c R, ‖riemannZeta z‖ ≤ C := by
    apply riemannZeta_norm_le_on_littlewood_disk_sphere hTpos hLpos.le
      hσ1.le hσupper hRpos hRhalf
    · intro z hz
      exact (hnearAt z hz).1
    · intro z hz
      exact (hnearAt z hz).2.1
    · intro z hz
      exact (hnearAt z hz).2.2.1
    · intro z hz
      exact hRmem.2.le.trans (hnearAt z hz).2.2.2.1
    · intro z hz
      exact (hnearAt z hz).2.2.2.2
  obtain ⟨G, hG, hGnz, _hGupper, _hcenter, hexact, hbound⟩ :=
    exists_taoZetaAdjustedResidual_logDeriv_bound σ t R C hσ1 hRpos
      hAvoid hSphere hBoundary
  refine ⟨R, G, ?_, hSphere, ?_, ?_, ?_, ?_⟩
  · simpa only [T] using hRmem
  · simpa only [c, σ, L, T] using hG
  · simpa only [c, σ, L, T] using hGnz
  · simpa only [c, σ, L, T] using hexact
  · simpa only [c, σ, C, L, T] using hbound

end

end Erdos1212Kernel
