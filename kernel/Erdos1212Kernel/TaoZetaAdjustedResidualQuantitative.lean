import Erdos1212Kernel.TaoZetaRightHalfPlaneLower

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

/-- Quantitative Borel bound for the actual adjusted zero-free residual.
The center lower bound is supplied by the modulus-one `3-4-1` Euler
product, while `C` is any zeta bound on the selected boundary sphere. -/
theorem exists_taoZetaAdjustedResidual_logDeriv_bound
    (σ t R C : Real) (hσ : 1 < σ) (hR : 0 < R)
    (hAvoid : ∀ z ∈ closedBall ((σ : Complex) + (t : Complex) * Complex.I) R,
      z ≠ 1)
    (hSphere : ∀ z : Complex, riemannZeta z = 0 →
      dist z ((σ : Complex) + (t : Complex) * Complex.I) ≠ R)
    (hC : ∀ z ∈ sphere ((σ : Complex) + (t : Complex) * Complex.I) R,
      ‖riemannZeta z‖ ≤ C) :
    ∃ G : Complex → Complex,
      AnalyticOnNhd Complex G
        (closedBall ((σ : Complex) + (t : Complex) * Complex.I) R) ∧
      (∀ z ∈ closedBall ((σ : Complex) + (t : Complex) * Complex.I) R,
        G z ≠ 0) ∧
      (∀ z ∈ closedBall ((σ : Complex) + (t : Complex) * Complex.I) R,
        ‖G z‖ ≤ C) ∧
      ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
        ‖G ((σ : Complex) + (t : Complex) * Complex.I)‖ ∧
      taoZetaLogDerivative ((σ : Complex) + (t : Complex) * Complex.I) +
          taoZetaAdjustedReciprocalSum
            ((σ : Complex) + (t : Complex) * Complex.I) R =
        -logDeriv G ((σ : Complex) + (t : Complex) * Complex.I) ∧
      ‖logDeriv G ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
        4 * (1 + Real.log C + 4 * Real.log (1 + 1 / (σ - 1))) / R := by
  let c : Complex := (σ : Complex) + (t : Complex) * Complex.I
  let B : Real := 1 + 1 / (σ - 1)
  let M : Real := 1 + Real.log C + 4 * Real.log B
  have hcre : 1 < c.re := by simp [c, hσ]
  have hcne : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hcre
  obtain ⟨G, hG, hGnz, hGupper, hcenter, hexact⟩ :=
    exists_taoZetaAdjustedResidual_norm_le hR hAvoid hSphere hcne hC
  have hcenterMem : c ∈ closedBall c R := by simp [hR.le]
  have hzetaPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcne
  have hGcenterPos : 0 < ‖G c‖ := by linarith
  have hCpos : 0 < C := hGcenterPos.trans_le (hGupper c hcenterMem)
  have hBpos : 0 < B := by
    dsimp [B]
    have hden : 0 < σ - 1 := by linarith
    have hinv : 0 ≤ 1 / (σ - 1) := by positivity
    linarith
  have hzetaLower : -4 * Real.log B ≤ Real.log ‖riemannZeta c‖ := by
    simpa only [B, c] using
      neg_four_mul_log_pseriesBound_le_log_norm_riemannZeta σ t hσ
  have hzetaLogLeG : Real.log ‖riemannZeta c‖ ≤ Real.log ‖G c‖ :=
    Real.log_le_log hzetaPos hcenter
  have hGLogLeC : Real.log ‖G c‖ ≤ Real.log C :=
    Real.log_le_log hGcenterPos (hGupper c hcenterMem)
  have hcore : 0 ≤ Real.log C + 4 * Real.log B := by linarith
  have hMpos : 0 < M := by
    dsimp [M]
    linarith
  have hlogNorm : ∀ z ∈ ball c R,
      Real.log ‖G z‖ - Real.log ‖G c‖ ≤ M := by
    intro z hz
    have hzClosed : z ∈ closedBall c R := ball_subset_closedBall hz
    have hGzPos : 0 < ‖G z‖ := norm_pos_iff.mpr (hGnz z hzClosed)
    have hGzLogLeC : Real.log ‖G z‖ ≤ Real.log C :=
      Real.log_le_log hGzPos (hGupper z hzClosed)
    dsimp [M]
    linarith
  have hlogDeriv := norm_logDeriv_le_four_mul_div_of_log_norm_sub_le
    hR hMpos (hG.differentiableOn.mono ball_subset_closedBall)
    (fun z hz => hGnz z (ball_subset_closedBall hz)) hlogNorm
  refine ⟨G, hG, hGnz, hGupper, hcenter, hexact, ?_⟩
  simpa only [M, B, c] using hlogDeriv

end

end Erdos1212Kernel
