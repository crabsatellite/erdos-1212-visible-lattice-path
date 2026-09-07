import Erdos1212Kernel.TaoAnalyticNonzeroLog
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Schwarz

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

/-- Borel--Carathéodory followed by Schwarz gives the derivative bound
at the center. This is the quantitative engine for the residual
logarithmic derivative. -/
theorem norm_deriv_le_four_mul_div_of_re_le
    {H : Complex → Complex} {c : Complex} {R M : Real}
    (hR : 0 < R) (hM : 0 < M)
    (hH : DifferentiableOn Complex H (ball c R))
    (hHc : H c = 0)
    (hRe : ∀ z ∈ ball c R, (H z).re ≤ M) :
    ‖deriv H c‖ ≤ 4 * M / R := by
  let F : Complex → Complex := fun w => H (c + w)
  have hmem {w : Complex} (hw : w ∈ ball 0 R) : c + w ∈ ball c R := by
    rw [mem_ball, Complex.dist_eq]
    simpa using (mem_ball_zero_iff.mp hw)
  have hF : DifferentiableOn Complex F (ball 0 R) := by
    intro w hw
    have houter := (hH (c + w) (hmem hw)).differentiableAt
      (isOpen_ball.mem_nhds (hmem hw))
    exact (houter.comp w (by fun_prop : DifferentiableAt Complex (fun x => c + x) w)).differentiableWithinAt
  have hFmaps : MapsTo F (ball 0 R) {z | z.re ≤ M} := by
    intro w hw
    exact hRe (c + w) (hmem hw)
  have hF0 : F 0 = 0 := by simp [F, hHc]
  have hhalf : 0 < R / 2 := by positivity
  have hinner : DifferentiableOn Complex F (ball 0 (R / 2)) :=
    hF.mono (ball_subset_ball (by linarith))
  have hMapsInner : MapsTo F (ball 0 (R / 2)) (closedBall (F 0) (2 * M)) := by
    intro w hw
    have hwR : w ∈ ball 0 R := (ball_subset_ball (by linarith)) hw
    have hb := Complex.borelCaratheodory_zero hM hF hFmaps hR hwR hF0
    have hwnorm : ‖w‖ < R / 2 := mem_ball_zero_iff.mp hw
    have hden : 0 < R - ‖w‖ := by linarith
    have hbound : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M := by
      apply (div_le_iff₀ hden).2
      nlinarith
    rw [mem_closedBall, hF0, dist_zero_right]
    exact hb.trans hbound
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball hinner hMapsInner hhalf
  have hHderiv : HasDerivAt F (deriv H c) 0 := by
    have hc : c ∈ ball c R := mem_ball_self hR
    have hHat := (hH c hc).differentiableAt (isOpen_ball.mem_nhds hc)
    have houter : HasDerivAt H (deriv H c) (c + 0) := by
      simpa only [add_zero] using hHat.hasDerivAt
    have hshift : HasDerivAt (fun x : Complex => c + x) 1 0 := by
      simpa only [add_comm] using (hasDerivAt_id 0).const_add c
    have hcomp := houter.comp 0 hshift
    simpa only [F, mul_one] using hcomp
  rw [hHderiv.deriv] at hs
  exact hs.trans_eq (by field_simp; ring)

/-- Quantitative logarithmic-derivative bound for a nonvanishing
holomorphic function on a disk, stated directly in terms of log-norm
growth from the center. -/
theorem norm_logDeriv_le_four_mul_div_of_log_norm_sub_le
    {g : Complex → Complex} {c : Complex} {R M : Real}
    (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn Complex g (ball c R))
    (hgn : ∀ z ∈ ball c R, g z ≠ 0)
    (hlogNorm : ∀ z ∈ ball c R,
      Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M) :
    ‖logDeriv g c‖ ≤ 4 * M / R := by
  obtain ⟨H, hHc, hH, hHre⟩ :=
    exists_normalizedAnalyticLogOn_ball_with_re hR hg hgn
  have hHdiff : DifferentiableOn Complex H (ball c R) := by
    intro z hz
    exact (hH z hz).differentiableAt.differentiableWithinAt
  have hbound := norm_deriv_le_four_mul_div_of_re_le hR hM hHdiff hHc
    (fun z hz => (hHre z hz).le.trans (hlogNorm z hz))
  rw [(hH c (mem_ball_self hR)).deriv] at hbound
  exact hbound

end

end Erdos1212Kernel
