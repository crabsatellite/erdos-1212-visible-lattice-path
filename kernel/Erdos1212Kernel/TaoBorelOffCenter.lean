import Erdos1212Kernel.TaoPerronPoleBoundary

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

theorem norm_deriv_le_twenty_four_mul_div_of_re_le_of_mem_third
    {H : Complex → Complex} {c z : Complex} {R M : Real}
    (hR : 0 < R) (hM : 0 < M)
    (hH : DifferentiableOn Complex H (ball c R))
    (hHc : H c = 0)
    (hRe : ∀ w ∈ ball c R, (H w).re ≤ M)
    (hz : z ∈ ball c (R / 3)) :
    ‖deriv H z‖ ≤ 24 * M / R := by
  let F : Complex → Complex := fun w => H (c + w)
  have hmem {w : Complex} (hw : w ∈ ball 0 R) : c + w ∈ ball c R := by
    rw [mem_ball, Complex.dist_eq]
    simpa using (mem_ball_zero_iff.mp hw)
  have hF : DifferentiableOn Complex F (ball 0 R) := by
    intro w hw
    have houter := (hH (c + w) (hmem hw)).differentiableAt
      (isOpen_ball.mem_nhds (hmem hw))
    exact (houter.comp w (by fun_prop : DifferentiableAt Complex (fun x => c + x) w)).differentiableWithinAt
  have hFmaps : MapsTo F (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    exact hRe (c + w) (hmem hw)
  have hF0 : F 0 = 0 := by simp [F, hHc]
  have hFbound : ∀ w ∈ ball 0 (R / 2), ‖F w‖ ≤ 2 * M := by
    intro w hw
    have hwR : w ∈ ball 0 R := (ball_subset_ball (by linarith)) hw
    have hb := Complex.borelCaratheodory_zero hM hF hFmaps hR hwR hF0
    have hwnorm : ‖w‖ < R / 2 := mem_ball_zero_iff.mp hw
    have hden : 0 < R - ‖w‖ := by linarith
    have hbound : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M := by
      apply (div_le_iff₀ hden).2
      nlinarith
    simpa only [hF0, dist_zero_right] using hb.trans hbound
  let w0 : Complex := z - c
  have hw0 : w0 ∈ ball 0 (R / 3) := by
    rw [mem_ball_zero_iff]
    have hzc := mem_ball.mp hz
    simpa only [w0, Complex.dist_eq, norm_sub_rev] using hzc
  have hlocal : ball w0 (R / 6) ⊆ ball 0 (R / 2) := by
    intro w hw
    rw [mem_ball] at hw ⊢
    calc
      dist w 0 ≤ dist w w0 + dist w0 0 := dist_triangle _ _ _
      _ < R / 6 + R / 3 := add_lt_add hw (mem_ball.mp hw0)
      _ = R / 2 := by ring
  have hlocalDiff : DifferentiableOn Complex F (ball w0 (R / 6)) :=
    hF.mono (hlocal.trans (ball_subset_ball (by linarith)))
  have hw0half : w0 ∈ ball 0 (R / 2) :=
    (ball_subset_ball (by linarith)) hw0
  have hlocalMaps : MapsTo F (ball w0 (R / 6))
      (closedBall (F w0) (4 * M)) := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq]
    calc
      ‖F w - F w0‖ ≤ ‖F w‖ + ‖F w0‖ := norm_sub_le _ _
      _ ≤ 2 * M + 2 * M := add_le_add (hFbound w (hlocal hw))
        (hFbound w0 hw0half)
      _ = 4 * M := by ring
  have hr : 0 < R / 6 := by positivity
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball
    hlocalDiff hlocalMaps hr
  have hzR : z ∈ ball c R :=
    (ball_subset_ball (by linarith : R / 3 ≤ R)) hz
  have hFderiv : HasDerivAt F (deriv H z) w0 := by
    have hHat := (hH z hzR).differentiableAt (isOpen_ball.mem_nhds hzR)
    have hcz : c + w0 = z := by
      dsimp [w0]
      ring
    have houter : HasDerivAt H (deriv H z) (c + w0) := by
      rw [hcz]
      exact hHat.hasDerivAt
    have hshift : HasDerivAt (fun x : Complex => c + x) 1 w0 := by
      simpa only [add_comm] using (hasDerivAt_id w0).const_add c
    have hcomp := houter.comp w0 hshift
    simpa only [F, mul_one] using hcomp
  rw [hFderiv.deriv] at hs
  exact hs.trans_eq (by field_simp; ring)

theorem norm_logDeriv_le_twenty_four_mul_div_of_log_norm_sub_le_of_mem_third
    {g : Complex → Complex} {c z : Complex} {R M : Real}
    (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn Complex g (ball c R))
    (hgn : ∀ w ∈ ball c R, g w ≠ 0)
    (hlogNorm : ∀ w ∈ ball c R,
      Real.log ‖g w‖ - Real.log ‖g c‖ ≤ M)
    (hz : z ∈ ball c (R / 3)) :
    ‖logDeriv g z‖ ≤ 24 * M / R := by
  obtain ⟨H, hHc, hH, hHre⟩ :=
    exists_normalizedAnalyticLogOn_ball_with_re hR hg hgn
  have hHdiff : DifferentiableOn Complex H (ball c R) := by
    intro w hw
    exact (hH w hw).differentiableAt.differentiableWithinAt
  have hbound := norm_deriv_le_twenty_four_mul_div_of_re_le_of_mem_third
    hR hM hHdiff hHc
      (fun w hw => (hHre w hw).le.trans (hlogNorm w hw)) hz
  have hzR : z ∈ ball c R :=
    (ball_subset_ball (by linarith : R / 3 ≤ R)) hz
  rw [(hH z hzR).deriv] at hbound
  exact hbound

end

end Erdos1212Kernel
