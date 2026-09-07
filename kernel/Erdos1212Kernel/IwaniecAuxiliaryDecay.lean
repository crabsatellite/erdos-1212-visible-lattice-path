import Erdos1212Kernel.IwaniecAuxiliaryProfiles

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniecAuxMWindowKernel_le_three {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxMWindowKernel s ≤ 3 := by
  have hweight : iwaniecAuxMWindowWeight s ≤ 1 := by
    unfold iwaniecAuxMWindowWeight
    have hnonneg : 0 ≤ (1 : Real) / (2 * s ^ 2) :=
      div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg s))
    linarith
  exact (mul_le_of_le_one_left (iwaniecAuxM_pos hs).le hweight).trans
    (iwaniecAuxM_le_three hs)

/-- A coarse consequence of the exact source window, used only to
justify the zero boundary term in the improper-integral identities. -/
theorem iwaniecAuxM_le_reciprocal {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM s ≤ 3 / (s - 2) := by
  have hint := iwaniecIntervalIntegrable_of_continuousOn_one _
    iwaniecAuxMWindowKernel_continuousOn (a := s - 1) (b := s) (by linarith) (by linarith)
  have hbound : (∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x) ≤ 3 := by
    have h := intervalIntegral.integral_mono_on (show s - 1 ≤ s by linarith)
      hint (g := fun _x : Real => (3 : Real)) intervalIntegrable_const
      (fun x hx => iwaniecAuxMWindowKernel_le_three (by linarith [hx.1]))
    simpa only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul, one_mul] using h
  have hcoef : s - 2 ≤ iwaniecAuxMCoefficient s := by
    unfold iwaniecAuxMCoefficient
    rw [le_div_iff₀ (show 0 < s by linarith)]
    nlinarith
  have hwindow := iwaniecAuxM_window_identity hs
  change iwaniecAuxMCoefficient s * iwaniecAuxM s =
    ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hwindow
  have hmul := mul_le_mul_of_nonneg_right hcoef (iwaniecAuxM_pos (s := s) (by linarith)).le
  rw [hwindow] at hmul
  rw [le_div_iff₀ (show 0 < s - 2 by linarith)]
  nlinarith

theorem tendsto_iwaniecAuxM_atTop_zero : Tendsto iwaniecAuxM atTop (nhds 0) := by
  have hshift : Tendsto (fun s : Real => s - 2) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-2 : Real) tendsto_id
  have hmajor : Tendsto (fun s : Real => (3 : Real) / (s - 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hshift
  apply squeeze_zero' (g := fun s : Real => 3 / (s - 2))
  · filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    exact (iwaniecAuxM_pos (by linarith)).le
  · filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    exact iwaniecAuxM_le_reciprocal hs
  · exact hmajor

theorem tendsto_iwaniecAuxLower_atTop_zero :
    Tendsto iwaniecAuxLower atTop (nhds 0) := by
  apply squeeze_zero' (g := fun s : Real => 2 * iwaniecAuxM s / 3)
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact (iwaniecAuxLower_pos hs).le
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact (iwaniecAuxLower_bounds hs).2
  · simpa using (tendsto_iwaniecAuxM_atTop_zero.const_mul 2).div_const 3

theorem tendsto_iwaniecAuxUpper_atTop_zero :
    Tendsto iwaniecAuxUpper atTop (nhds 0) := by
  apply squeeze_zero' (g := fun s : Real => 2 * iwaniecAuxM s / 3)
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact (iwaniecAuxUpper_pos (by linarith)).le
  · filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
    exact (iwaniecAuxUpper_bounds hs).2
  · simpa using (tendsto_iwaniecAuxM_atTop_zero.const_mul 2).div_const 3

theorem tendsto_iwaniecAuxG_atTop_zero (rank : Nat) :
    Tendsto (iwaniecAuxG rank) atTop (nhds 0) := by
  unfold iwaniecAuxG
  split
  · exact tendsto_iwaniecAuxLower_atTop_zero
  · exact tendsto_iwaniecAuxUpper_atTop_zero

end

end Erdos1212Kernel
