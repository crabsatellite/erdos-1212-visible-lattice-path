import Erdos1212Kernel.IwaniecAuxiliaryWeightRatio

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem iwaniecAuxWeightRatio_pos {s : Real} (hs : 3 ≤ s) : 0 < iwaniecAuxWeightRatio s :=
  div_pos (iwaniecAuxMWindowWeight_pos (by linarith)) (iwaniecAuxMWindowWeight_pos (by linarith))

theorem iwaniecAuxEta_weighted_point {x : Real} (hx : 3 ≤ x) :
    iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x =
      iwaniecAuxMWindowKernel (x - 1) := by
  unfold iwaniecAuxWeightRatio iwaniecAuxEta iwaniecAuxMWindowKernel
  field_simp [(iwaniecAuxMWindowWeight_pos (s := x) (by linarith)).ne',
    (iwaniecAuxM_pos (s := x) (by linarith)).ne']

theorem iwaniecAuxEta_weighted_window {s : Real} (hs : 4 ≤ s) :
    (∫ x in (s - 1)..s,
      iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x) =
      iwaniecAuxMCoefficient (s - 1) * iwaniecAuxM (s - 1) := by
  have heq : (∫ x in (s - 1)..s,
      iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x) =
      ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel (x - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (show s - 1 ≤ s by linarith)] at hx
    exact iwaniecAuxEta_weighted_point (by linarith [hx.1])
  rw [heq, intervalIntegral.integral_comp_sub_right]
  exact (iwaniecAuxM_window_identity (s := s - 1) (by linarith)).symm

theorem iwaniecAuxWeightRatio_delay_balance {s : Real} (hs : 4 ≤ s) :
    iwaniecAuxWeightRatio (s - 1) * iwaniecAuxMCoefficient s * iwaniecAuxDelayKernel s =
      iwaniecAuxMCoefficient (s - 1) * iwaniecAuxDelayKernel (s - 1) := by
  rw [mul_assoc, iwaniecAuxMCoefficient_mul_delay (by linarith : 3 ≤ s),
    iwaniecAuxMCoefficient_mul_delay (by linarith : 3 ≤ s - 1)]
  unfold iwaniecAuxWeightRatio
  exact div_mul_cancel₀ _ (iwaniecAuxMWindowWeight_pos (by linarith : 2 ≤ s - 1)).ne'

theorem iwaniecAuxM_mul_hazard {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM s * iwaniecAuxHazard s = iwaniecAuxM (s - 1) * iwaniecAuxDelayKernel s := by
  unfold iwaniecAuxHazard iwaniecAuxEta
  field_simp [(iwaniecAuxM_pos (by linarith : 2 ≤ s)).ne']

/-- A monotone past window forces a strictly positive next hazard
increment. This is the missing producer in the first-contact proof of
eta monotonicity; it uses both exact weighted M windows. -/
theorem iwaniecAuxHazard_lag_lt_of_eta_window
    {s : Real} (hs : 4 ≤ s)
    (heta : ∀ x ∈ Set.Icc (s - 1) s, iwaniecAuxEta (s - 1) ≤ iwaniecAuxEta x) :
    iwaniecAuxHazard (s - 1) < iwaniecAuxHazard s := by
  let c := iwaniecAuxWeightRatio (s - 1) * iwaniecAuxEta (s - 1)
  have hcLeft : ContinuousOn (fun x => c * iwaniecAuxMWindowKernel x) (Set.Icc (s - 1) s) := by
    apply (continuousOn_const.mul iwaniecAuxMWindowKernel_continuousOn).mono
    intro x hx
    change (1 : Real) < x
    linarith [hx.1]
  have hcRight : ContinuousOn
      (fun x => iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x)
      (Set.Icc (s - 1) s) := by
    have hwr : ContinuousOn iwaniecAuxWeightRatio (Set.Icc (s - 1) s) := by
      intro x hx
      exact (iwaniecAuxWeightRatio_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt
    have her := iwaniecAuxEta_continuousOn.mono (show Set.Icc (s - 1) s ⊆ Set.Ici (3 : Real) by
      intro x hx
      change (3 : Real) ≤ x
      linarith [hx.1])
    apply (hwr.mul her).mul (iwaniecAuxMWindowKernel_continuousOn.mono _)
    intro x hx
    change (1 : Real) < x
    linarith [hx.1]
  have hpoint : ∀ x ∈ Set.Ioc (s - 1) s,
      c * iwaniecAuxMWindowKernel x <
        iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x := by
    intro x hx
    have hxThree : 3 ≤ x := by linarith [hx.1]
    have hratio := iwaniecAuxWeightRatio_strictMonoOn
      (show (3 : Real) ≤ s - 1 by linarith) hxThree hx.1
    have hmul := (mul_lt_mul_of_pos_right hratio (iwaniecAuxEta_pos (s := s - 1) (by linarith))).trans_le
      (mul_le_mul_of_nonneg_left (heta x ⟨hx.1.le, hx.2⟩) (iwaniecAuxWeightRatio_pos hxThree).le)
    exact mul_lt_mul_of_pos_right hmul
      (mul_pos (iwaniecAuxMWindowWeight_pos (by linarith)) (iwaniecAuxM_pos (by linarith)))
  have hi : (∫ x in (s - 1)..s, c * iwaniecAuxMWindowKernel x) <
      ∫ x in (s - 1)..s,
        iwaniecAuxWeightRatio x * iwaniecAuxEta x * iwaniecAuxMWindowKernel x := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcLeft hcRight
    · intro x hx
      exact (hpoint x hx).le
    · exact ⟨s, ⟨by linarith, le_rfl⟩, hpoint s ⟨by linarith, le_rfl⟩⟩
  rw [intervalIntegral.integral_const_mul, iwaniecAuxEta_weighted_window hs] at hi
  have hw := iwaniecAuxM_window_identity (s := s) (by linarith)
  change iwaniecAuxMCoefficient s * iwaniecAuxM s =
    ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hw
  rw [← hw] at hi
  have hscaled := mul_lt_mul_of_pos_right hi (iwaniecAuxDelayKernel_pos (s := s) (by linarith))
  have hleft : (c * (iwaniecAuxMCoefficient s * iwaniecAuxM s)) * iwaniecAuxDelayKernel s =
      (iwaniecAuxMCoefficient (s - 1) * iwaniecAuxM s) * iwaniecAuxHazard (s - 1) := by
    calc
      _ = (iwaniecAuxWeightRatio (s - 1) * iwaniecAuxMCoefficient s * iwaniecAuxDelayKernel s) *
          iwaniecAuxM s * iwaniecAuxEta (s - 1) := by dsimp [c]; ring
      _ = _ := by rw [iwaniecAuxWeightRatio_delay_balance hs]; unfold iwaniecAuxHazard; ring
  have hright : (iwaniecAuxMCoefficient (s - 1) * iwaniecAuxM (s - 1)) * iwaniecAuxDelayKernel s =
      (iwaniecAuxMCoefficient (s - 1) * iwaniecAuxM s) * iwaniecAuxHazard s := by
    rw [mul_assoc, ← iwaniecAuxM_mul_hazard (by linarith : 3 ≤ s)]
    ring
  rw [hleft, hright] at hscaled
  exact (mul_lt_mul_iff_right₀
    (mul_pos (iwaniecAuxMCoefficient_pos (by linarith : 3 ≤ s - 1))
      (iwaniecAuxM_pos (by linarith : 2 ≤ s)))).mp hscaled

end

end Erdos1212Kernel
