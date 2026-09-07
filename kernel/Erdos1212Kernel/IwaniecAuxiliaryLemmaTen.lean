import Erdos1212Kernel.IwaniecAuxiliaryEtaMonotonicity
import Mathlib.Analysis.Asymptotics.Defs

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxEtaKernel_continuousOn :
    ContinuousOn (fun x : Real => iwaniecAuxEta x * x / (x - 1) ^ 2) (Set.Ici (3 : Real)) := by
  apply (iwaniecAuxEta_continuousOn.mul continuousOn_id).div
    ((continuousOn_id.sub continuousOn_const).pow 2)
  intro x hx
  exact pow_ne_zero 2 (show x - 1 ≠ 0 by linarith [hx.out])

theorem iwaniecAuxDelayKernel_lt_window_bound
    {s x : Real} (hs : 4 < s) (hx : s - 1 ≤ x) :
    iwaniecAuxDelayKernel x < 1 / (s - 3) := by
  have hxPos : 0 < x := by linarith
  unfold iwaniecAuxDelayKernel
  rw [div_lt_div_iff₀ (sq_pos_of_pos (show 0 < x - 1 by linarith)) (show 0 < s - 3 by linarith)]
  have hprod := mul_nonneg hxPos.le (show 0 ≤ x - (s - 1) by linarith)
  nlinarith

/-- The exact integral comparison used in source Lemma 10. Eta's
monotonicity is now supplied by its producer, not by a premise. -/
theorem log_iwaniecAuxEta_lt_endpoint {s : Real} (hs : 4 < s) :
    Real.log (iwaniecAuxEta s) < iwaniecAuxEta s / (s - 3) := by
  rw [log_iwaniecAuxEta_eq_integral hs]
  have hc := iwaniecAuxEtaKernel_continuousOn.mono (show Set.Icc (s - 1) s ⊆ Set.Ici (3 : Real) by
    intro x hx
    change (3 : Real) ≤ x
    linarith [hx.1])
  have hpoint : ∀ x ∈ Set.Icc (s - 1) s,
      iwaniecAuxEta x * x / (x - 1) ^ 2 < iwaniecAuxEta s / (s - 3) := by
    intro x hx
    have hxThree : 3 ≤ x := by linarith [hx.1]
    have hmono := iwaniecAuxEta_monotoneOn hxThree (show 3 ≤ s by linarith) hx.2
    have hfirst := mul_le_mul_of_nonneg_right hmono (iwaniecAuxDelayKernel_pos (by linarith : 2 ≤ x)).le
    have hlast := mul_lt_mul_of_pos_left (iwaniecAuxDelayKernel_lt_window_bound hs hx.1)
      (iwaniecAuxEta_pos (by linarith : 3 ≤ s))
    simpa only [iwaniecAuxDelayKernel, ← mul_div_assoc, mul_one] using hfirst.trans_lt hlast
  have hi : (∫ x in (s - 1)..s, iwaniecAuxEta x * x / (x - 1) ^ 2) <
      ∫ _x in (s - 1)..s, iwaniecAuxEta s / (s - 3) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hc continuousOn_const
    · intro x hx
      exact (hpoint x ⟨hx.1.le, hx.2⟩).le
    · exact ⟨s, ⟨by linarith, le_rfl⟩, hpoint s ⟨by linarith, le_rfl⟩⟩
  simpa only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul, one_mul] using hi

theorem iwaniecAuxEta_gt_shift_log {s : Real} (hs : 4 < s) :
    (s - 3) * Real.log (s - 2) < iwaniecAuxEta s := by
  have hlog := log_iwaniecAuxEta_lower (s := s) (by linarith)
  have hbound := log_iwaniecAuxEta_lt_endpoint hs
  rw [lt_div_iff₀ (show 0 < s - 3 by linarith)] at hbound
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ s - 3 by linarith)
  nlinarith

theorem iwaniecAuxEta_gt_quarter_s_log {s : Real} (hs : 6 ≤ s) :
    s * Real.log s / 4 < iwaniecAuxEta s := by
  have hsPos : 0 < s := by linarith
  have hsubPos : 0 < s - 2 := by linarith
  have hsquare : s ≤ (s - 2) ^ 2 := by nlinarith
  have hlog := Real.log_le_log hsPos hsquare
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogNonneg : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hscale : s / 2 ≤ s - 3 := by linarith
  have hlogScale : Real.log s / 2 ≤ Real.log (s - 2) := by linarith
  have hmul := mul_le_mul hscale hlogScale (by positivity : 0 ≤ Real.log s / 2)
    (show 0 ≤ s - 3 by linarith)
  have hbound := iwaniecAuxEta_gt_shift_log (s := s) (by linarith)
  nlinarith

/-- An explicit absolute bound proving the O(1) in source Lemma 10. -/
theorem iwaniecAuxLemmaTen_bound {s : Real} (hs : 6 ≤ s) :
    s * Real.log s / iwaniecAuxEta s < 4 := by
  rw [div_lt_iff₀ (iwaniecAuxEta_pos (by linarith : 3 ≤ s))]
  linarith [iwaniecAuxEta_gt_quarter_s_log hs]

theorem iwaniecAuxM_s_log_lt_four_lag {s : Real} (hs : 6 ≤ s) :
    iwaniecAuxM s * s * Real.log s < 4 * iwaniecAuxM (s - 1) := by
  have h := iwaniecAuxEta_gt_quarter_s_log hs
  unfold iwaniecAuxEta at h
  rw [lt_div_iff₀ (iwaniecAuxM_pos (by linarith : 2 ≤ s))] at h
  nlinarith

/-- Source Lemma 10 in its original M-normalization, not an eta alias. -/
theorem iwaniecAuxLemmaTen :
    (fun s : Real => iwaniecAuxM s * s * Real.log s / iwaniecAuxM (s - 1))
      =O[atTop] (fun _s : Real => (1 : Real)) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (6 : Real)] with s hs
  have hM := iwaniecAuxM_pos (s := s) (by linarith)
  have hlag := iwaniecAuxM_pos (s := s - 1) (by linarith)
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hnn : 0 ≤ iwaniecAuxM s * s * Real.log s / iwaniecAuxM (s - 1) :=
    div_nonneg (mul_nonneg (mul_nonneg hM.le (by linarith)) hlog) hlag.le
  simp only [Real.norm_eq_abs, abs_of_nonneg hnn, abs_one, mul_one]
  rw [div_le_iff₀ hlag]
  exact (iwaniecAuxM_s_log_lt_four_lag hs).le

end

end Erdos1212Kernel
