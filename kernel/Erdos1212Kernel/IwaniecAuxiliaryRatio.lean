import Erdos1212Kernel.IwaniecAuxiliaryMProperties

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def iwaniecAuxAbsRatio (s : Real) : Real := |iwaniecAuxW s| / iwaniecAuxM s

theorem iwaniecAuxAbsRatio_continuousOn :
    ContinuousOn iwaniecAuxAbsRatio (Set.Ici (2 : Real)) := by
  apply iwaniecAuxW_continuousOn.abs.div iwaniecAuxM_continuousOn
  intro s hs
  exact (iwaniecAuxM_pos hs).ne'

theorem iwaniecAuxW_initial_range {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    -(1 / 2 : Real) ≤ iwaniecAuxW s ∧ iwaniecAuxW s ≤ 1 := by
  rw [iwaniecAuxW_initial hs.2]
  have hden : 0 < s - 1 := by linarith [hs.1]
  have hinvLow : (1 / 2 : Real) ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hden]
    linarith [hs.2]
  have hinvHigh : (1 : Real) / (s - 1) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith [hs.1]
  have hlogLow : 0 ≤ Real.log (s - 1) := Real.log_nonneg (by linarith [hs.1])
  have hlogHigh := Real.log_le_sub_one_of_pos hden
  constructor <;> linarith [hs.2]

theorem iwaniecAuxW_abs_le_initial {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    |iwaniecAuxW s| ≤ iwaniecAuxM s / 3 := by
  have hrange := iwaniecAuxW_initial_range hs
  have hrelation : iwaniecAuxM s = 2 + iwaniecAuxW s := by
    rw [iwaniecAuxM_initial hs.2, iwaniecAuxW_initial hs.2]
    ring
  rw [abs_le]
  constructor <;> linarith [hrange.1, hrange.2]

theorem iwaniecAuxAbsRatio_le_initial {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    iwaniecAuxAbsRatio s ≤ 1 / 3 := by
  unfold iwaniecAuxAbsRatio
  rw [div_le_iff₀ (iwaniecAuxM_pos hs.1)]
  have h := iwaniecAuxW_abs_le_initial hs
  linarith

/-- Kernel proof of Lemma 6 by the paper's first-contact argument. The
least point at which the ratio reaches the threshold has all earlier
ratios below it; the exact conserved windows then give a contradiction. -/
theorem iwaniecAuxAbsRatio_le_third {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxAbsRatio s ≤ 1 / 3 := by
  by_contra hnot
  have hbad : (1 / 3 : Real) < iwaniecAuxAbsRatio s := lt_of_not_ge hnot
  have hsHigh : 3 < s := by
    by_contra hnotHigh
    have hbound := iwaniecAuxAbsRatio_le_initial ⟨hs, le_of_not_gt hnotHigh⟩
    linarith
  let bad : Set Real := Set.Icc 3 s ∩ iwaniecAuxAbsRatio ⁻¹' Set.Ici (1 / 3)
  have hcont : ContinuousOn iwaniecAuxAbsRatio (Set.Icc (3 : Real) s) := by
    apply iwaniecAuxAbsRatio_continuousOn.mono
    intro x hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hclosed : IsClosed bad :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  have hnonempty : bad.Nonempty := ⟨s, ⟨⟨hsHigh.le, le_rfl⟩, hbad.le⟩⟩
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast hnonempty
  have haThree : 3 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have hcontact : (1 / 3 : Real) ≤ iwaniecAuxAbsRatio a := ha.1.2
  have hbefore : ∀ x : Real, 2 ≤ x → x < a → iwaniecAuxAbsRatio x ≤ 1 / 3 := by
    intro x hxTwo hxa
    by_cases hxThree : x ≤ 3
    · exact iwaniecAuxAbsRatio_le_initial ⟨hxTwo, hxThree⟩
    · by_contra hxNot
      have hxLarge : (1 / 3 : Real) < iwaniecAuxAbsRatio x := lt_of_not_ge hxNot
      have hxBad : x ∈ bad := ⟨⟨(lt_of_not_ge hxThree).le, hxa.le.trans haUpper⟩, hxLarge.le⟩
      have hax : a ≤ x := ha.2 hxBad
      linarith
  have haPos : 0 < a := by linarith
  have hratioPos : 0 < iwaniecAuxAbsRatio a := by linarith
  have hpoint : ∀ x ∈ Set.Icc (a - 1) a,
      |iwaniecAuxWWindowKernel x| ≤
        iwaniecAuxAbsRatio a * iwaniecAuxMReciprocalKernel x := by
    intro x hx
    have hxTwo : 2 ≤ x := by linarith [hx.1]
    have hratio : iwaniecAuxAbsRatio x ≤ iwaniecAuxAbsRatio a := by
      rcases lt_or_eq_of_le hx.2 with hlt | rfl
      · exact (hbefore x hxTwo hlt).trans hcontact
      · exact le_rfl
    unfold iwaniecAuxAbsRatio at hratio
    rw [div_le_iff₀ (iwaniecAuxM_pos hxTwo)] at hratio
    unfold iwaniecAuxWWindowKernel iwaniecAuxMReciprocalKernel
    rw [abs_div, abs_of_nonneg (sq_nonneg x)]
    have hscaled := div_le_div_of_nonneg_right hratio (sq_nonneg x)
    convert hscaled using 1 <;> unfold iwaniecAuxAbsRatio <;> ring
  have hAbsInt : IntervalIntegrable (fun x => |iwaniecAuxWWindowKernel x|)
      volume (a - 1) a :=
    iwaniecIntervalIntegrable_of_continuousOn_one _
      iwaniecAuxWWindowKernel_continuousOn.abs (by linarith) (by linarith)
  have hMajorCont : ContinuousOn
      (fun x => iwaniecAuxAbsRatio a * iwaniecAuxMReciprocalKernel x) (Set.Ioi (1 : Real)) :=
    continuousOn_const.mul iwaniecAuxMReciprocalKernel_continuousOn
  have hMajorInt := iwaniecIntervalIntegrable_of_continuousOn_one _ hMajorCont
    (a := a - 1) (b := a) (by linarith) (by linarith)
  have hIntegral := intervalIntegral.integral_mono_on (show a - 1 ≤ a by linarith)
    hAbsInt hMajorInt hpoint
  rw [intervalIntegral.integral_const_mul] at hIntegral
  have hAbsIntegral : |∫ x in (a - 1)..a, iwaniecAuxWWindowKernel x| ≤
      ∫ x in (a - 1)..a, |iwaniecAuxWWindowKernel x| :=
    intervalIntegral.abs_integral_le_integral_abs (show a - 1 ≤ a by linarith)
  have hwindow := iwaniecAuxW_window_identity haThree
  have hAbsWindow : |iwaniecAuxW a| =
      a * |∫ x in (a - 1)..a, iwaniecAuxWWindowKernel x| := by
    rw [hwindow, abs_mul, abs_neg, abs_of_pos haPos]
    rfl
  have hupper : |iwaniecAuxW a| ≤ iwaniecAuxAbsRatio a *
      (a * (∫ x in (a - 1)..a, iwaniecAuxMReciprocalKernel x)) := by
    rw [hAbsWindow]
    have h := mul_le_mul_of_nonneg_left (hAbsIntegral.trans hIntegral) haPos.le
    convert h using 1 <;> ring
  have hgap := iwaniecAuxM_reciprocal_window_lt haThree
  have hstrict := mul_lt_mul_of_pos_left hgap hratioPos
  have hcancel : iwaniecAuxAbsRatio a * iwaniecAuxM a = |iwaniecAuxW a| := by
    unfold iwaniecAuxAbsRatio
    exact div_mul_cancel₀ _ (iwaniecAuxM_pos (by linarith : 2 ≤ a)).ne'
  rw [hcancel] at hstrict
  change iwaniecAuxAbsRatio a *
    (a * (∫ x in (a - 1)..a, iwaniecAuxMReciprocalKernel x)) < |iwaniecAuxW a| at hstrict
  linarith

theorem iwaniecAuxW_abs_le_third_M {s : Real} (hs : 2 ≤ s) :
    |iwaniecAuxW s| ≤ iwaniecAuxM s / 3 := by
  have h := iwaniecAuxAbsRatio_le_third hs
  unfold iwaniecAuxAbsRatio at h
  rw [div_le_iff₀ (iwaniecAuxM_pos hs)] at h
  linarith

end

end Erdos1212Kernel
