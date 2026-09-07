import Erdos1212Kernel.IwaniecAuxiliaryComparisonKernel
import Erdos1212Kernel.IwaniecAuxiliaryProfiles
import Erdos1212Kernel.IwaniecSieveSeriesMonotonicity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-- The first-contact argument of source Lemma 7, applied to the actual
ordinary and auxiliary M functions, with their two distinct kernels. -/
theorem iwaniecMExtended_lt_four_aux {s : Real} (hs : 2 ≤ s) :
    iwaniecMExtended s < 4 * iwaniecAuxM s := by
  by_contra hnot
  have hsBad : 4 * iwaniecAuxM s ≤ iwaniecMExtended s := le_of_not_gt hnot
  have hsHigh : 3 < s := by
    by_contra hnotHigh
    have hi := iwaniecMExtended_lt_four_aux_initial ⟨hs, le_of_not_gt hnotHigh⟩
    linarith
  let gap := fun t : Real => iwaniecMExtended t - 4 * iwaniecAuxM t
  let bad : Set Real := Set.Icc 3 s ∩ gap ⁻¹' Set.Ici 0
  have hgapCont : ContinuousOn gap (Set.Ici (2 : Real)) :=
    iwaniecMExtended_continuousOn.sub (continuousOn_const.mul iwaniecAuxM_continuousOn)
  have hcont : ContinuousOn gap (Set.Icc (3 : Real) s) := by
    apply hgapCont.mono
    intro x hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hclosed : IsClosed bad :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  have hnonempty : bad.Nonempty := ⟨s, ⟨⟨hsHigh.le, le_rfl⟩, sub_nonneg.mpr hsBad⟩⟩
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast hnonempty
  have haThree : 3 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haContact : 4 * iwaniecAuxM a ≤ iwaniecMExtended a := sub_nonneg.mp ha.1.2
  have hbefore : ∀ x : Real, 2 ≤ x → x < a → iwaniecMExtended x < 4 * iwaniecAuxM x := by
    intro x hxTwo hxa
    by_cases hxThree : x ≤ 3
    · exact iwaniecMExtended_lt_four_aux_initial ⟨hxTwo, hxThree⟩
    · by_contra hxNot
      have hxBad : x ∈ bad :=
        ⟨⟨(lt_of_not_ge hxThree).le, hxa.le.trans haUpper⟩, sub_nonneg.mpr (le_of_not_gt hxNot)⟩
      have hax := ha.2 hxBad
      linarith
  have hOldInt := iwaniecMExtended_intervalIntegrable
    (a := a - 1) (b := a) (by linarith) (by linarith)
  have hNewInt : IntervalIntegrable (fun x => 4 * iwaniecAuxM x) volume (a - 1) a := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.mul iwaniecAuxM_continuousOn).mono
    intro x hx
    rw [Set.uIcc_of_le (show a - 1 ≤ a by linarith)] at hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hIntegral := intervalIntegral.integral_mono_on_of_le_Ioo
    (show a - 1 ≤ a by linarith) hOldInt hNewInt
    (fun x hx => (hbefore x (by linarith [hx.1]) hx.2).le)
  rw [intervalIntegral.integral_const_mul] at hIntegral
  rw [← iwaniecMExtended_window_identity haThree] at hIntegral
  have hstrict := mul_lt_mul_of_pos_left (iwaniecAuxM_unweighted_window_lt haThree)
    (show (0 : Real) < 4 by norm_num)
  have hcontact := mul_le_mul_of_nonneg_left haContact (show 0 ≤ a - 1 by linarith)
  nlinarith

theorem iwaniecMExtended_le_four_aux {s : Real} (hs : 2 ≤ s) :
    iwaniecMExtended s ≤ 4 * iwaniecAuxM s := (iwaniecMExtended_lt_four_aux hs).le

theorem iwaniecParitySieveProfile_le_MExtended (rank : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecParitySieveProfile rank s ≤ iwaniecMExtended s := by
  have hf := iwaniecEvenSieveSeries_nonneg hs
  have hF := iwaniecOddSieveSeries_nonneg (show 1 ≤ s by linarith)
  by_cases hsHigh : 3 ≤ s
  · rw [iwaniecMExtended_of_three_le hsHigh]
    unfold iwaniecParitySieveProfile
    split <;> linarith
  · have hsLow : s ≤ 3 := (lt_of_not_ge hsHigh).le
    rw [iwaniecMExtended_of_le_three hsLow]
    have hC : 3 ≤ iwaniecSieveNormalizationC := by
      unfold iwaniecSieveNormalizationC
      have hnonneg := iwaniecOddSieveSeries_nonneg (s := 3) (by norm_num)
      linarith
    unfold iwaniecParitySieveProfile
    split
    · linarith
    · rw [iwaniecOddSieveSeries_eq_three (by linarith) hsLow]
      unfold iwaniecSieveNormalizationC
      linarith

/-- The source Lemma 7 majorant for every parity profile. -/
theorem iwaniecParitySieveProfile_lt_four_aux (rank : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecParitySieveProfile rank s < 4 * iwaniecAuxM s :=
  (iwaniecParitySieveProfile_le_MExtended rank hs).trans_lt (iwaniecMExtended_lt_four_aux hs)

theorem iwaniecParitySieveProfile_lt_twelve_auxG
    (rank auxRank : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecParitySieveProfile rank s < 12 * iwaniecAuxG auxRank s := by
  have hprofile := iwaniecParitySieveProfile_lt_four_aux rank hs
  have hG := (iwaniecAuxG_bounds auxRank hs).1
  linarith

end

end Erdos1212Kernel
