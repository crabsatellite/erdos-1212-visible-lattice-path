import Erdos1212Kernel.IwaniecDickmanPositivity
import Erdos1212Kernel.IwaniecAuxiliaryDickmanWindows
import Erdos1212Kernel.IwaniecAuxiliaryProfiles
import Mathlib.Analysis.Asymptotics.Defs

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-- The source's lower comparison with rho, now for the actual
constructed functions rather than an assumed comparison principle. -/
theorem iwaniecDickman_lt_auxM {s : Real} (hs : 2 ≤ s) :
    iwaniecDickman s < iwaniecAuxM s := by
  have hinit : ∀ x ∈ Set.Icc (2 : Real) 3, iwaniecDickman x < iwaniecAuxM x := by
    intro x hx
    have hr := iwaniecDickman_le_one (s := x) (by linarith [hx.1])
    have hm := iwaniecAuxM_initial_ge_three_halves hx
    linarith
  by_contra hnot
  have hsBad : iwaniecAuxM s ≤ iwaniecDickman s := le_of_not_gt hnot
  have hsHigh : 3 < s := by
    by_contra hnotHigh
    have h := hinit s ⟨hs, le_of_not_gt hnotHigh⟩
    linarith
  let gap := fun x : Real => iwaniecAuxM x - iwaniecDickman x
  let bad : Set Real := Set.Icc 3 s ∩ gap ⁻¹' Set.Iic 0
  have hc : ContinuousOn gap (Set.Icc (3 : Real) s) := by
    apply (iwaniecAuxM_continuousOn.sub iwaniecDickman_continuous.continuousOn).mono
    intro x hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hclosed : IsClosed bad := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast (show bad.Nonempty from
    ⟨s, ⟨⟨hsHigh.le, le_rfl⟩, sub_nonpos.mpr hsBad⟩⟩)
  have haThree : 3 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haBad : iwaniecAuxM a ≤ iwaniecDickman a := sub_nonpos.mp ha.1.2
  have hbefore : ∀ x : Real, 2 ≤ x → x < a → iwaniecDickman x ≤ iwaniecAuxM x := by
    intro x hx hxa
    by_cases hxThree : x ≤ 3
    · exact (hinit x ⟨hx, hxThree⟩).le
    · by_contra hnotx
      have hxBad : x ∈ bad := ⟨⟨(lt_of_not_ge hxThree).le, hxa.le.trans haUpper⟩,
        sub_nonpos.mpr (lt_of_not_ge hnotx).le⟩
      have hax := ha.2 hxBad
      linarith
  have hintM : IntervalIntegrable iwaniecAuxM volume (a - 1) a :=
    iwaniecIntervalIntegrable_of_continuousOn_one _ (iwaniecAuxFunction_continuousOn (-1)) (by linarith) (by linarith)
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (show a - 1 ≤ a by linarith)
    (iwaniecDickman_continuous.intervalIntegrable (a - 1) a) hintM
    (fun x hx => hbefore x (by linarith [hx.1]) hx.2)
  have hm := iwaniecAuxM_gt_dickman_average haThree
  rw [one_div_mul_eq_div, div_lt_iff₀ (show 0 < a by linarith)] at hm
  have hr := iwaniecDickman_window_identity (s := a) (by linarith)
  have hcMul := mul_le_mul_of_nonneg_left haBad (show 0 ≤ a by linarith)
  nlinarith

/-- The upper comparison uses the source's exact `s+2` shift. -/
theorem iwaniecAuxM_add_two_lt_three_dickman {s : Real} (hs : 1 ≤ s) :
    iwaniecAuxM (s + 2) < 3 * iwaniecDickman s := by
  let f := fun x : Real => iwaniecAuxM (x + 2)
  have hcF : ContinuousOn f (Set.Ici (0 : Real)) := by
    apply iwaniecAuxM_continuousOn.comp (continuousOn_id.add continuousOn_const)
    intro x hx
    change (2 : Real) ≤ x + 2
    linarith [hx.out]
  have hinit : ∀ x ∈ Set.Icc (0 : Real) 1, f x ≤ 3 * iwaniecDickman x := by
    intro x hx
    rw [iwaniecDickman_initial hx.2, mul_one]
    exact iwaniecAuxM_le_three (by linarith [hx.1])
  by_contra hnot
  have hsBad : 3 * iwaniecDickman s ≤ f s := le_of_not_gt hnot
  let gap := fun x => f x - 3 * iwaniecDickman x
  let bad : Set Real := Set.Icc 1 s ∩ gap ⁻¹' Set.Ici 0
  have hc : ContinuousOn gap (Set.Icc (1 : Real) s) := by
    apply (hcF.sub (continuousOn_const.mul iwaniecDickman_continuous.continuousOn)).mono
    intro x hx
    change (0 : Real) ≤ x
    linarith [hx.1]
  have hclosed : IsClosed bad := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast (show bad.Nonempty from
    ⟨s, ⟨⟨hs, le_rfl⟩, sub_nonneg.mpr hsBad⟩⟩)
  have haOne : 1 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haBad : 3 * iwaniecDickman a ≤ f a := sub_nonneg.mp ha.1.2
  have hbefore : ∀ x : Real, 0 ≤ x → x < a → f x ≤ 3 * iwaniecDickman x := by
    intro x hx hxa
    by_cases hxOne : x ≤ 1
    · exact hinit x ⟨hx, hxOne⟩
    · by_contra hnotx
      have hxBad : x ∈ bad := ⟨⟨(lt_of_not_ge hxOne).le, hxa.le.trans haUpper⟩,
        sub_nonneg.mpr (lt_of_not_ge hnotx).le⟩
      have hax := ha.2 hxBad
      linarith
  have hintF : IntervalIntegrable f volume (a - 1) a := by
    apply ContinuousOn.intervalIntegrable
    apply hcF.mono
    intro x hx
    rw [Set.uIcc_of_le (show a - 1 ≤ a by linarith)] at hx
    change (0 : Real) ≤ x
    linarith [hx.1]
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (show a - 1 ≤ a by linarith) hintF
    ((continuous_const.mul iwaniecDickman_continuous).intervalIntegrable (a - 1) a)
    (fun x hx => hbefore x (by linarith [hx.1]) hx.2)
  change (∫ x in (a - 1)..a, f x) ≤ ∫ x in (a - 1)..a, 3 * iwaniecDickman x at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hm : f a < (1 / a) * (∫ x in (a - 1)..a, f x) := iwaniecAuxM_add_two_lt_dickman_average haOne
  rw [one_div_mul_eq_div, lt_div_iff₀ (show 0 < a by linarith)] at hm
  have hr := iwaniecDickman_window_identity haOne
  have hcMul := mul_le_mul_of_nonneg_left haBad (show 0 ≤ a by linarith)
  nlinarith

theorem iwaniecDickman_isBigO_auxM : iwaniecDickman =O[atTop] iwaniecAuxM := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (2 : Real)] with s hs
  have hr := iwaniecDickman_pos (s := s) (by linarith)
  have hm := iwaniecAuxM_pos hs
  simp only [Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hm, one_mul]
  exact (iwaniecDickman_lt_auxM hs).le

/-- Both actual G bounds are now attached to the same constructed rho,
with the source shift retained in the upper bound. -/
theorem iwaniecAuxG_dickman_sandwich (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    iwaniecDickman s / 3 < iwaniecAuxG rank s ∧
      iwaniecAuxG rank s < 2 * iwaniecDickman (s - 2) := by
  have hG := iwaniecAuxG_bounds rank (s := s) (by linarith)
  have hlow := iwaniecDickman_lt_auxM (s := s) (by linarith)
  have hhigh := iwaniecAuxM_add_two_lt_three_dickman (s := s - 2) (by linarith)
  rw [sub_add_cancel] at hhigh
  constructor <;> linarith [hG.1, hG.2]

end

end Erdos1212Kernel
