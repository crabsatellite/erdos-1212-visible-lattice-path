import Erdos1212Kernel.IwaniecAuxiliaryWindowComparison
import Erdos1212Kernel.IwaniecBuchstabInvariant

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecMExtended_initial_explicit
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    iwaniecMExtended s = 2 * Real.exp Real.eulerMascheroniConstant *
      (1 - Real.log (s - 1)) := by
  rw [iwaniecMExtended_of_le_three hs.2, iwaniecSieveNormalizationC_value,
    iwaniecEvenSieveSeries_explicit hs.1 (hs.2.trans (by norm_num))]
  ring

theorem iwaniecMExtended_window_identity {s : Real} (hs : 3 ≤ s) :
    (s - 1) * iwaniecMExtended s = ∫ x in (s - 1)..s, iwaniecMExtended x := by
  have hz : iwaniecMConservation s = 0 := by
    rcases hs.eq_or_lt with rfl | hlt
    · exact iwaniecMConservation_three_eq_zero
    · exact iwaniecMConservation_eq_zero_of_three_lt hlt
  unfold iwaniecMConservation at hz
  rw [iwaniecMPrimitive_sub_shift_eq_window hs] at hz
  exact sub_eq_zero.mp hz

theorem iwaniecMExtended_lt_four_aux_initial
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    iwaniecMExtended s < 4 * iwaniecAuxM s := by
  have hden : 0 < s - 1 := by linarith [hs.1]
  have hinv : (1 / 2 : Real) ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hden]
    linarith [hs.2]
  have hlogLow := Real.log_nonneg (show 1 ≤ s - 1 by linarith [hs.1])
  have hlogHigh := Real.log_le_sub_one_of_pos hden
  have hMlower : (3 / 2 : Real) ≤ iwaniecAuxM s := by
    rw [iwaniecAuxM_initial hs.2]
    linarith [hs.2]
  have he : Real.exp Real.eulerMascheroniConstant < 3 :=
    (Real.exp_lt_exp.mpr (show Real.eulerMascheroniConstant < 1 by
      linarith [Real.eulerMascheroniConstant_lt_two_thirds])).trans Real.exp_one_lt_three
  have hMupper : iwaniecMExtended s ≤ 2 * Real.exp Real.eulerMascheroniConstant := by
    rw [iwaniecMExtended_initial_explicit hs]
    have hePos := Real.exp_pos Real.eulerMascheroniConstant
    nlinarith
  linarith


end

end Erdos1212Kernel
