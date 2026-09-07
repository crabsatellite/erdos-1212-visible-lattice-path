import Erdos1212Kernel.IwaniecQErrorAbsorption
import Erdos1212Kernel.IwaniecPaperQFarRelative
import Erdos1212Kernel.IwaniecInductionRankSlack
import Erdos1212Kernel.IwaniecPaperAChildCountSum

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 650000

theorem iwaniecPaperQ_successor_antitone_high (rank : Nat) {level s T : Real}
    (hy : 1 < level) (hs : 4 ≤ s) (hsT : s ≤ T) :
    iwaniecPaperQ (rank + 1) level T ≤ iwaniecPaperQ (rank + 1) level s := by
  have hstart : iwaniecCorollaryThreeDomainStart rank ≤ s :=
    (iwaniecCorollaryThreeDomainStart_bounds rank).2.trans (by linarith)
  have hrec := iwaniecPaperQ_successor_band_recursion rank hy hstart hsT (hs.trans hsT)
  rw [iwaniecPaperD2_eq_zero_of_four_le hy hs, ite_self, add_zero] at hrec
  have hsum : 0 ≤ ∑ p ∈ iwaniecStrictPrimeBand
      (Real.exp (Real.log level / T)) (Real.exp (Real.log level / s)),
      iwaniecPaperQ rank (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
    apply Finset.sum_nonneg
    intro p _hp
    exact div_nonneg (iwaniecPaperQ_nonneg _ _ _) (Nat.cast_nonneg p)
  linarith only [hrec, hsum]

theorem iwaniecQ_middle_step_budget {B q C f W : Real}
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hC : 2 ≤ C) (hf : (1 / 2 : Real) ≤ f) (hW : 1 ≤ W) :
    5 * B * q + C * f * (B * W * (1 + q)) ≤ C * B * (f * (1 + 8 * q) * W) := by
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hCf : 1 ≤ C * f := by
    have hh := mul_le_mul hC hf (by norm_num : (0 : Real) ≤ 1 / 2) hC0
    nlinarith only [hh]
  have hCfW : 1 ≤ C * f * W := by
    have hh := mul_le_mul hCf hW (by norm_num : (0 : Real) ≤ 1) (mul_nonneg hC0 hf0)
    simpa only [one_mul] using hh
  have hpaid := mul_le_mul_of_nonneg_right hCfW (mul_nonneg hB hq)
  have hpositive : 0 ≤ C * f * B * W * q := by positivity
  nlinarith only [hpaid, hpositive]

theorem iwaniecQ_inv_four_le_weighted (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecAuxG rank s / Real.log level ^ 4 ≤
      (iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 2) *
        (Real.log level ^ 2)⁻¹ := by
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hs1 := hstart.trans hs
  have hW : 1 ≤ iwaniecAuxWeightPower level s :=
    Real.one_le_rpow (iwaniecAuxWeightBase_one_le level hs1) (by linarith)
  have hG := (iwaniecAuxG_pos_exactDomain rank hs).le
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hW hG)
    (pow_nonneg (Real.log_pos hy).le 4)
  simp only [one_mul] at hh
  convert hh using 1 <;> field_simp [(Real.log_pos hy).ne'] <;> ring

theorem iwaniec_exp_gamma_lt_three : Real.exp Real.eulerMascheroniConstant < 3 :=
  (Real.exp_lt_exp.mpr (show Real.eulerMascheroniConstant < 1 by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds])).trans Real.exp_one_lt_three

theorem eventually_iwaniecQ_far_normalized :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level (iwaniecPaperXi level - 1) <
        3 * (iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 2) *
          (Real.log level ^ 2)⁻¹ := by
  filter_upwards [eventually_iwaniecPaperQ_far_relative_bound] with level hlevel
  refine ⟨hlevel.1, ?_⟩
  intro rank s hs hsξ
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hW := (iwaniecAuxWeightPower_pos level (hstart.trans hs)).le
  have hG := (iwaniecAuxG_pos_exactDomain rank hs).le
  have hmass := mul_lt_mul_of_pos_left (hlevel.2 rank s hs hsξ) (Real.exp_pos Real.eulerMascheroniConstant)
  have hscale := mul_le_mul_of_nonneg_right iwaniec_exp_gamma_lt_three.le
    (show 0 ≤ iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4 by positivity)
  have hh := hmass.trans_le hscale
  convert hh using 1 <;> field_simp [(Real.log_pos hlevel.1).ne'] <;> ring

end

end Erdos1212Kernel
