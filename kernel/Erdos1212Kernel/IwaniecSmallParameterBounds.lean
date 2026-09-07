import Erdos1212Kernel.IwaniecFiniteMainBound
import Erdos1212Kernel.IwaniecAuxTauUniform

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniecWeightPower_small_parameter_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ s : Real, 1 ≤ s → s ≤ 3 →
      iwaniecAuxWeightPower level s ≤ 2 := by
  let K : Real := 10 * 3 ^ 3 * Real.log 3 ^ 5
  filter_upwards [eventually_iwaniecWeightPower_fixed_linear_bound (t := 3) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 K)] with level hfixed hlog
  have hL1 : 1 ≤ Real.log level := (le_max_left _ _).trans hlog
  have hKL : K ≤ Real.log level := (le_max_right _ _).trans hlog
  have hsmall : K / Real.log level ^ 2 ≤ 1 := by
    apply (div_le_one₀ (sq_pos_of_pos (Real.log_pos hfixed.1))).mpr
    nlinarith only [hL1, hKL]
  have hthree : iwaniecAuxWeightPower level 3 ≤ 2 := by
    have hh := hfixed.2
    change iwaniecAuxWeightPower level 3 ≤ 1 + K / Real.log level ^ 2 at hh
    linarith only [hh, hsmall]
  refine ⟨hfixed.1, ?_⟩
  intro s hs hs3
  exact (iwaniecAuxWeightPower_monotoneOn level hs (by norm_num : (3 : Real) ∈ Set.Ici 1) hs3).trans hthree

theorem eventually_iwaniecEulerError_small_parameter {D : Real} (hD : 0 ≤ D) :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ s : Real, 2 ≤ s → s ≤ 3 →
      D * Real.exp (-Real.sqrt (Real.log level / s)) ≤ 1 / Real.log level ^ 2 := by
  filter_upwards [eventually_iwaniec_source_four_three hD,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with level hsource hlog
  have hL := Real.log_pos hsource.1
  refine ⟨hsource.1, ?_⟩
  intro s hs hs3
  have hE : Real.exp (-Real.sqrt (Real.log level / s)) ≤ Real.exp (-Real.sqrt (Real.log level / 6)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hL.le (by linarith) (by linarith : s ≤ 6)))
  have hnormal : (2 : Real) / Real.log level ^ 4 ≤ 1 / Real.log level ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hL 4) (sq_pos_of_pos hL)).mpr
    have hsq : 2 ≤ Real.log level ^ 2 := by nlinarith only [hlog]
    have hh := mul_nonneg (sq_nonneg (Real.log level)) (sub_nonneg.mpr hsq)
    nlinarith only [hh]
  exact (mul_le_mul_of_nonneg_left hE hD).trans
    ((hsource.2 2).le.trans
      ((div_le_div_of_nonneg_right (iwaniecAuxG_le_two 2 (s := 4) (by norm_num)) (pow_nonneg hL.le 4)).trans hnormal))

end

end Erdos1212Kernel
