import Erdos1212Kernel.IwaniecPaperARecursionParameter

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniecPaperChild_level_gt_one {level : Real} (hy : 1 < level) {p : Nat}
    (hp : p.Prime) (ht : 2 ≤ Real.log level / Real.log (p : Real)) :
    1 < level / (p : Real) := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlogp := Real.log_pos hp1
  have hprod := (le_div_iff₀ hlogp).mp ht
  have hlog : Real.log (p : Real) < Real.log level := by linarith only [hprod, hlogp]
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hp0, Real.exp_log (show 0 < level by linarith)] at hexp
  exact (one_lt_div hp0).mpr hexp

theorem iwaniecPaperChild_xi_of_parent_parameter {level : Real} (hy : 1 < level) {p : Nat}
    (hp : p.Prime) (ht : 2 ≤ Real.log level / Real.log (p : Real))
    (htxi : Real.log level / Real.log (p : Real) ≤ iwaniecPaperXi level) :
    Real.log (level / (p : Real)) / Real.log (p : Real) ≤ iwaniecPaperXi (level / (p : Real)) := by
  have hchild := iwaniecPaperChild_level_gt_one hy hp ht
  have hp1 : (1 : Real) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpLog : 0 < Real.log (p : Real) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hL : 0 < Real.log level := Real.log_pos hy
  have hLc : 0 < Real.log (level / (p : Real)) := Real.log_pos hchild
  have hulevel : 0 < Real.log (Real.log (3 * level)) :=
    (by norm_num : (0 : Real) < 1 / 16).trans (iwaniecShiftedLogLog_gt_sixteenth hy)
  have huchild : 0 < Real.log (Real.log (3 * (level / (p : Real)))) :=
    (by norm_num : (0 : Real) < 1 / 16).trans (iwaniecShiftedLogLog_gt_sixteenth hchild)
  have hchildLe : level / (p : Real) ≤ level := div_le_self (by linarith) hp1
  have hlog3 := Real.log_le_log (show 0 < 3 * (level / (p : Real)) by linarith)
    (show 3 * (level / (p : Real)) ≤ 3 * level by linarith)
  have hloglog := Real.log_le_log (Real.log_pos (show 1 < 3 * (level / (p : Real)) by linarith)) hlog3
  have hden := Real.rpow_le_rpow huchild.le hloglog (by norm_num : (0 : Real) ≤ 11 / 5)
  have hraw := (div_le_div_iff₀ hpLog (Real.rpow_pos_of_pos hulevel (11 / 5 : Real))).mp htxi
  have hparent : Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) ≤ Real.log (p : Real) := by
    exact (mul_le_mul_iff_right₀ hL).mp hraw
  unfold iwaniecPaperXi
  exact div_le_div_of_nonneg_left hLc.le (Real.rpow_pos_of_pos huchild (11 / 5 : Real)) (hden.trans hparent)

theorem iwaniecPaperBand_child_domain (rank : Nat) {level s : Real}
    (hy : 1 < level) (hξ : iwaniecAuxSZero ≤ iwaniecPaperXi level)
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) {p : Nat}
    (hp : p ∈ iwaniecStrictPrimeBand
      (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s))) :
    1 < level / (p : Real) ∧
      iwaniecAuxGStart rank ≤ Real.log (level / (p : Real)) / Real.log (p : Real) ∧
      Real.log (level / (p : Real)) / Real.log (p : Real) ≤ iwaniecPaperXi (level / (p : Real)) := by
  obtain ⟨hpPool, hpLower⟩ := Finset.mem_filter.mp hp
  have hprime := (mem_iwaniecStrictPrimePool.mp hpPool).1
  have hpLog := Real.log_pos (show (1 : Real) < p by exact_mod_cast hprime.one_lt)
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have ht := iwaniecPaperBand_child_parameter_lower hy (show 0 < s by linarith) hp
  have ht2 : 2 ≤ Real.log level / Real.log (p : Real) := hs2.trans ht
  have hξsub : 0 < iwaniecPaperXi level - 1 := by linarith [iwaniecAuxSZero_large]
  have hlogLower := Real.log_le_log (Real.exp_pos (Real.log level / (iwaniecPaperXi level - 1))) hpLower
  rw [Real.log_exp] at hlogLower
  have hprod := (div_le_iff₀ hξsub).mp hlogLower
  have htξ : Real.log level / Real.log (p : Real) ≤ iwaniecPaperXi level := by
    have hh : Real.log level / Real.log (p : Real) ≤ iwaniecPaperXi level - 1 :=
      (div_le_iff₀ hpLog).mpr (by linarith only [hprod])
    linarith only [hh]
  refine ⟨iwaniecPaperChild_level_gt_one hy hprime ht2, ?_,
    iwaniecPaperChild_xi_of_parent_parameter hy hprime ht2 htξ⟩
  rw [iwaniecPaperChild_logParameter (show 0 < level by linarith) hprime]
  unfold iwaniecCorollaryThreeDomainStart at hs
  linarith only [hs, ht]

end

end Erdos1212Kernel
