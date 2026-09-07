import Erdos1212Kernel.IwaniecStoppedCubicCap
import Erdos1212Kernel.IwaniecPaperARecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecPaperOddCutoff_eq_min {level s : Real} (hy : 1 < level) (hs : 0 < s) :
    Real.exp (Real.log level / max 3 s) =
      min (Real.exp (Real.log level / s)) (Real.exp (Real.log level / 3)) := by
  by_cases hs3 : s ≤ 3
  · have horder := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (Real.log_pos hy).le hs hs3)
    rw [max_eq_left hs3, min_eq_right horder]
  · have h3s : 3 ≤ s := (lt_of_not_ge hs3).le
    have horder := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num : (0 : Real) < 3) h3s)
    rw [max_eq_right h3s, min_eq_left horder]

theorem iwaniecStopped_logRatio_cutoff {level z : Real} (hy : 1 < level) (hz : 1 < z) :
    Real.exp (Real.log level / (Real.log level / Real.log z)) = z := by
  have hL : Real.log level ≠ 0 := (Real.log_pos hy).ne'
  have hZ : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  have hquot : Real.log level / (Real.log level / Real.log z) = Real.log z := by field_simp [hL, hZ]
  rw [hquot, Real.exp_log (zero_lt_one.trans hz)]

theorem iwaniecPaperD_even_logRatio {rank : Nat} (hr : Even rank) {level z : Real}
    (hy : 1 < level) (hz : 1 < z) :
    iwaniecPaperD rank level (Real.log level / Real.log z) = iwaniecPaperStoppedLayer 0 level z rank := by
  simp only [iwaniecPaperD, if_pos hr]
  rw [iwaniecStopped_logRatio_cutoff hy hz]

theorem iwaniecPaperD_odd_logRatio {rank : Nat} (hr : ¬Even rank) {level z : Real}
    (hy : 1 < level) (hz : 1 < z) :
    iwaniecPaperD rank level (Real.log level / Real.log z) =
      iwaniecPaperStoppedLayer 1 level (min z (Real.exp (Real.log level / 3))) rank := by
  simp only [iwaniecPaperD, if_neg hr]
  rw [iwaniecPaperOddCutoff_eq_min hy (div_pos (Real.log_pos hy) (Real.log_pos hz)),
    iwaniecStopped_logRatio_cutoff hy hz]

theorem iwaniecPaperQ_even_logRatio {rank : Nat} (hr : Even rank) {level z : Real}
    (hy : 1 < level) (hz : 1 < z) :
    iwaniecPaperQ rank level (Real.log level / Real.log z) = iwaniecPaperStoppedPartial 0 level z rank := by
  rw [iwaniecPaperQ_even_eq_partial hr, iwaniecStopped_logRatio_cutoff hy hz]

theorem iwaniecPaperQ_odd_logRatio {rank : Nat} (hr : ¬Even rank) {level z : Real}
    (hy : 1 < level) (hz : 1 < z) :
    iwaniecPaperQ rank level (Real.log level / Real.log z) =
      iwaniecPaperStoppedPartial 1 level (min z (Real.exp (Real.log level / 3))) rank := by
  rw [iwaniecPaperQ_odd_eq_partial hr,
    iwaniecPaperOddCutoff_eq_min hy (div_pos (Real.log_pos hy) (Real.log_pos hz)),
    iwaniecStopped_logRatio_cutoff hy hz]

/-- The actual first-prime pool supplies both the child level domain
and the strict parent-to-child parameter inequality. -/
theorem iwaniecStoppedChild_domain {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) {p : Nat}
    (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    1 < level / p ∧ s - 1 < Real.log level / Real.log (p : Real) - 1 := by
  obtain ⟨hpPrime, hpLt⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hp1 : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
  have hs0 : 0 < s := by linarith
  have hchild : 1 < level / p := (one_lt_div hp0).mpr (hpLt.trans_le (iwaniecPaperCutoff_le_level hy hs))
  have hlog := Real.log_lt_log hp0 hpLt
  rw [Real.log_exp] at hlog
  have hprod := (lt_div_iff₀ hs0).mp hlog
  have ht : s < Real.log level / Real.log (p : Real) :=
    (lt_div_iff₀ (Real.log_pos hp1)).mpr (by nlinarith only [hprod])
  exact ⟨hchild, by linarith only [ht]⟩

end

end Erdos1212Kernel
