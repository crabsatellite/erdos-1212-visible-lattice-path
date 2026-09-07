import Erdos1212Kernel.IwaniecPaperASharpSplit
import Erdos1212Kernel.IwaniecXiRounding

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem iwaniecReciprocalPower_antitone
    {B a b : Real} (hB : 0 < B) (ha : 0 < a) (hBa : B ≤ a) (hab : a ≤ b) :
    (B / b) ^ b ≤ (B / a) ^ a := by
  have hb : 0 < b := ha.trans_le hab
  have hbase : B / b ≤ B / a := div_le_div_of_nonneg_left hB.le ha hab
  calc
    (B / b) ^ b ≤ (B / a) ^ b :=
      Real.rpow_le_rpow (div_nonneg hB.le hb.le) hbase hb.le
    _ ≤ (B / a) ^ a := Real.rpow_le_rpow_of_exponent_ge
      (div_pos hB ha) ((div_le_one ha).2 hBa) hab

theorem iwaniecXiSplitThreshold_long_power_le
    {xi B : Real} (hxi : 1 < xi) (hlog : 1 < Real.log xi)
    (hB : 0 < B) (hBsplit : B ≤ iwaniecXiSplit xi) :
    (B / (iwaniecXiSplitThreshold xi : Real)) ^ iwaniecXiSplitThreshold xi ≤
      (B / iwaniecXiSplit xi) ^ iwaniecXiSplit xi := by
  have h := iwaniecReciprocalPower_antitone hB (iwaniecXiSplit_pos hxi hlog)
    hBsplit (iwaniecXiSplit_le_threshold xi)
  simpa only [Real.rpow_natCast] using h

theorem iwaniecXiSplitThreshold_short_exp_le
    {xi level : Real} (hxi : 1 < xi) (hlog : 1 < Real.log xi)
    (hslack : Real.log xi ^ 2 ≤ xi * Real.log 2) (hlevel : 1 < level) :
    Real.exp (((iwaniecXiSplitThreshold xi - 1 : Nat) : Real) *
        Real.log level / (xi - 1)) ≤
      level * Real.exp (-Real.log level / Real.log (2 * xi)) := by
  have hratio := iwaniecXiSplitThreshold_pred_ratio_bound hxi hlog hslack
  have hscaled := mul_le_mul_of_nonneg_right hratio (Real.log_pos hlevel).le
  have hexponent : ((iwaniecXiSplitThreshold xi - 1 : Nat) : Real) *
      Real.log level / (xi - 1) ≤
      (1 - 1 / Real.log (2 * xi)) * Real.log level := by
    convert hscaled using 1 <;> ring
  have hexp := Real.exp_le_exp.mpr hexponent
  have hrewrite : (1 - 1 / Real.log (2 * xi)) * Real.log level =
      Real.log level + (-Real.log level / Real.log (2 * xi)) := by ring
  rwa [hrewrite, Real.exp_add, Real.exp_log (zero_lt_one.trans hlevel)] at hexp

/-- The integer threshold has been fully eliminated from the estimate by
its exact ceiling transport; `xi_1` is the source's real split parameter. -/
theorem eventually_iwaniecPaperA_rounded_xi_bound :
    ∀ᶠ level : Real in atTop, ∀ rank : Nat, ∀ xi : Real,
      2 < xi → 1 < Real.log xi → Real.log xi ^ 2 ≤ xi * Real.log 2 →
      0 < Real.log (Real.log level) →
      6 * Real.log (Real.log level) ≤ iwaniecXiSplit xi →
      (iwaniecPaperA rank level (xi - 1) : Real) ≤
        3 * level * Real.exp (-Real.log level / Real.log (2 * xi)) +
          2 * level *
            (3 * Real.log (Real.log level) / iwaniecXiSplit xi) ^ iwaniecXiSplit xi := by
  filter_upwards [eventually_iwaniecPaperA_sharp_stirling_bound,
    eventually_gt_atTop (1 : Real)] with level hbound hlevel
  intro rank xi hxi hlog hslack hll hsplit
  have hxiOne : 1 < xi := by linarith
  have hK := iwaniecXiSplitThreshold_pos hxiOne hlog
  have hKthreshold : 6 * Real.log (Real.log level) ≤
      (iwaniecXiSplitThreshold xi + 1 : Nat) := by
    have hreal := hsplit.trans (iwaniecXiSplit_le_threshold xi)
    push_cast
    linarith
  have hraw := hbound rank (iwaniecXiSplitThreshold xi) (xi - 1) hK
    (by linarith) hKthreshold
  have hshort := iwaniecXiSplitThreshold_short_exp_le hxiOne hlog hslack hlevel
  have hlong := iwaniecXiSplitThreshold_long_power_le hxiOne hlog
    (show 0 < 3 * Real.log (Real.log level) by positivity)
    (show 3 * Real.log (Real.log level) ≤ iwaniecXiSplit xi by linarith)
  have hshortScaled := mul_le_mul_of_nonneg_left hshort (show (0 : Real) ≤ 3 by norm_num)
  have hlongScaled := mul_le_mul_of_nonneg_left hlong
    (show (0 : Real) ≤ 2 * level by positivity)
  apply hraw.trans
  convert add_le_add hshortScaled hlongScaled using 1 <;> ring

end

end Erdos1212Kernel
