import Erdos1212Kernel.TaoFrequencyOrder

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1800000

def taoVdcThreshold (k : Nat) : Real := (k : Real) - 2 + taoVdcAlpha k

theorem taoVdc_two_pow_decompose {k : Nat} (hk : 2 ≤ k) :
    (2 : Real) ^ k = 4 * (2 : Real) ^ (k - 2) := by
  rw [show k = (k - 2) + 2 by omega, pow_add]
  norm_num
  ring

theorem taoVdc_two_pow_pred {k : Nat} (hk : 2 ≤ k) :
    (2 : Real) ^ (k - 1) = 2 * (2 : Real) ^ (k - 2) := by
  rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  ring

theorem taoVdc_high_exponent_identity {k : Nat} (hk : 2 ≤ k) :
    (taoVdcAlpha k - 2) * (2 * taoVdcBeta k) = -taoVdcAlpha k := by
  have hp := taoVdc_two_pow_decompose hk
  have ha : 0 < (2 : Real) ^ (k - 2) := by positivity
  have ha1 : 1 ≤ (2 : Real) ^ (k - 2) := one_le_pow₀ (by norm_num)
  have hd : 0 < (2 : Real) ^ k - 2 := by
    rw [hp]
    nlinarith
  unfold taoVdcAlpha taoVdcBeta
  field_simp
  nlinarith

theorem taoVdc_low_exponent_identity {k : Nat} (hk : 3 ≤ k) :
    (taoVdcAlpha k - 2) * (taoVdcBeta k - taoVdcBeta (k - 1)) =
      taoVdcBeta (k - 1) := by
  have hp := taoVdc_two_pow_decompose (by omega : 2 ≤ k)
  have hpred := taoVdc_two_pow_pred (by omega : 2 ≤ k)
  have ha : 0 < (2 : Real) ^ (k - 2) := by positivity
  have ha1 : 1 ≤ (2 : Real) ^ (k - 2) := one_le_pow₀ (by norm_num)
  have hd : 0 < (2 : Real) ^ k - 2 := by rw [hp]; nlinarith
  have hdp : 0 < (2 : Real) ^ (k - 1) - 2 := by
    rw [hpred]
    have ha2 : 2 ≤ (2 : Real) ^ (k - 2) := by
      have : 1 ≤ k - 2 := by omega
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) this : (2 : Real) ^ 1 ≤ 2 ^ (k - 2))
    nlinarith
  unfold taoVdcAlpha taoVdcBeta
  field_simp
  nlinarith

theorem taoVdc_beta_strict_decrease {k : Nat} (hk : 3 ≤ k) :
    taoVdcBeta k < taoVdcBeta (k - 1) := by
  have hprev : 2 ≤ k - 1 := by omega
  have hb := taoVdcBeta_pos hprev
  have hden : 0 < 2 * (1 + taoVdcBeta (k - 1)) := by positivity
  have hdiv : taoVdcBeta (k - 1) / (2 * (1 + taoVdcBeta (k - 1))) <
      taoVdcBeta (k - 1) := by
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_pos_of_pos hb]
  have hrec := taoVdcBeta_succ hprev
  have hkEq : (k - 1) + 1 = k := by omega
  rw [hkEq] at hrec
  calc
    _ = taoVdcBeta (k - 1) / (2 * (1 + taoVdcBeta (k - 1))) := hrec
    _ < _ := hdiv

end

end Erdos1212Kernel
