import Erdos1212Kernel.TaoVdcOrderBounds
import Erdos1212Kernel.TaoVdcRate

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

theorem taoVdc_log_factor_lower (k : Nat) {T : Real} (hT : 0 ≤ T) :
    (1 : Real) / 2 ≤ (Real.log (2 + T)) ^ (taoVdcAlpha k) := by
  have hlow := taoSecondDerivative_log_lower hT
  calc
    _ = ((1 : Real) / 2) ^ (1 : Real) := by rw [Real.rpow_one]
    _ ≤ ((1 : Real) / 2) ^ (taoVdcAlpha k) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (taoVdcAlpha_le_one k)
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) hlow (taoVdcAlpha_pos k).le

theorem taoVdc_amplitude_ge_one (k : Nat) {A : Real} (hA : 1 ≤ A) :
    1 ≤ A ^ (2 * taoVdcAlpha k) := by
  have ha := taoVdcAlpha_pos k
  exact Real.one_le_rpow hA (by positivity)

/-- The small-T regime is separate: the source's displayed H need not
be at most N here. The original target is already bounded below. -/
theorem taoVdcRate_small_lower {k : Nat} (hk : 3 ≤ k) {N T : Real}
    (hN : 1 ≤ N) (hT : 0 < T) (hsmall : T ≤ 1) : 1 / 2 ≤ taoVdcRate k N T := by
  have hNp : 0 < N := by linarith
  have hbeta := taoVdcBeta_pos (by omega : 2 ≤ k)
  have hQ : N ^ k ≤ N ^ k / T := (le_div_iff₀ hT).2 (by nlinarith [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ N ^ k by positivity)])
  have hpower : N ^ (taoVdcAlpha k) ≤ (N ^ k / T) ^ (taoVdcBeta k) := by
    calc
      _ ≤ N ^ ((k : Real) * taoVdcBeta k) := Real.rpow_le_rpow_of_exponent_le hN (taoVdc_order_beta_ge_alpha hk)
      _ = (N ^ k) ^ (taoVdcBeta k) := by rw [Real.rpow_mul hNp.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hQ hbeta.le
  have hratio : 1 ≤ (1 / N ^ (taoVdcAlpha k)) * (N ^ k / T) ^ (taoVdcBeta k) := by
    have hh : 1 ≤ (N ^ k / T) ^ (taoVdcBeta k) / N ^ (taoVdcAlpha k) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).2 (by simpa using hpower)
    calc
      _ ≤ (N ^ k / T) ^ (taoVdcBeta k) / N ^ (taoVdcAlpha k) := hh
      _ = _ := by ring
  have hlog := taoVdc_log_factor_lower k hT.le
  have hmul := mul_le_mul hratio hlog (by norm_num : (0 : Real) ≤ 1 / 2) (by positivity)
  have hlast : 0 ≤ (T / N ^ k) ^ (taoVdcBeta k) := by positivity
  unfold taoVdcRate
  nlinarith

theorem taoVdcRate_large_lower {k : Nat} (hk : 2 ≤ k) {N T : Real}
    (hN : 0 < N) (hT : 0 < T) (hlarge : N ^ k ≤ T) : 1 ≤ taoVdcRate k N T := by
  have hratio : 1 ≤ T / N ^ k := (le_div_iff₀ (by positivity : 0 < N ^ k)).2 (by simpa using hlarge)
  have hlast := Real.one_le_rpow hratio (taoVdcBeta_pos hk).le
  have hL : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hfirst : 0 ≤ (1 / N ^ (taoVdcAlpha k)) * (N ^ k / T) ^ (taoVdcBeta k) * (Real.log (2 + T)) ^ (taoVdcAlpha k) := by positivity
  unfold taoVdcRate
  linarith

end

end Erdos1212Kernel
