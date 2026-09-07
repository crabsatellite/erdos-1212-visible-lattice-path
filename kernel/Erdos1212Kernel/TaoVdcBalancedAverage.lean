import Erdos1212Kernel.TaoVdcBalance
import Erdos1212Kernel.TaoVdcAveragedRates

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

/-- The averaged lower-order rate becomes the square of each exact
next-order term. This is the algebra preceding the single square root
in van der Corput, with the floor loss retained. -/
theorem taoVdc_balanced_average {k : Nat} (hk : 2 ≤ k) {N : Nat} {T : Real}
    (hN : 0 < N) (hT : 1 ≤ T) (hupper : T ≤ (N : Real) ^ (k + 1)) :
    (1 / (taoVdcShift (k + 1) N T : Real)) *
      (∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T), taoVdcRate k N ((h : Real) * T / N)) ≤
        4 * (taoVdcFirst (k + 1) N T) ^ 2 + (taoVdcSecond (k + 1) N T) ^ 2 := by
  have hn : 3 ≤ k + 1 := by omega
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  obtain ⟨hH, hHN, _hhalf, _hfull⟩ := taoVdcShift_admissible hn hN hT hupper
  have hbase := taoVdc_average_rates k hk N (taoVdcShift (k + 1) N T) hTp hH hHN
  have hneg := taoVdcShift_negative_power hn hN hT hupper (taoVdcBeta_pos hk).le
    ((taoVdcBeta_le_half hk).trans (by norm_num : (1 : Real) / 2 ≤ 1))
  have hpos := taoVdcShift_positive_power hn hN hT hupper (taoVdcBeta_pos hk).le
  have hfirst := mul_le_mul_of_nonneg_left hneg (show 0 ≤
    2 * ((1 / (N : Real) ^ (taoVdcAlpha k)) * ((N : Real) ^ (k + 1) / T) ^ (taoVdcBeta k) *
      (Real.log (2 + T)) ^ (taoVdcAlpha k)) by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hpos (show 0 ≤ (T / (N : Real) ^ (k + 1)) ^ (taoVdcBeta k) by positivity)
  apply hbase.trans
  calc
    _ ≤ (2 * ((1 / (N : Real) ^ (taoVdcAlpha k)) * ((N : Real) ^ (k + 1) / T) ^ (taoVdcBeta k) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k))) * (2 * (taoVdcRealShift (k + 1) N T) ^ (-taoVdcBeta k)) +
        (T / (N : Real) ^ (k + 1)) ^ (taoVdcBeta k) * (taoVdcRealShift (k + 1) N T) ^ (taoVdcBeta k) :=
      add_le_add hfirst hsecond
    _ = 4 * (((1 / (N : Real) ^ (taoVdcAlpha k)) * ((N : Real) ^ (k + 1) / T) ^ (taoVdcBeta k) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k)) * (taoVdcRealShift (k + 1) N T) ^ (-taoVdcBeta k)) +
        (T / (N : Real) ^ (k + 1)) ^ (taoVdcBeta k) * (taoVdcRealShift (k + 1) N T) ^ (taoVdcBeta k) := by ring
    _ = _ := by rw [taoVdc_first_balance hk hNp hTp, taoVdc_second_balance hk hNp hTp]

end

end Erdos1212Kernel
