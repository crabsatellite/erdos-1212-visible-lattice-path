import Erdos1212Kernel.TaoVdcRate
import Erdos1212Kernel.TaoVdcPowerSums

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

theorem taoVdc_average_power_envelope (H : Nat) (hH : 0 < H) {p X Y : Real}
    (hp : 0 ≤ p) (hphalf : p ≤ 1 / 2) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (1 / (H : Real)) * (∑ h ∈ Finset.Icc 1 H, (X * (h : Real) ^ (-p) + Y * (h : Real) ^ p)) ≤
      2 * X * (H : Real) ^ (-p) + Y * (H : Real) ^ p := by
  have hn := mul_le_mul_of_nonneg_left (taoVdc_average_negative_rpow H hH hp hphalf) hX
  have hp' := mul_le_mul_of_nonneg_left (taoVdc_average_positive_rpow H hH hp) hY
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ = X * ((1 / (H : Real)) * ∑ h ∈ Finset.Icc 1 H, (h : Real) ^ (-p)) +
        Y * ((1 / (H : Real)) * ∑ h ∈ Finset.Icc 1 H, (h : Real) ^ p) := by ring
    _ ≤ X * (2 * (H : Real) ^ (-p)) + Y * (H : Real) ^ p := add_le_add hn hp'
    _ = _ := by ring

theorem taoVdc_average_rates (k : Nat) (hk : 2 ≤ k) (N H : Nat) {T : Real}
    (hT : 0 < T) (hH : 0 < H) (hHN : H ≤ N) :
    (1 / (H : Real)) * (∑ h ∈ Finset.Icc 1 H, taoVdcRate k N ((h : Real) * T / N)) ≤
      2 * ((1 / (N : Real) ^ (taoVdcAlpha k)) * ((N : Real) ^ (k + 1) / T) ^ (taoVdcBeta k) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k)) * (H : Real) ^ (-taoVdcBeta k) +
      (T / (N : Real) ^ (k + 1)) ^ (taoVdcBeta k) * (H : Real) ^ (taoVdcBeta k) := by
  have hN : 0 < N := hH.trans_le hHN
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hL : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  have hsum := Finset.sum_le_sum (fun h (hh : h ∈ Finset.Icc 1 H) => by
    have hhpos : 0 < (h : Real) := by exact_mod_cast (Finset.mem_Icc.mp hh).1
    have hhN : (h : Real) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hh).2.trans hHN
    exact taoVdcRate_difference_bound k hNp hT hhpos hhN)
  apply (mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / (H : Real) by positivity)).trans
  exact taoVdc_average_power_envelope H hH (taoVdcBeta_pos hk).le (taoVdcBeta_le_half hk) (by positivity) (by positivity)

end

end Erdos1212Kernel
