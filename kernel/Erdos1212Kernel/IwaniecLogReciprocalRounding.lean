import Erdos1212Kernel.IwaniecEulerProductError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniec_half_le_log_two : (1 / 2 : Real) ≤ Real.log 2 := by
  have hh := Real.le_log_one_add_of_nonneg (show (0 : Real) ≤ 1 by norm_num)
  norm_num at hh
  linarith only [hh]

theorem iwaniec_log_reciprocal_nearby_bound {n x c : Real}
    (hx : 3 ≤ x) (hn : x - 1 ≤ n) (hnx : n ≤ x) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |c / Real.log n - c / Real.log x| ≤ 8 / x := by
  have hn2 : 2 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hln := Real.log_pos (show 1 < n by linarith)
  have hlx := Real.log_pos (show 1 < x by linarith)
  have hhalfN : (1 / 2 : Real) ≤ Real.log n :=
    iwaniec_half_le_log_two.trans (Real.log_le_log (by norm_num) hn2)
  have hlogs := Real.log_le_log hn0 hnx
  have hhalfX : (1 / 2 : Real) ≤ Real.log x := hhalfN.trans hlogs
  have hden := mul_le_mul hhalfN hhalfX (by norm_num : (0 : Real) ≤ 1 / 2) hln.le
  norm_num at hden
  have hdiff0 : 0 ≤ Real.log x - Real.log n := sub_nonneg.mpr hlogs
  have hdiff : Real.log x - Real.log n ≤ 1 / n := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
    rw [Real.log_div hx0.ne' hn0.ne'] at hh
    calc
      _ ≤ x / n - 1 := hh
      _ = (x - n) / n := by field_simp [hn0.ne']
      _ ≤ 1 / n := div_le_div_of_nonneg_right (by linarith only [hn]) hn0.le
  have hnum : c * (Real.log x - Real.log n) ≤ 1 / n := by
    have hh := mul_le_mul_of_nonneg_right hc1 hdiff0
    have hmul : c * (Real.log x - Real.log n) ≤ Real.log x - Real.log n := by simpa only [one_mul] using hh
    exact hmul.trans hdiff
  have heq : c / Real.log n - c / Real.log x =
      c * (Real.log x - Real.log n) / (Real.log n * Real.log x) := by
    field_simp [hln.ne', hlx.ne']
    <;> ring
  rw [heq, abs_of_nonneg (div_nonneg (mul_nonneg hc0 hdiff0) (mul_nonneg hln.le hlx.le))]
  calc
    _ ≤ (1 / n) / (Real.log n * Real.log x) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hln.le hlx.le)
    _ ≤ (1 / n) / (1 / 4) :=
      div_le_div_of_nonneg_left (by positivity : 0 ≤ 1 / n) (by norm_num : (0 : Real) < 1 / 4) hden
    _ = 4 / n := by ring
    _ ≤ 8 / x := by
      apply (div_le_div_iff₀ hn0 hx0).mpr
      linarith only [hn, hx]

end

end Erdos1212Kernel
