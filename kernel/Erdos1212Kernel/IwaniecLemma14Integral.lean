import Erdos1212Kernel.IwaniecAntitonePrimeNatural
import Erdos1212Kernel.IwaniecLogReciprocalRounding

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 500000

theorem iwaniec_inv_log_antitoneOn :
    AntitoneOn (fun x : Real => (Real.log x)⁻¹) (Ioi 1) := by
  intro x hx y hy hxy
  exact (inv_le_inv₀ (Real.log_pos hy) (Real.log_pos hx)).mpr
    (Real.log_le_log (zero_lt_one.trans hx) hxy)

theorem iwaniec_inv_log_integral {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, (Real.log x)⁻¹ / (x * Real.log x)) =
      (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : Real => -(Real.log t)⁻¹)
        ((Real.log x)⁻¹ / (x * Real.log x)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx1 : 1 < x := ha.trans_le hx.1
    have hx0 : x ≠ 0 := (zero_lt_one.trans hx1).ne'
    have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    convert ((Real.hasDerivAt_log hx0).inv hl0).neg using 1 <;>
      field_simp <;> ring
  have hi : IntervalIntegrable (fun x : Real => (Real.log x)⁻¹ / (x * Real.log x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx1 : 1 < x := ha.trans_le hx.1
    have hx0 : x ≠ 0 := (zero_lt_one.trans hx1).ne'
    have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    exact (((Real.continuousAt_log hx0).inv₀ hl0).div
      (continuousAt_id.mul (Real.continuousAt_log hx0)) (mul_ne_zero hx0 hl0)).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi
  convert hh using 1 <;> ring

/-- A rounding estimate valid even when the smaller endpoint is 2. -/
theorem iwaniec_log_reciprocal_nearby_two {n x : Real}
    (hn2 : 2 ≤ n) (hn : x - 1 ≤ n) (hnx : n ≤ x) :
    |(Real.log n)⁻¹ - (Real.log x)⁻¹| ≤ 8 / x := by
  by_cases hx3 : 3 ≤ x
  · simpa only [one_div] using
      (iwaniec_log_reciprocal_nearby_bound (c := 1) hx3 hn hnx (by norm_num) le_rfl)
  · have hn0 : 0 < n := by linarith
    have hx0 : 0 < x := hn0.trans_le hnx
    have hln : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogs := Real.log_le_log hn0 hnx
    have hhalf : (1 / 2 : Real) ≤ Real.log n :=
      iwaniec_half_le_log_two.trans (Real.log_le_log (by norm_num) hn2)
    have hninv : (Real.log n)⁻¹ ≤ 2 := by
      have hh : (1 : Real) / Real.log n ≤ 2 := (div_le_iff₀ hln).mpr (by linarith)
      simpa only [one_div] using hh
    have hxinv : 0 ≤ (Real.log x)⁻¹ := inv_nonneg.mpr (hln.le.trans hlogs)
    have hinv : (Real.log x)⁻¹ ≤ (Real.log n)⁻¹ :=
      iwaniec_inv_log_antitoneOn (show 1 < n by linarith) (show 1 < x by linarith) hnx
    rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
    have h8 : 2 ≤ 8 / x := (le_div_iff₀ hx0).mpr (by linarith)
    linarith

end

end Erdos1212Kernel
