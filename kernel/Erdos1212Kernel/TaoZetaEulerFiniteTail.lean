import Erdos1212Kernel.TaoZetaEulerKernel
import Mathlib.Analysis.SumIntegralComparisons

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoZetaEuler_power_sum_bound {σ a : Real} (hσ : 0 < σ) (ha : 1 ≤ a) (M : Nat) :
    (∑ m ∈ Finset.range M, (a + m) ^ (-σ - 1)) ≤
      a ^ (-σ) * (1 + 1 / σ) := by
  have hapos : 0 < a := by linarith
  cases M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ M =>
      rw [Finset.sum_range_succ']
      rw [add_comm]
      simp only [Nat.cast_zero, add_zero]
      have hanti : AntitoneOn (fun x : Real => x ^ (-σ - 1)) (Set.Icc a (a + M)) := by
        intro x hx y hy hxy
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
      have htail := hanti.sum_le_integral
      have hzero : (0 : Real) ∉ Set.uIcc a (a + M) := by
        have hM0 : (0 : Real) ≤ M := by positivity
        rw [Set.uIcc_of_le (by linarith : a ≤ a + M)]
        intro h
        linarith [h.1]
      have hint : (∫ x in a..a + M, x ^ (-σ - 1)) =
          ((a + M) ^ (-σ) - a ^ (-σ)) / (-σ) := by
        have h := integral_rpow (a := a) (b := a + M) (r := -σ - 1)
          (Or.inr ⟨(by linarith : -σ - 1 ≠ -1), hzero⟩)
        have hexp : -σ - 1 + 1 = -σ := by ring
        rw [hexp] at h
        exact h
      rw [hint] at htail
      have hnonneg : 0 ≤ (a + M) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have htail' : (∑ i ∈ Finset.range M, (a + (i + 1 : Nat)) ^ (-σ - 1)) ≤
          a ^ (-σ) / σ := by
        apply htail.trans
        have heq : ((a + M) ^ (-σ) - a ^ (-σ)) / (-σ) =
            (a ^ (-σ) - (a + M) ^ (-σ)) / σ := by
          field_simp
          ring
        rw [heq]
        apply (div_le_div_iff_of_pos_right hσ).2
        nlinarith
      have haexp : a ^ (-σ - 1) ≤ a ^ (-σ) :=
        Real.rpow_le_rpow_of_exponent_le ha (by linarith)
      calc
        _ ≤ a ^ (-σ) + a ^ (-σ) / σ := add_le_add haexp htail'
        _ = a ^ (-σ) * (1 + 1 / σ) := by ring

theorem taoZetaEuler_finite_error_identity {s : Complex} {a : Real} (ha : 1 ≤ a) (M : Nat) :
    (∑ m ∈ Finset.range M,
        (taoZetaEulerKernel s (a + m) - ∫ x in a + m..a + m + 1, taoZetaEulerKernel s x)) =
      (∑ m ∈ Finset.range M, taoZetaEulerKernel s (a + m)) -
        ∫ x in a..a + M, taoZetaEulerKernel s x := by
  have hint (m : Nat) (hm : m < M) :
      IntervalIntegrable (taoZetaEulerKernel s) volume (a + m) (a + (m + 1 : Nat)) := by
    have hzero : (0 : Real) ∉ Set.uIcc (a + m) (a + (m + 1 : Nat)) := by
      rw [Set.uIcc_of_le (by push_cast; linarith)]
      intro h
      linarith [ha, h.1]
    exact intervalIntegral.intervalIntegrable_cpow (r := -s) (Or.inr hzero)
  rw [Finset.sum_sub_distrib]
  congr 1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero, add_assoc] using hsum

theorem taoZetaEuler_finite_tail_error {s : Complex} {a : Real}
    (hs : 0 < s.re) (ha : 1 ≤ a) (M : Nat) :
    ‖(∑ m ∈ Finset.range M, taoZetaEulerKernel s (a + m)) -
        ∫ x in a..a + M, taoZetaEulerKernel s x‖ ≤
      ‖s‖ * a ^ (-s.re) * (1 + 1 / s.re) := by
  rw [← taoZetaEuler_finite_error_identity ha]
  calc
    _ ≤ ∑ m ∈ Finset.range M,
        ‖taoZetaEulerKernel s (a + m) - ∫ x in a + m..a + m + 1,
          taoZetaEulerKernel s x‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range M, ‖s‖ * (a + m) ^ (-s.re - 1) := by
      apply Finset.sum_le_sum
      intro m _hm
      exact taoZetaEulerKernel_unit_integral_error hs (by
        have hm0 : (0 : Real) ≤ m := by positivity
        linarith)
    _ = ‖s‖ * ∑ m ∈ Finset.range M, (a + m) ^ (-s.re - 1) := by rw [Finset.mul_sum]
    _ ≤ ‖s‖ * (a ^ (-s.re) * (1 + 1 / s.re)) :=
      mul_le_mul_of_nonneg_left (taoZetaEuler_power_sum_bound hs ha M) (norm_nonneg _)
    _ = _ := by ring

end

end Erdos1212Kernel
