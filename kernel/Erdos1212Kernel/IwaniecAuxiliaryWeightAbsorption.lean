import Erdos1212Kernel.IwaniecAuxiliaryWeightCalculus
import Mathlib.Tactic.Positivity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

theorem iwaniecWeight_error_lt_one {C z v : Real} (hC : 0 < C) (hz : 0 < z) (hv : 1 ≤ v)
    (hscale : z * v ^ (22 / 5 : Real) ≤ 1) (hlarge : 120 * C < v ^ (2 / 5 : Real)) :
    100 * C * z * v ^ 4 < 1 := by
  have hvPos : 0 < v := by linarith
  have hp : v ^ 4 * v ^ (2 / 5 : Real) = v ^ (22 / 5 : Real) := by
    rw [← Real.rpow_natCast v 4, ← Real.rpow_add hvPos]
    norm_num
  have hprod : (100 * C * z * v ^ 4) * v ^ (2 / 5 : Real) ≤ 100 * C := by
    calc
      _ = 100 * C * (z * (v ^ 4 * v ^ (2 / 5 : Real))) := by ring
      _ = 100 * C * (z * v ^ (22 / 5 : Real)) := by rw [hp]
      _ ≤ _ := by nlinarith
  have hpowPos := Real.rpow_pos_of_pos hvPos (2 / 5 : Real)
  by_contra hnot
  have hge : 1 ≤ 100 * C * z * v ^ 4 := le_of_not_gt hnot
  nlinarith

/-- The exact `23/5`, `2/5`, and `600*C` scalar line in the source's
proof of (3.16). -/
theorem iwaniecWeight_source_expansion_lower
    {C z v : Real} (hC : 0 < C) (hz : 0 < z) (hv : 1 ≤ v)
    (hscale : z * v ^ (22 / 5 : Real) ≤ 1) :
    1 + (5 * v ^ (2 / 5 : Real) - 600 * C) * z * v ^ (23 / 5 : Real) ≤
      (1 + 5 * z * v ^ 5) * (1 - 100 * C * z * v ^ 4) := by
  have hvPos : 0 < v := by linarith
  have hpow5 : v ^ (2 / 5 : Real) * v ^ (23 / 5 : Real) = v ^ 5 := by
    rw [← Real.rpow_add hvPos]
    norm_num
  have hpow9 : v ^ (22 / 5 : Real) * v ^ (23 / 5 : Real) = v ^ 9 := by
    rw [← Real.rpow_add hvPos]
    norm_num
  have hpow4 : v ^ 4 ≤ v ^ (23 / 5 : Real) := by
    have h := Real.rpow_le_rpow_of_exponent_le hv (show (4 : Real) ≤ 23 / 5 by norm_num)
    norm_num at h
    exact h
  have hsmall : 100 * C * z * v ^ 4 ≤ 100 * C * z * v ^ (23 / 5 : Real) :=
    mul_le_mul_of_nonneg_left hpow4 (by positivity)
  have hcross : z ^ 2 * v ^ 9 ≤ z * v ^ (23 / 5 : Real) := by
    have h := mul_le_mul_of_nonneg_right hscale (show 0 ≤ z * v ^ (23 / 5 : Real) by positivity)
    have heq : (z * v ^ (22 / 5 : Real)) * (z * v ^ (23 / 5 : Real)) = z ^ 2 * v ^ 9 := by
      calc
        _ = z ^ 2 * (v ^ (22 / 5 : Real) * v ^ (23 / 5 : Real)) := by ring
        _ = _ := by rw [hpow9]
    rw [heq, one_mul] at h
    exact h
  have hcrossScaled := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 500 * C by positivity)
  calc
    _ = 1 + 5 * z * v ^ 5 - 100 * C * z * v ^ (23 / 5 : Real) -
        500 * C * z * v ^ (23 / 5 : Real) := by rw [← hpow5]; ring
    _ ≤ 1 + 5 * z * v ^ 5 - 100 * C * z * v ^ 4 - 500 * C * z ^ 2 * v ^ 9 := by
      nlinarith
    _ = _ := by ring

theorem iwaniecWeight_bernoulli_five {a : Real} (ha : 0 ≤ a) :
    1 + 5 * a ≤ (1 + a) ^ 5 := by
  have h : 0 ≤ a ^ 2 * (10 + 10 * a + 5 * a ^ 2 + a ^ 3) := by positivity
  nlinarith

theorem iwaniecWeight_absorbs_error {C z v : Real} (hC : 0 < C) (hz : 0 < z) (hv : 1 ≤ v)
    (hscale : z * v ^ (22 / 5 : Real) ≤ 1) (hlarge : 120 * C < v ^ (2 / 5 : Real)) :
    1 < (1 + z * v ^ 5) ^ 5 * (1 - 100 * C * z * v ^ 4) := by
  have herror := iwaniecWeight_error_lt_one hC hz hv hscale hlarge
  have hsource := iwaniecWeight_source_expansion_lower hC hz hv hscale
  have hbern := iwaniecWeight_bernoulli_five (show 0 ≤ z * v ^ 5 by positivity)
  have hpos : 0 < (5 * v ^ (2 / 5 : Real) - 600 * C) * z * v ^ (23 / 5 : Real) := by
    have hcoef : 0 < 5 * v ^ (2 / 5 : Real) - 600 * C := by linarith
    exact mul_pos (mul_pos hcoef hz) (Real.rpow_pos_of_pos (by linarith : 0 < v) _)
  have hmult := mul_le_mul_of_nonneg_right hbern (show 0 ≤ 1 - 100 * C * z * v ^ 4 by linarith)
  nlinarith

end

end Erdos1212Kernel
