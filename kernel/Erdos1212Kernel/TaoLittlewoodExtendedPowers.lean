import Erdos1212Kernel.TaoLittlewoodScalarBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoLittlewood_strip_sigma_lower {T : Real} {R : Nat} {σ : Real}
    (hwidth : taoLittlewoodWidth T R ≤ (1 : Real) / 8)
    (hstrip : 1 - taoLittlewoodWidth T R ≤ σ) :
    (7 : Real) / 8 ≤ σ := by linarith

theorem taoLittlewood_extended_cutoff_power {T σ : Real}
    (hT : 1 < T) (hσ1 : σ ≤ 1)
    (hdelta : 1 - σ ≤ (1 : Real) / 8) :
    (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) ^ (1 - σ) ≤
      T ^ (1 / 4 : Real) := by
  have hJtop := taoLittlewoodJ_top hT
  have hQnat : 2 ^ (2 * taoLittlewoodJ T) = (2 ^ taoLittlewoodJ T) ^ 2 := by
    rw [show 2 * taoLittlewoodJ T = taoLittlewoodJ T + taoLittlewoodJ T by omega,
      pow_add, pow_two]
  have hQ : (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) ≤ T ^ 2 := by
    rw [hQnat]
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hJtop 2
  have hdelta0 : 0 ≤ 1 - σ := by linarith
  have hfirst := Real.rpow_le_rpow (by positivity) hQ hdelta0
  have hsecond : (T ^ 2) ^ (1 - σ) ≤ (T ^ 2) ^ (1 / 8 : Real) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith : (1 : Real) ≤ T ^ 2) hdelta
  apply hfirst.trans
  apply hsecond.trans_eq
  rw [← Real.rpow_natCast T 2,
    ← Real.rpow_mul (zero_le_one.trans hT.le)]
  congr 1
  norm_num

theorem taoLittlewood_base_cutoff_power {T σ : Real}
    (hT : 1 < T) (hσ1 : σ ≤ 1)
    (hdelta : 1 - σ ≤ (1 : Real) / 8) :
    (((2 ^ taoLittlewoodJ T : Nat) : Real)) ^ (1 - σ) ≤
      T ^ (1 / 8 : Real) := by
  have hJtop := taoLittlewoodJ_top hT
  have hdelta0 : 0 ≤ 1 - σ := by linarith
  exact (Real.rpow_le_rpow (by positivity) hJtop hdelta0).trans
    (Real.rpow_le_rpow_of_exponent_le hT.le hdelta)

end

end Erdos1212Kernel
