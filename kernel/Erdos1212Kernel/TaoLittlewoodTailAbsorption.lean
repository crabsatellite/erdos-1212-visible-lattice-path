import Erdos1212Kernel.TaoLittlewoodExtendedPowers

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoLittlewood_quarter_square {T : Real} (hT : 0 < T) :
    T ^ (1 / 4 : Real) * T ^ (1 / 4 : Real) = Real.sqrt T := by
  rw [← Real.rpow_add hT, Real.sqrt_eq_rpow]
  congr 1
  norm_num

theorem taoLittlewood_sqrt_mul_eighth {T : Real} (hT : 0 < T) :
    Real.sqrt T * T ^ (1 / 8 : Real) = T ^ (5 / 8 : Real) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]
  congr 1
  norm_num

theorem taoLittlewood_high_tail_first_le_two {T σ : Real}
    (hT : 2 ≤ T) (hσ1 : σ ≤ 1) (hdelta : 1 - σ ≤ (1 : Real) / 8)
    (hlogQuarter : Real.log T ≤ T ^ (1 / 4 : Real)) :
    (((2 ^ (2 * taoLittlewoodJ T) : Nat) : Real)) ^ (1 - σ) *
        Real.log (2 + T) / Real.sqrt T ≤ 2 := by
  have hQ := taoLittlewood_extended_cutoff_power (by linarith : 1 < T) hσ1 hdelta
  have hlog := taoLittlewood_log_two_add_le_two_log hT
  have hlog2q : Real.log (2 + T) ≤ 2 * T ^ (1 / 4 : Real) :=
    hlog.trans (mul_le_mul_of_nonneg_left hlogQuarter (by norm_num))
  have hnum := mul_le_mul hQ hlog2q (Real.log_nonneg (by linarith : 1 ≤ 2 + T))
    (Real.rpow_nonneg (by positivity : 0 ≤ T) _)
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  apply (div_le_iff₀ hsqrt).2
  calc
    _ ≤ T ^ (1 / 4 : Real) * (2 * T ^ (1 / 4 : Real)) := hnum
    _ = 2 * (T ^ (1 / 4 : Real) * T ^ (1 / 4 : Real)) := by ring
    _ = 2 * Real.sqrt T := by rw [taoLittlewood_quarter_square (by linarith)]

theorem taoLittlewood_high_tail_second_le_two {T σ : Real}
    (hT : 2 ≤ T) (hσ1 : σ ≤ 1) (hdelta : 1 - σ ≤ (1 : Real) / 8) :
    Real.sqrt T * (((2 ^ taoLittlewoodJ T : Nat) : Real)) ^ (-σ) ≤ 2 := by
  let N : Real := ((2 ^ taoLittlewoodJ T : Nat) : Real)
  have hNpos : 0 < N := by unfold N; positivity
  have hNdelta := taoLittlewood_base_cutoff_power (T := T) (σ := σ)
    (by linarith : 1 < T) hσ1 hdelta
  have hNlower : T / 2 < N := by simpa only [N] using taoLittlewoodJ_bottom (by linarith : 1 < T)
  have hrewrite : N ^ (-σ) = N ^ (1 - σ) / N := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hNpos]
    congr 1 <;> ring
  rw [hrewrite]
  have hnum : Real.sqrt T * N ^ (1 - σ) ≤ Real.sqrt T * T ^ (1 / 8 : Real) :=
    mul_le_mul_of_nonneg_left hNdelta (Real.sqrt_nonneg _)
  have hpow : T ^ (5 / 8 : Real) ≤ T := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : Real) ≤ T)
        (by norm_num : (5 / 8 : Real) ≤ 1))
  have hnumT : Real.sqrt T * N ^ (1 - σ) ≤ T := by
    exact hnum.trans (by rw [taoLittlewood_sqrt_mul_eighth (by linarith)]; exact hpow)
  rw [show Real.sqrt T * (N ^ (1 - σ) / N) =
    (Real.sqrt T * N ^ (1 - σ)) / N by ring]
  apply (div_le_iff₀ hNpos).2
  nlinarith

end

end Erdos1212Kernel
