import Erdos1212Kernel.TaoFiniteDyadicMixed

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1800000

theorem taoExplicitDecayExponent_mono_scale {T N₁ N₂ : Real}
    (hT : 1 ≤ T) (hN₁ : 1 < N₁) (hN : N₁ ≤ N₂) :
    taoExplicitDecayExponent T N₁ ≤ taoExplicitDecayExponent T N₂ := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog1 : 0 < Real.log N₁ := Real.log_pos hN₁
  have hlogN := Real.log_le_log (by linarith : 0 < N₁) hN
  have hratio : Real.log 2 / Real.log N₂ ≤ Real.log 2 / Real.log N₁ :=
    div_le_div_of_nonneg_left hlog2 hlog1 hlogN
  have hpow := Real.rpow_le_rpow_of_exponent_le hT hratio
  have hden : 0 < 4 * T ^ (Real.log 2 / Real.log N₂) := by positivity
  unfold taoExplicitDecayExponent
  exact one_div_le_one_div_of_le hden (mul_le_mul_of_nonneg_left hpow (by norm_num))

theorem taoFiniteDyadic_zeta_endpoint_conditions (t σ : Real) (R J : Nat)
    (ht : t ≠ 0) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hT1 : 1 ≤ taoLogFrequency t)
    (hTop : (((2 ^ J : Nat) : Real)) ≤ taoLogFrequency t)
    (hWidthR : 1 - σ ≤
      taoExplicitDecayExponent (taoLogFrequency t) (((2 ^ R : Nat) : Real))) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), taoZetaTerm σ t n‖ ≤
      (J : Real) * ((((2 ^ R : Nat) : Real)) ^ (1 - σ) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) := by
  apply taoFiniteDyadic_zeta_mixed_scales t σ R J ht hσ0 hσ1 hR hRJ
  · intro r _hRr hrJ
    have hpowNat : 2 ^ r ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow : (((2 ^ r : Nat) : Real)) ≤ ((2 ^ J : Nat) : Real) := by exact_mod_cast hpowNat
    exact hpow.trans hTop
  · intro r hRr _hrJ
    have hpowNat : 2 ^ R ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hRr
    have hpow : (((2 ^ R : Nat) : Real)) ≤ ((2 ^ r : Nat) : Real) := by exact_mod_cast hpowNat
    have hbase : (1 : Real) < ((2 ^ R : Nat) : Real) := by
      have : 2 ≤ 2 ^ R := (pow_le_pow_right₀ (by norm_num) hR : 2 ^ 1 ≤ 2 ^ R)
      exact_mod_cast this
    exact hWidthR.trans (taoExplicitDecayExponent_mono_scale hT1 hbase hpow)

end

end Erdos1212Kernel
