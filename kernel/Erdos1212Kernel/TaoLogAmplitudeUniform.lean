import Erdos1212Kernel.TaoLogDerivativeConsumer

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1700000

theorem taoLog_nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      omega

theorem taoLogDerivativeAmplitude_pow_bound (k : Nat) :
    taoLogDerivativeAmplitude k ≤ (2 : Real) ^ ((k + 1) + (k + 1) ^ 2) := by
  have hfacNat := Nat.factorial_le_pow (k + 1)
  have hnNat := taoLog_nat_le_two_pow (k + 1)
  have hfac : (((k + 1).factorial : Nat) : Real) ≤ (((k + 1 : Nat) : Real) ^ (k + 1)) := by
    exact_mod_cast hfacNat
  have hn : ((k + 1 : Nat) : Real) ≤ (2 : Real) ^ (k + 1) := by exact_mod_cast hnNat
  have hpow : (((k + 1 : Nat) : Real) ^ (k + 1)) ≤ ((2 : Real) ^ (k + 1)) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) hn (k + 1)
  unfold taoLogDerivativeAmplitude
  calc
    _ ≤ (2 : Real) ^ (k + 1) * (((k + 1 : Nat) : Real) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ ≤ (2 : Real) ^ (k + 1) * (((2 : Real) ^ (k + 1)) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      congr 1 <;> ring

theorem taoLog_amplitude_exponent_budget {k : Nat} (hk : 3 ≤ k) :
    (k + 1) + (k + 1) ^ 2 ≤ 32 * 2 ^ (k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hindex : n + 1 - 3 = (n - 3) + 1 := by omega
      have hpoly : (n + 2) + (n + 2) ^ 2 ≤ 2 * ((n + 1) + (n + 1) ^ 2) := by
        nlinarith
      calc
        _ ≤ 2 * ((n + 1) + (n + 1) ^ 2) := hpoly
        _ ≤ 2 * (32 * 2 ^ (n - 3)) := Nat.mul_le_mul_left 2 ih
        _ = _ := by rw [hindex, pow_succ] <;> ring

theorem taoLogDerivativeAmplitude_source_uniform {k : Nat} (hk : 3 ≤ k) :
    taoLogDerivativeAmplitude k ^ (1 / (2 : Real) ^ (k - 3)) ≤ (2 : Real) ^ 32 := by
  have hA := taoLogDerivativeAmplitude_pow_bound k
  have hAr : 0 ≤ taoLogDerivativeAmplitude k :=
    zero_le_one.trans (taoLogDerivativeAmplitude_one_le k)
  have hr : 0 ≤ (1 : Real) / (2 : Real) ^ (k - 3) := by positivity
  have hmono := Real.rpow_le_rpow hAr hA hr
  have hbudget : (((k + 1) + (k + 1) ^ 2 : Nat) : Real) /
      (2 : Real) ^ (k - 3) ≤ 32 := by
    have hh : (((k + 1) + (k + 1) ^ 2 : Nat) : Real) ≤
        (32 * 2 ^ (k - 3) : Nat) := by exact_mod_cast taoLog_amplitude_exponent_budget hk
    norm_num at hh ⊢
    exact (div_le_iff₀ (by positivity : (0 : Real) < 2 ^ (k - 3))).2 (by simpa only [mul_comm] using hh)
  calc
    _ ≤ ((2 : Real) ^ ((k + 1) + (k + 1) ^ 2)) ^
        (1 / (2 : Real) ^ (k - 3)) := hmono
    _ = (2 : Real) ^ ((((k + 1) + (k + 1) ^ 2 : Nat) : Real) /
        (2 : Real) ^ (k - 3)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
      congr 1
      ring
    _ ≤ (2 : Real) ^ (32 : Real) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget
    _ = _ := Real.rpow_natCast 2 32

theorem taoLogDerivativeAmplitude_two_uniform :
    taoLogDerivativeAmplitude 2 ^ (2 * taoVdcAlpha 2) ≤ (2 : Real) ^ 32 := by
  norm_num [taoLogDerivativeAmplitude, taoVdcAlpha]

theorem taoLogDerivativeAmplitude_uniform {k : Nat} (hk : 2 ≤ k) :
    taoLogDerivativeAmplitude k ^ (2 * taoVdcAlpha k) ≤ (2 : Real) ^ 32 := by
  by_cases hk2 : k = 2
  · simpa only [hk2] using taoLogDerivativeAmplitude_two_uniform
  · have hk3 : 3 ≤ k := by omega
    rw [taoVdc_source_amplitude_exponent hk3]
    exact taoLogDerivativeAmplitude_source_uniform hk3

end

end Erdos1212Kernel
