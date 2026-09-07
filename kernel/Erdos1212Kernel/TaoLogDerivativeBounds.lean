import Erdos1212Kernel.TaoLogDerivativeFamily
import Mathlib.Data.Nat.Factorial.BigOperators

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1700000

def taoLogFrequency (t : Real) : Real := |t| / (2 * Real.pi)

def taoLogDerivativeAmplitude (k : Nat) : Real :=
  (2 : Real) ^ (k + 1) * ((k + 1).factorial : Real)

theorem taoLogFrequency_nonneg (t : Real) : 0 ≤ taoLogFrequency t := by
  unfold taoLogFrequency
  positivity

theorem taoLogFrequency_pos {t : Real} (ht : t ≠ 0) : 0 < taoLogFrequency t := by
  unfold taoLogFrequency
  positivity

theorem taoLogDerivativeFamily_succ_abs (t : Real) (n : Nat) {x : Real} (hx : 0 < x) :
    |taoLogDerivativeFamily t (n + 1) x| =
      (n.factorial : Real) * taoLogFrequency t / x ^ (n + 1) := by
  rw [taoLogDerivativeFamily_succ, abs_mul, taoLogDerivativeCoeff_abs, abs_zpow,
    abs_of_pos hx, zpow_neg, zpow_natCast]
  unfold taoLogFrequency
  ring

theorem taoLogDerivativeAmplitude_one_le (k : Nat) : 1 ≤ taoLogDerivativeAmplitude k := by
  unfold taoLogDerivativeAmplitude
  have hpow : (1 : Real) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hfac : (1 : Real) ≤ ((k + 1).factorial : Real) := by exact_mod_cast Nat.factorial_pos (k + 1)
  nlinarith [mul_le_mul hpow hfac (by norm_num : (0 : Real) ≤ 1) (by positivity : 0 ≤ (2 : Real) ^ (k + 1))]

theorem taoLogDerivativeAmplitude_two_pow {k j : Nat} (hj : j ≤ k + 1) :
    (2 : Real) ^ j ≤ taoLogDerivativeAmplitude k := by
  have hpow : (2 : Real) ^ j ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) hj
  have hfac : (1 : Real) ≤ ((k + 1).factorial : Real) := by exact_mod_cast Nat.factorial_pos (k + 1)
  unfold taoLogDerivativeAmplitude
  nlinarith [mul_le_mul_of_nonneg_left hfac (show 0 ≤ (2 : Real) ^ (k + 1) by positivity)]

theorem taoLogDerivativeAmplitude_factorial {k j : Nat} (hj : 1 ≤ j) (hjk : j ≤ k + 1) :
    ((j - 1).factorial : Real) ≤ taoLogDerivativeAmplitude k := by
  have hindex : j - 1 ≤ k + 1 := (Nat.sub_le j 1).trans hjk
  have hfacNat := Nat.factorial_le hindex
  have hfac : ((j - 1).factorial : Real) ≤ ((k + 1).factorial : Real) := by exact_mod_cast hfacNat
  have hpow : (1 : Real) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hfac0 : 0 ≤ ((j - 1).factorial : Real) := by positivity
  unfold taoLogDerivativeAmplitude
  exact hfac.trans (by nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ ((k + 1).factorial : Real) by positivity)])

theorem taoLogDerivativeFamily_abs (t : Real) {j : Nat} (hj : 1 ≤ j) {x : Real} (hx : 0 < x) :
    |taoLogDerivativeFamily t j x| =
      ((j - 1).factorial : Real) * taoLogFrequency t / x ^ j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa only [Nat.add_comm, Nat.add_sub_cancel_left] using taoLogDerivativeFamily_succ_abs t n hx

theorem taoLogDerivativeFamily_dyadic_bounds (t : Real) (k j : Nat) {N x : Real}
    (hN : 0 < N) (hj : j ∈ Finset.Icc 1 (k + 1)) (hx : x ∈ Set.Icc N (2 * N)) :
    taoLogFrequency t / (taoLogDerivativeAmplitude k * N ^ j) ≤
        |taoLogDerivativeFamily t j x| ∧
      |taoLogDerivativeFamily t j x| ≤
        taoLogDerivativeAmplitude k * taoLogFrequency t / N ^ j := by
  have hj' := Finset.mem_Icc.mp hj
  have hxpos : 0 < x := hN.trans_le hx.1
  have hfreq := taoLogFrequency_nonneg t
  have hA := taoLogDerivativeAmplitude_one_le k
  have hApos : 0 < taoLogDerivativeAmplitude k := lt_of_lt_of_le zero_lt_one hA
  have hfac0 : 0 ≤ ((j - 1).factorial : Real) := by positivity
  have hfac1 : 1 ≤ ((j - 1).factorial : Real) := by exact_mod_cast Nat.factorial_pos (j - 1)
  have hfacA := taoLogDerivativeAmplitude_factorial hj'.1 hj'.2
  have hNpow : N ^ j ≤ x ^ j := pow_le_pow_left₀ hN.le hx.1 j
  have hxpow : x ^ j ≤ (2 * N) ^ j := pow_le_pow_left₀ hxpos.le hx.2 j
  have htwoA := taoLogDerivativeAmplitude_two_pow hj'.2
  have htwoN : (2 * N) ^ j ≤ taoLogDerivativeAmplitude k * N ^ j := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right htwoA (pow_nonneg hN.le j)
  rw [taoLogDerivativeFamily_abs t hj'.1 hxpos]
  constructor
  · have hden : x ^ j ≤ taoLogDerivativeAmplitude k * N ^ j := hxpow.trans htwoN
    have hinv : 1 / (taoLogDerivativeAmplitude k * N ^ j) ≤ 1 / x ^ j :=
      one_div_le_one_div_of_le (pow_pos hxpos j) hden
    have hfirst := mul_le_mul_of_nonneg_left hinv hfreq
    have hsecond := mul_le_mul_of_nonneg_right hfac1 (show 0 ≤ taoLogFrequency t / x ^ j by positivity)
    calc
      _ = taoLogFrequency t * (1 / (taoLogDerivativeAmplitude k * N ^ j)) := by ring
      _ ≤ taoLogFrequency t * (1 / x ^ j) := hfirst
      _ = taoLogFrequency t / x ^ j := by ring
      _ ≤ (j - 1).factorial * (taoLogFrequency t / x ^ j) := by nlinarith
      _ = (j - 1).factorial * taoLogFrequency t / x ^ j := by ring
  · have hinv : 1 / x ^ j ≤ 1 / N ^ j := one_div_le_one_div_of_le (pow_pos hN j) hNpow
    have hcoef := mul_le_mul_of_nonneg_right hfacA hfreq
    calc
      _ = (((j - 1).factorial : Real) * taoLogFrequency t) * (1 / x ^ j) := by ring
      _ ≤ (taoLogDerivativeAmplitude k * taoLogFrequency t) * (1 / N ^ j) :=
        mul_le_mul hcoef hinv (by positivity)
          (mul_nonneg (zero_le_one.trans (taoLogDerivativeAmplitude_one_le k)) hfreq)
      _ = _ := by ring

end

end Erdos1212Kernel
