import Erdos1212Kernel.TaoDyadicSelectedDecay

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoFrequencyOrder_log_bound (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hT : (N : Real) ≤ T) :
    ((taoFrequencyOrder N T hN - 1 : Nat) : Real) * Real.log N ≤ Real.log T := by
  have hNp : 0 < (N : Real) := by positivity
  have hTp : 0 < T := hNp.trans_le hT
  have hlower := taoFrequencyOrder_lower N T hN hT
  have hlog := Real.log_le_log (pow_pos hNp _) hlower
  rw [Real.log_pow] at hlog
  exact hlog

theorem taoFrequencyOrder_le_log_ratio (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hT : (N : Real) ≤ T) :
    ((taoFrequencyOrder N T hN - 1 : Nat) : Real) ≤ Real.log T / Real.log N := by
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos (by exact_mod_cast hN)
  exact (le_div_iff₀ hlogN).2 (taoFrequencyOrder_log_bound N T hN hT)

theorem taoFrequencyOrder_two_power_bound (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hT : (N : Real) ≤ T) :
    (2 : Real) ^ (taoFrequencyOrder N T hN + 1) ≤
      4 * T ^ (Real.log 2 / Real.log N) := by
  let k := taoFrequencyOrder N T hN
  have hk : 2 ≤ k := taoFrequencyOrder_two_le N T hN
  have hNp : 0 < (N : Real) := by positivity
  have hTp : 0 < T := hNp.trans_le hT
  have horder := taoFrequencyOrder_le_log_ratio N T hN hT
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) horder
  rw [Real.rpow_natCast] at hpow
  have heq : (2 : Real) ^ (Real.log T / Real.log N) =
      T ^ (Real.log 2 / Real.log N) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hTp]
    congr 1
    ring
  rw [heq] at hpow
  have hdecomp := taoVdc_two_pow_decompose (k := k + 1) (by omega)
  have hmul := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : Real) ≤ 4)
  rw [show k + 1 - 2 = k - 1 by omega] at hdecomp
  exact hdecomp.le.trans (by simpa only [mul_assoc] using hmul)

theorem taoFrequencyOrder_beta_lower (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hT : (N : Real) ≤ T) :
    1 / (4 * T ^ (Real.log 2 / Real.log N)) ≤
      taoVdcBeta (taoFrequencyOrder N T hN + 1) := by
  let k := taoFrequencyOrder N T hN
  have hk : 2 ≤ k := taoFrequencyOrder_two_le N T hN
  have hpow := taoFrequencyOrder_two_power_bound N T hN hT
  have hden : 0 < (2 : Real) ^ (k + 1) - 2 := by
    have hh : (2 : Real) ^ 3 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at hh
    linarith
  have hdenle : (2 : Real) ^ (k + 1) - 2 ≤
      4 * T ^ (Real.log 2 / Real.log N) := (sub_le_self _ (by norm_num)).trans hpow
  unfold taoVdcBeta
  exact one_div_le_one_div_of_le hden hdenle

theorem taoSelectedDecay_explicit (t : Real) (N : Nat) (hN : 2 ≤ N)
    (ht : t ≠ 0) (hNT : (N : Real) ≤ taoLogFrequency t) :
    taoSelectedDecay t N hN ≤
      (1 / (N : Real)) ^
        (1 / (4 * (taoLogFrequency t) ^ (Real.log 2 / Real.log N))) := by
  have hbase0 : 0 < 1 / (N : Real) := by positivity
  have hbase1 : 1 / (N : Real) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : Real) < (N : Real))).2
    exact_mod_cast (show 1 ≤ N by omega)
  have hbeta := taoFrequencyOrder_beta_lower N (taoLogFrequency t) hN hNT
  unfold taoSelectedDecay
  exact Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 hbeta

theorem taoDyadicComplexPower_explicit_decay (t σ : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hNT : (N : Real) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (1 / (N : Real)) ^
          (1 / (4 * (taoLogFrequency t) ^ (Real.log 2 / Real.log N)))) := by
  have hbase := taoDyadicComplexPower_selected_decay t σ N M hN hMN ht hσ hNT
  have hdecay := taoSelectedDecay_explicit t N hN ht hNT
  have hcoef : 0 ≤ (N : Real) ^ (1 - σ) *
      ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) := by
    have hlog := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  apply hbase.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdecay hcoef

end

end Erdos1212Kernel
