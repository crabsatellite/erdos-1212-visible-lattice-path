import Erdos1212Kernel.TaoFrequencyOrderQuantitative

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

def taoExplicitDecayExponent (T N : Real) : Real :=
  1 / (4 * T ^ (Real.log 2 / Real.log N))

theorem taoDyadic_scale_absorption {N σ T : Real} (hN : 1 ≤ N)
    (hwidth : 1 - σ ≤ taoExplicitDecayExponent T N) :
    N ^ (1 - σ) * (1 / N) ^ (taoExplicitDecayExponent T N) ≤ 1 := by
  have hNp : 0 < N := by linarith
  have hexp : 1 - σ - taoExplicitDecayExponent T N ≤ 0 := by linarith
  have hprod : N ^ (1 - σ) * (1 / N) ^ (taoExplicitDecayExponent T N) =
      N ^ (1 - σ - taoExplicitDecayExponent T N) := by
    rw [Real.div_rpow (by norm_num : (0 : Real) ≤ 1) hNp.le, Real.one_rpow,
      one_div, ← Real.rpow_neg hNp.le, ← Real.rpow_add hNp]
    congr 1 <;> ring
  rw [hprod]
  exact Real.rpow_le_one_of_one_le_of_nonpos hN hexp

theorem taoDyadicComplexPower_log_bound_of_width (t σ : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hNT : (N : Real) ≤ taoLogFrequency t)
    (hwidth : 1 - σ ≤ taoExplicitDecayExponent (taoLogFrequency t) N) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) := by
  have hbase := taoDyadicComplexPower_explicit_decay t σ N M hN hMN ht hσ hNT
  have hN1 : 1 ≤ (N : Real) := by exact_mod_cast (show 1 ≤ N by omega)
  have habsorb := taoDyadic_scale_absorption hN1 hwidth
  have hlog : 0 ≤ (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) := by
    have := Real.log_nonneg (by linarith [taoLogFrequency_pos ht] : 1 ≤ 2 + taoLogFrequency t)
    positivity
  apply hbase.trans
  unfold taoExplicitDecayExponent at habsorb
  calc
    _ = ((N : Real) ^ (1 - σ) *
        (1 / (N : Real)) ^ (1 / (4 * taoLogFrequency t ^ (Real.log 2 / Real.log N)))) *
          ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) := by ring
    _ ≤ 1 * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) :=
      mul_le_mul_of_nonneg_right habsorb hlog
    _ = _ := one_mul _

theorem taoDyadicComplexPower_trivial_bound (t σ : Real) (N M : Nat)
    (hN : 0 < N) (hMN : M ≤ N) (hσ : 0 ≤ σ) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤ M := by
  calc
    _ ≤ ∑ m ∈ Finset.range M,
        ‖(((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range M, (1 : Real) := by
      apply Finset.sum_le_sum
      intro m _hm
      have hn : 0 < (((N + m : Nat) : Real)) := by positivity
      change ‖((((N + m : Nat) : Real) : Complex) ^
        (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤ 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]
      have hre : (-((σ : Complex) + (t : Complex) * Complex.I)).re = -σ := by
        simp [Complex.mul_re]
      rw [hre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ N + m by omega)) (by linarith)
    _ = _ := by simp

theorem taoDyadicComplexPower_trivial_weighted_bound (t σ : Real) (N M : Nat)
    (hN : 0 < N) (hMN : M ≤ N) (hσ : 0 ≤ σ) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (M : Real) * (N : Real) ^ (-σ) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  calc
    _ ≤ ∑ m ∈ Finset.range M,
        ‖(((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range M, (N : Real) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro m _hm
      have hn : 0 < (((N + m : Nat) : Real)) := by positivity
      change ‖((((N + m : Nat) : Real) : Complex) ^
        (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤ (N : Real) ^ (-σ)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]
      have hre : (-((σ : Complex) + (t : Complex) * Complex.I)).re = -σ := by
        simp [Complex.mul_re]
      rw [hre]
      exact Real.rpow_le_rpow_of_nonpos hNR (by exact_mod_cast (show N ≤ N + m by omega)) (by linarith)
    _ = _ := by simp [nsmul_eq_mul]

theorem taoDyadicComplexPower_trivial_scale_bound (t σ : Real) (N M : Nat)
    (hN : 0 < N) (hMN : M ≤ N) (hσ : 0 ≤ σ) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) := by
  have hbase := taoDyadicComplexPower_trivial_weighted_bound t σ N M hN hMN hσ
  have hMR : (M : Real) ≤ N := by exact_mod_cast hMN
  have hdecay : 0 ≤ (N : Real) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  apply hbase.trans
  calc
    _ ≤ (N : Real) * (N : Real) ^ (-σ) := mul_le_mul_of_nonneg_right hMR hdecay
    _ = (N : Real) ^ (1 - σ) := by
      have hNR : 0 < (N : Real) := by exact_mod_cast hN
      calc
        _ = (N : Real) ^ (1 : Real) * (N : Real) ^ (-σ) := by rw [Real.rpow_one]
        _ = (N : Real) ^ (1 + -σ) := by rw [Real.rpow_add hNR]
        _ = _ := by congr 1 <;> ring

end

end Erdos1212Kernel
