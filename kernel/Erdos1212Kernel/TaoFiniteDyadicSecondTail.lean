import Erdos1212Kernel.TaoSecondDerivativeDyadicTail

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoFiniteDyadic_interval_decomposition (f : Nat → Complex)
    (J K : Nat) (hJK : J ≤ K) :
    (∑ r ∈ Finset.Ico J K, taoDyadicBlock f r) =
      ∑ n ∈ Finset.Ico (2 ^ J) (2 ^ K), f n := by
  induction K with
  | zero =>
      have hJ : J = 0 := by omega
      subst J
      simp
  | succ K ih =>
      by_cases hJK' : J ≤ K
      · rw [Finset.sum_Ico_succ_top hJK', ih hJK', taoDyadicBlock_eq_Ico]
        rw [Finset.sum_Ico_consecutive]
        · exact pow_le_pow_right₀ (by norm_num) hJK'
        · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · have hJ : J = K + 1 := by omega
        subst J
        simp

theorem taoDyadic_secondDerivative_uniform_tail_block
    (t σ : Real) (J K r : Nat) (ht : t ≠ 0)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hJr : J ≤ r) (hrK : r < K) :
    ‖taoDyadicBlock (taoZetaTerm σ t) r‖ ≤
      (2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ)) := by
  have hNr : 0 < 2 ^ r := by positivity
  have hblock := taoDyadicComplexPower_secondDerivative_bound
    t σ (2 ^ r) (2 ^ r) hNr le_rfl ht hσ0
  rw [taoDyadicBlock_zeta_eq]
  have hbaseR : (0 : Real) < ((2 ^ r : Nat) : Real) := by positivity
  have hbaseJ : (0 : Real) < ((2 ^ J : Nat) : Real) := by positivity
  have hbaseK : (0 : Real) < ((2 ^ K : Nat) : Real) := by positivity
  have hrKpowNat : 2 ^ r ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hJrpowNat : 2 ^ J ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hJr
  have hrKpow : (((2 ^ r : Nat) : Real)) ≤ ((2 ^ K : Nat) : Real) := by exact_mod_cast hrKpowNat
  have hJrpow : (((2 ^ J : Nat) : Real)) ≤ ((2 ^ r : Nat) : Real) := by exact_mod_cast hJrpowNat
  have hdelta : 0 ≤ 1 - σ := by linarith
  have hfirstPow : (((2 ^ r : Nat) : Real)) ^ (1 - σ) ≤
      (((2 ^ K : Nat) : Real)) ^ (1 - σ) :=
    Real.rpow_le_rpow hbaseR.le hrKpow hdelta
  have hsecondPow : (((2 ^ r : Nat) : Real)) ^ (-σ) ≤
      (((2 ^ J : Nat) : Real)) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hbaseJ hJrpow (by linarith)
  have hlog : 0 ≤ Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t) := by
    have hT := taoLogFrequency_pos ht
    have hlog0 := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  have hsqrt : 0 ≤ Real.sqrt (taoLogFrequency t) := Real.sqrt_nonneg _
  apply hblock.trans
  unfold taoSecondDerivativeRate
  have hscale : (((2 ^ r : Nat) : Real)) ^ (1 - σ) /
      ((2 ^ r : Nat) : Real) = (((2 ^ r : Nat) : Real)) ^ (-σ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hbaseR]
    congr 1 <;> ring
  have hsecondEq : (((2 ^ r : Nat) : Real)) ^ (1 - σ) *
      (Real.sqrt (taoLogFrequency t) / ((2 ^ r : Nat) : Real)) =
        Real.sqrt (taoLogFrequency t) * (((2 ^ r : Nat) : Real)) ^ (-σ) := by
    rw [show (((2 ^ r : Nat) : Real)) ^ (1 - σ) *
        (Real.sqrt (taoLogFrequency t) / ((2 ^ r : Nat) : Real)) =
          Real.sqrt (taoLogFrequency t) *
            ((((2 ^ r : Nat) : Real)) ^ (1 - σ) / ((2 ^ r : Nat) : Real)) by ring,
      hscale]
  have hfirstTerm : (((2 ^ r : Nat) : Real)) ^ (1 - σ) *
      Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t) ≤
        (((2 ^ K : Nat) : Real)) ^ (1 - σ) *
          Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t) := by
    calc
      _ = (((2 ^ r : Nat) : Real)) ^ (1 - σ) *
          (Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) := by ring
      _ ≤ (((2 ^ K : Nat) : Real)) ^ (1 - σ) *
          (Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) :=
        mul_le_mul_of_nonneg_right hfirstPow hlog
      _ = _ := by ring
  calc
    _ = (2 : Real) ^ 20 *
        (((((2 ^ r : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ r : Nat) : Real)) ^ (-σ)) := by
      calc
        _ = (2 : Real) ^ 20 *
            (((((2 ^ r : Nat) : Real)) ^ (1 - σ) *
                Real.log (2 + taoLogFrequency t) /
                  Real.sqrt (taoLogFrequency t)) +
              (((2 ^ r : Nat) : Real)) ^ (1 - σ) *
                (Real.sqrt (taoLogFrequency t) / ((2 ^ r : Nat) : Real))) := by ring
        _ = _ := by rw [hsecondEq]
    _ ≤ (2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        hfirstTerm
        (mul_le_mul_of_nonneg_left hsecondPow hsqrt)

theorem taoFiniteDyadic_secondDerivative_tail
    (t σ : Real) (J K : Nat) (ht : t ≠ 0)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hJK : J ≤ K) :
    ‖∑ n ∈ Finset.Ico (2 ^ J) (2 ^ K), taoZetaTerm σ t n‖ ≤
      ((K - J : Nat) : Real) * ((2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ))) := by
  rw [← taoFiniteDyadic_interval_decomposition (taoZetaTerm σ t) J K hJK]
  calc
    _ ≤ ∑ r ∈ Finset.Ico J K, ‖taoDyadicBlock (taoZetaTerm σ t) r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.Ico J K, (2 : Real) ^ 20 *
        (((((2 ^ K : Nat) : Real)) ^ (1 - σ) *
            Real.log (2 + taoLogFrequency t) / Real.sqrt (taoLogFrequency t)) +
          Real.sqrt (taoLogFrequency t) *
            (((2 ^ J : Nat) : Real)) ^ (-σ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact taoDyadic_secondDerivative_uniform_tail_block t σ J K r ht hσ0 hσ1
        (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
    _ = _ := by simp [nsmul_eq_mul]

end

end Erdos1212Kernel
