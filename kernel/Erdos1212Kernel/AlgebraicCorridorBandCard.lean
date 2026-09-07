import Erdos1212Kernel.AlgebraicCorridorBandState
import Mathlib.Data.Nat.Log

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-! Quantitative finite-state facts that do not use a prime-counting
asymptotic.  They are the exact elementary part of the paper's estimate for
the set of prime factors of one finite band. -/

theorem two_pow_primeFactor_card_le {n : ℕ} (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n := by
  have hprodle : (∏ p ∈ n.primeFactors, p) ≤ n := by
    exact Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hprod : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc
      2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod'
        intro p hp
        have hpgt := (Nat.prime_of_mem_primeFactors hp).one_lt
        omega
  exact hprod.trans hprodle

theorem primeFactor_card_le_log {n : ℕ} (hn : 0 < n) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  exact Nat.le_log_of_pow_le (by norm_num) (two_pow_primeFactor_card_le hn)

theorem corridorBandPrimeFactors_card_le
    {lower B : ℕ} (hlower : 0 < lower) :
    (corridorBandPrimeFactors lower B).card ≤
      ∑ i ∈ Finset.range B, Nat.log 2 (lower + i) := by
  apply le_trans (Finset.card_biUnion_le)
  apply Finset.sum_le_sum
  intro i hi
  exact primeFactor_card_le_log (by omega)

theorem corridorBandPrimeFactors_card_le_mul_log
    {lower B U : ℕ} (hlower : 0 < lower)
    (hU : ∀ i ∈ Finset.range B, lower + i ≤ U) :
    (corridorBandPrimeFactors lower B).card ≤ B * Nat.log 2 U := by
  calc
    (corridorBandPrimeFactors lower B).card ≤
        ∑ i ∈ Finset.range B, Nat.log 2 (lower + i) :=
      corridorBandPrimeFactors_card_le hlower
    _ ≤ ∑ i ∈ Finset.range B, Nat.log 2 U := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.log_mono (b := 2) (c := 2) (by norm_num) (by rfl)
        (hU i hi)
    _ = B * Nat.log 2 U := by simp [Nat.mul_comm]

theorem corridorBandPrimeFactors_card_le_mul_logb
    {lower B U : ℕ} (hlower : 0 < lower)
    (hU : ∀ i ∈ Finset.range B, lower + i ≤ U) :
    ((corridorBandPrimeFactors lower B).card : ℝ) ≤
      (B : ℝ) * Real.logb 2 (U : ℝ) := by
  have hcard := corridorBandPrimeFactors_card_le (B := B) hlower
  have hcardR : ((corridorBandPrimeFactors lower B).card : ℝ) ≤
      ((∑ i ∈ Finset.range B, Nat.log 2 (lower + i) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc
    ((corridorBandPrimeFactors lower B).card : ℝ) ≤
        ((∑ i ∈ Finset.range B, Nat.log 2 (lower + i) : ℕ) : ℝ) := hcardR
    _ = ∑ i ∈ Finset.range B, (Nat.log 2 (lower + i) : ℝ) := by
      rw [Nat.cast_sum]
    _ ≤ ∑ i ∈ Finset.range B, (Nat.log 2 U : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact_mod_cast
        (Nat.log_mono (b := 2) (c := 2) (by norm_num) (by rfl)
          (hU i hi))
    _ = (B : ℝ) * (Nat.log 2 U : ℝ) := by simp
    _ ≤ (B : ℝ) * Real.logb 2 (U : ℝ) := by
      apply mul_le_mul_of_nonneg_left (Real.natLog_le_logb U 2)
      positivity

end

end Erdos1212Kernel
