import Mathlib.NumberTheory.Bertrand
import Erdos1212Kernel.ComponentRankConfinement

namespace Erdos1212Kernel

/-!
# Explicit exponential geometry for exact boundary rank

The fixed-rank confinement argument needs a quantitative bound which can be
combined with a growing rank cutoff.  The original implementation used a
factorial modulus.  After replacing it by the primorial, Bertrand's postulate
and `primorial_le_four_pow` give a completely explicit exponential bound.

No asymptotic prime estimate is used here.
-/

theorem nthPrime_le_two_pow_succ (n : Nat) :
    Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp [Nat.nth_prime_zero_eq_two]
  | succ n ih =>
      let current := Nat.nth Nat.Prime n
      have hcurrentPrime : Nat.Prime current := Nat.prime_nth_prime n
      obtain ⟨next, hnextPrime, hcurrentNext, hnextUpper⟩ :=
        Nat.exists_prime_lt_and_le_two_mul current hcurrentPrime.ne_zero
      have hcountCurrent :
          Nat.count Nat.Prime (current + 1) = n + 1 := by
        simpa [current] using
          Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime n
      have hcurrentSuccLeNext : current + 1 ≤ next := by omega
      have hcountNext :
          n + 1 ≤ Nat.count Nat.Prime next := by
        rw [← hcountCurrent]
        exact Nat.count_monotone Nat.Prime hcurrentSuccLeNext
      have hcountNextSucc :
          n + 2 ≤ Nat.count Nat.Prime (next + 1) := by
        rw [Nat.count_succ, if_pos hnextPrime]
        omega
      have hnthLt :
          Nat.nth Nat.Prime (n + 1) < next + 1 :=
        Nat.nth_lt_of_lt_count (by omega)
      have hnthLeNext :
          Nat.nth Nat.Prime (n + 1) ≤ next := by omega
      calc
        Nat.nth Nat.Prime (n + 1) ≤ next := hnthLeNext
        _ ≤ 2 * current := hnextUpper
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem add_two_le_two_pow_succ (n : Nat) :
    n + 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hone : 1 ≤ 2 ^ (n + 1) := by
        simpa using Nat.one_le_pow' (n + 1) 1
      rw [show n + 1 + 1 = n + 2 by omega, pow_succ]
      omega

theorem uniformCompositeSurvivorGap_le_sixteen_pow (H : Nat) :
    uniformCompositeSurvivorGap H ≤ 16 ^ (H + 1) := by
  calc
    uniformCompositeSurvivorGap H =
        Nat.nth Nat.Prime H * (H + 2) * uniformCoprimeModulus H := rfl
    _ ≤ 2 ^ (H + 1) * 2 ^ (H + 1) * 4 ^ (H + 1) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (nthPrime_le_two_pow_succ H)
          (add_two_le_two_pow_succ H))
        (uniformCoprimeModulus_le_four_pow H)
    _ = 16 ^ (H + 1) := by
      rw [← mul_pow, ← mul_pow]
      norm_num

theorem componentRankGap_le_sixteen_pow (K : Nat) :
    componentRankGap K ≤ 16 ^ (K + 6) := by
  simpa [componentRankGap] using
    uniformCompositeSurvivorGap_le_sixteen_pow (K + 5)

end Erdos1212Kernel
