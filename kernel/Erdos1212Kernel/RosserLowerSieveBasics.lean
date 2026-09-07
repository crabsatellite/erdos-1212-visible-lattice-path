import Mathlib.NumberTheory.SelbergSieve

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction BigOperators
open Finset Real Nat

set_option maxHeartbeats 1200000

namespace BoundingSieve

variable {s : BoundingSieve}

/-- Lower Rosser/Moebius coefficients: their divisor sum is bounded above by
the exact coprimality indicator. -/
def IsLowerMoebius (muMinus : Nat → Real) : Prop :=
  ∀ n : Nat, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

theorem sum_lowerMoebius_le_siftedSum
    (muMinus : Nat → Real) (hmu : IsLowerMoebius muMinus) :
    ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d ≤
      s.siftedSum := by
  have hreindex :
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
        ∑ n ∈ s.support,
          s.weights n *
            ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := by
    calc
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
          ∑ d ∈ divisors s.prodPrimes,
            ∑ n ∈ s.support,
              if d ∣ n then s.weights n * muMinus d else 0 := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [BoundingSieve.multSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        split_ifs <;> ring
      _ = ∑ n ∈ s.support,
          ∑ d ∈ divisors s.prodPrimes,
            if d ∣ n then s.weights n * muMinus d else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ n ∈ s.support,
          s.weights n *
            ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [Finset.mul_sum, ← Finset.sum_filter]
        have hsets :
            (divisors s.prodPrimes).filter (fun d => d ∣ n) =
              (Nat.gcd s.prodPrimes n).divisors := by
          rw [← divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
            (Nat.gcd_dvd_left _ _)]
          ext d
          simp +contextual [dvd_gcd_iff]
        rw [hsets]
  rw [hreindex, BoundingSieve.siftedSum_eq_sum_support_mul_ite]
  apply Finset.sum_le_sum
  intro n _hn
  apply mul_le_mul_of_nonneg_left
  · simpa using hmu (Nat.gcd s.prodPrimes n)
  · exact s.weights_nonneg n

theorem lowerMoebius_main_sub_error_le_siftedSum
    (muMinus : Nat → Real) (hmu : IsLowerMoebius muMinus) :
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤
      s.siftedSum := by
  have hraw := sum_lowerMoebius_le_siftedSum
    (s := s) muMinus hmu
  have hexpand :
      (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
        s.totalMass * s.mainSum muMinus +
          ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [s.multSum_eq_main_err]
    ring
  have hrem :
      -s.errSum muMinus ≤
        ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d _hd
    rw [← abs_mul]
    exact neg_abs_le (muMinus d * s.rem d)
  calc
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤
        s.totalMass * s.mainSum muMinus +
          ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d :=
      by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_left hrem (s.totalMass * s.mainSum muMinus)
    _ = ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d :=
      hexpand.symm
    _ ≤ s.siftedSum := hraw

end BoundingSieve

end

end Erdos1212Kernel
