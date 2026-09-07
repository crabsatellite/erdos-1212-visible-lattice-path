import Erdos1212Kernel.TaoFirstDerivativeScale
import Mathlib.Data.Int.Interval

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

/-- Exact reindexing, including all signs of the integer left endpoint. -/
theorem taoFirstDerivative_sum_Ico_eq_range (f : Real → Real) (a : Int) (M : Nat) :
    (∑ n ∈ Finset.Ico a (a + M), taoCorputPhase (f (n : Real))) =
      ∑ n ∈ Finset.range M, taoCorputPhase (f ((a : Real) + n)) := by
  rw [Int.Ico_eq_finset_map, show (a + (M : Int) - a).toNat = M by omega, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro n _hn
  simp

theorem taoFirstDerivative_sum_Icc_eq_range (f : Real → Real) (a : Int) (M : Nat) :
    (∑ n ∈ Finset.Icc a (a + M), taoCorputPhase (f (n : Real))) =
      ∑ n ∈ Finset.range (M + 1), taoCorputPhase (f ((a : Real) + n)) := by
  rw [Int.Icc_eq_finset_map, show (a + (M : Int) + 1 - a).toNat = M + 1 by omega, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro n _hn
  simp

theorem taoFirstDerivative_integer_interval_bound (f f' f'' : Real → Real) (a b : Int)
    {A N T : Real} (hab : a ≤ b) (hA : 1 ≤ A) (hN : 1 ≤ N) (hT : 0 < T)
    (hlength : (b : Real) - a ≤ N) (hsmall : T ≤ N / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) b, HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc (a : Real) b, T / (A * N) ≤ |f' t|)
    (hfirst : ∀ t ∈ Set.Icc (a : Real) b, |f' t| ≤ A * T / N)
    (hsecond : ∀ t ∈ Set.Icc (a : Real) b, |f'' t| ≤ A * T / N ^ 2) :
    ‖∑ n ∈ Finset.Ico a b, taoCorputPhase (f (n : Real))‖ / N ≤ (2 + 2 * Real.pi) * A ^ 3 / T := by
  have heInt : a + ((b - a).toNat : Int) = b := by omega
  have heReal : (a : Real) + ((b - a).toNat : Real) = b := by exact_mod_cast heInt
  have hM : ((b - a).toNat : Real) ≤ N := by linarith
  have hsum := taoFirstDerivative_sum_Ico_eq_range f a (b - a).toNat
  rw [heInt] at hsum
  rw [hsum]
  apply taoFirstDerivative_scaled_sum_bound f f' f'' (a : Real) (b - a).toNat hA hN hT hM hsmall
  · simpa only [heReal] using hf
  · simpa only [heReal] using hf'
  · simpa only [heReal] using hlow
  · simpa only [heReal] using hfirst
  · simpa only [heReal] using hsecond

theorem taoFirstDerivative_integer_closed_interval_bound (f f' f'' : Real → Real) (a b : Int)
    {A N T : Real} (hab : a ≤ b) (hA : 1 ≤ A) (hN : 1 ≤ N) (hT : 0 < T)
    (hlength : (b : Real) - a ≤ N) (hsmall : T ≤ N / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) b, HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc (a : Real) b, T / (A * N) ≤ |f' t|)
    (hfirst : ∀ t ∈ Set.Icc (a : Real) b, |f' t| ≤ A * T / N)
    (hsecond : ∀ t ∈ Set.Icc (a : Real) b, |f'' t| ≤ A * T / N ^ 2) :
    ‖∑ n ∈ Finset.Icc a b, taoCorputPhase (f (n : Real))‖ / N ≤ (3 + 2 * Real.pi) * A ^ 3 / T := by
  have heInt : a + ((b - a).toNat : Int) = b := by omega
  have heReal : (a : Real) + ((b - a).toNat : Real) = b := by exact_mod_cast heInt
  have hM : ((b - a).toNat : Real) ≤ N := by linarith
  have hsum := taoFirstDerivative_sum_Icc_eq_range f a (b - a).toNat
  rw [heInt] at hsum
  rw [hsum]
  apply taoFirstDerivative_scaled_closed_sum_bound f f' f'' (a : Real) (b - a).toNat hA hN hT hM hsmall
  · simpa only [heReal] using hf
  · simpa only [heReal] using hf'
  · simpa only [heReal] using hlow
  · simpa only [heReal] using hfirst
  · simpa only [heReal] using hsecond

end

end Erdos1212Kernel
