import Erdos1212Kernel.TaoLittlewoodThreshold
import Erdos1212Kernel.TaoDyadicComplexPower

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoLogDirichlet_short_secondDerivative_bound (t : Real) (N M : Nat)
    (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0) :
    ‖∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      (2 : Real) ^ 20 * taoSecondDerivativeRate N (taoLogFrequency t) := by
  have hraw := taoLogDirichlet_short_vdc_bound t 2 N M (by norm_num) hN hMN ht
  rw [taoVdcRate_two (N := (N : Real)) (T := taoLogFrequency t)
    (by positivity) (taoLogFrequency_pos ht), taoVdc_amplitude_two] at hraw
  have hrate : 0 ≤ taoSecondDerivativeRate (N : Real) (taoLogFrequency t) :=
    taoSecondDerivative_rate_nonneg (by positivity) (taoLogFrequency_pos ht)
  have hcoef : 256 * taoLogDerivativeAmplitude 2 ^ 2 ≤ (2 : Real) ^ 20 := by
    norm_num [taoLogDerivativeAmplitude]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hrate)

theorem taoDyadicWeightedDirichlet_secondDerivative_bound
    (t σ : Real) (N M : Nat) (hN : 0 < N) (hMN : M ≤ N)
    (ht : t ≠ 0) (hσ : 0 ≤ σ) :
    ‖∑ m ∈ Finset.range M, (taoDyadicWeight N σ m : Complex) *
        (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))‖ ≤
      (N : Real) * ((2 : Real) ^ 20 *
        taoSecondDerivativeRate N (taoLogFrequency t)) := by
  let z : Nat → Complex := fun m =>
    (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))
  let w : Nat → Real := taoDyadicWeight N σ
  let B : Real := (N : Real) * ((2 : Real) ^ 20 *
    taoSecondDerivativeRate N (taoLogFrequency t))
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hB : 0 ≤ B := by
    unfold B
    have hrate := taoSecondDerivative_rate_nonneg hNp (taoLogFrequency_pos ht)
    positivity
  have hprefix (m : Nat) (hm : m ≤ M) : ‖taoPrefixSum z m‖ ≤ B := by
    have hmN := hm.trans hMN
    have h := taoLogDirichlet_short_secondDerivative_bound t N m hN hmN ht
    have hsum : taoPrefixSum z m =
        ∑ n ∈ taoCorputInterval (N : Int) m,
          (n : Complex) ^ (-(t : Complex) * Complex.I) := by
      unfold taoPrefixSum z
      rw [taoCorputInterval_sum_eq_range]
      apply Finset.sum_congr rfl
      intro i _hi
      norm_cast
    rw [hsum]
    unfold B
    simpa only [mul_comm] using (div_le_iff₀ hNp).mp h
  have hweighted := taoWeightedPrefix_norm_bound z w M hB
    (fun n _hn => taoDyadicWeight_nonneg N σ n)
    (fun n _hn => taoDyadicWeight_antitone hN hσ n) hprefix
  rw [show w 0 = 1 by exact taoDyadicWeight_zero hN σ, mul_one] at hweighted
  exact hweighted

/-- Uniform k=2 tail block, valid on both sides of the frequency scale.
This is the high-scale consumer needed when the Euler cutoff is moved
from `T` to `T^2`. -/
theorem taoDyadicComplexPower_secondDerivative_bound
    (t σ : Real) (N M : Nat) (hN : 0 < N) (hMN : M ≤ N)
    (ht : t ≠ 0) (hσ : 0 ≤ σ) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^
          (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 20 *
        taoSecondDerivativeRate N (taoLogFrequency t)) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hweighted := taoDyadicWeightedDirichlet_secondDerivative_bound
    t σ N M hN hMN ht hσ
  have hscale : 0 ≤ (N : Real) ^ (-σ) := Real.rpow_nonneg hNR.le _
  have hmul := mul_le_mul_of_nonneg_left hweighted hscale
  have hid := taoDyadicComplexPower_sum_identity N M hN σ t
  have hscaleN : (N : Real) ^ (-σ) * (N : Real) =
      (N : Real) ^ (1 - σ) := by
    calc
      _ = (N : Real) ^ (-σ) * (N : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (N : Real) ^ (-σ + 1) := by rw [Real.rpow_add hNR]
      _ = _ := by congr 1 <;> ring
  rw [← hid, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscale]
  calc
    _ ≤ (N : Real) ^ (-σ) * ((N : Real) *
        ((2 : Real) ^ 20 * taoSecondDerivativeRate N (taoLogFrequency t))) := hmul
    _ = _ := by rw [← mul_assoc, hscaleN]

end

end Erdos1212Kernel
