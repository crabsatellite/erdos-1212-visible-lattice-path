import Erdos1212Kernel.TaoVdcEquationEightConsumer

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

def taoSelectedDecay (t : Real) (N : Nat) (hN : 2 ≤ N) : Real :=
  (1 / (N : Real)) ^
    (taoVdcBeta (taoFrequencyOrder N (taoLogFrequency t) hN + 1))

theorem taoSelectedDecay_nonneg (t : Real) (N : Nat) (hN : 2 ≤ N) :
    0 ≤ taoSelectedDecay t N hN := by
  unfold taoSelectedDecay
  exact Real.rpow_nonneg (by positivity) _

theorem taoDyadicWeighted_selected_decay (t σ : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hNT : (N : Real) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M, (taoDyadicWeight N σ m : Complex) *
        (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))‖ ≤
      (N : Real) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        taoSelectedDecay t N hN) := by
  let z : Nat → Complex := fun m =>
    (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))
  let w : Nat → Real := taoDyadicWeight N σ
  let B : Real := (N : Real) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
    taoSelectedDecay t N hN)
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : Real) := by exact_mod_cast hNpos
  have hT := taoLogFrequency_pos ht
  have hB : 0 ≤ B := by
    unfold B
    have hlog := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    exact mul_nonneg hNR.le (mul_nonneg (mul_nonneg (by positivity) hlog)
      (taoSelectedDecay_nonneg t N hN))
  have hprefix (m : Nat) (hm : m ≤ M) : ‖taoPrefixSum z m‖ ≤ B := by
    have hmN := hm.trans hMN
    have h := taoLogDirichlet_short_selected_decay t N m hN hmN ht hNT
    have hsum : taoPrefixSum z m =
        ∑ n ∈ taoCorputInterval (N : Int) m,
          (n : Complex) ^ (-(t : Complex) * Complex.I) := by
      unfold taoPrefixSum z
      rw [taoCorputInterval_sum_eq_range]
      apply Finset.sum_congr rfl
      intro i _hi
      norm_cast
    rw [hsum]
    unfold B taoSelectedDecay
    simpa only [mul_comm] using (div_le_iff₀ hNR).mp h
  have hweighted := taoWeightedPrefix_norm_bound z w M hB
    (fun n _hn => taoDyadicWeight_nonneg N σ n)
    (fun n _hn => taoDyadicWeight_antitone hNpos hσ n) hprefix
  rw [show w 0 = 1 by exact taoDyadicWeight_zero hNpos σ, mul_one] at hweighted
  exact hweighted

theorem taoDyadicComplexPower_selected_decay (t σ : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hNT : (N : Real) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        taoSelectedDecay t N hN) := by
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : Real) := by exact_mod_cast hNpos
  have hweighted := taoDyadicWeighted_selected_decay t σ N M hN hMN ht hσ hNT
  have hscale : 0 ≤ (N : Real) ^ (-σ) := Real.rpow_nonneg hNR.le _
  have hmul := mul_le_mul_of_nonneg_left hweighted hscale
  have hid := taoDyadicComplexPower_sum_identity N M hNpos σ t
  have hscaleN : (N : Real) ^ (-σ) * (N : Real) = (N : Real) ^ (1 - σ) := by
    calc
      _ = (N : Real) ^ (-σ) * (N : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (N : Real) ^ (-σ + 1) := by rw [Real.rpow_add hNR]
      _ = _ := by congr 1; ring
  have heq : (N : Real) ^ (-σ) * ((N : Real) *
      ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) * taoSelectedDecay t N hN)) =
      (N : Real) ^ (1 - σ) *
        ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) * taoSelectedDecay t N hN) := by
    rw [← mul_assoc, hscaleN]
  rw [← hid, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
  exact hmul.trans_eq heq

end

end Erdos1212Kernel
