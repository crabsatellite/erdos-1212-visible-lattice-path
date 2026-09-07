import Erdos1212Kernel.TaoWeightedPrefixAbel

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

def taoDyadicWeight (N : Nat) (σ : Real) (m : Nat) : Real :=
  ((N : Real) / (N + m : Nat)) ^ σ

theorem taoDyadicWeight_nonneg (N : Nat) (σ : Real) (m : Nat) : 0 ≤ taoDyadicWeight N σ m := by
  unfold taoDyadicWeight
  exact Real.rpow_nonneg (by positivity) _

theorem taoDyadicWeight_zero {N : Nat} (hN : 0 < N) (σ : Real) : taoDyadicWeight N σ 0 = 1 := by
  unfold taoDyadicWeight
  rw [Nat.add_zero, div_self (by exact_mod_cast (Nat.ne_of_gt hN)), Real.one_rpow]

theorem taoDyadicWeight_antitone {N : Nat} (hN : 0 < N) {σ : Real} (hσ : 0 ≤ σ) (m : Nat) :
    taoDyadicWeight N σ (m + 1) ≤ taoDyadicWeight N σ m := by
  have hNR : 0 ≤ (N : Real) := by positivity
  have hd0 : 0 < ((N + m : Nat) : Real) := by positivity
  have hd1 : 0 < ((N + (m + 1) : Nat) : Real) := by positivity
  have hden : ((N + m : Nat) : Real) ≤ (N + (m + 1) : Nat) := by exact_mod_cast (by omega : N + m ≤ N + (m + 1))
  have hdiv : (N : Real) / (N + (m + 1) : Nat) ≤ (N : Real) / (N + m : Nat) :=
    div_le_div_of_nonneg_left hNR hd0 hden
  exact Real.rpow_le_rpow (by positivity) hdiv hσ

theorem taoCorputInterval_sum_eq_range {E : Type*} [AddCommMonoid E] (g : Int → E)
    (a : Int) (M : Nat) :
    (∑ n ∈ taoCorputInterval a M, g n) = ∑ m ∈ Finset.range M, g (a + m) := by
  unfold taoCorputInterval
  rw [Int.Ico_eq_finset_map, show (a + (M : Int) - a).toNat = M by omega, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m _hm
  simp

/-- The weighted dyadic block is controlled by the same optimized bound
for every literal short prefix. This is the finite partial-summation
consumer used in the zeta reduction. -/
theorem taoDyadicWeightedDirichlet_band_bound (t σ : Real) (k N M : Nat)
    (hk : 2 ≤ k) (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hlow : (N : Real) ^ (k - 1) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M, (taoDyadicWeight N σ m : Complex) *
        (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))‖ ≤
      (N : Real) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k)) := by
  let z : Nat → Complex := fun m =>
    (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))
  let w : Nat → Real := taoDyadicWeight N σ
  let B : Real := (N : Real) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
    (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k))
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hT := taoLogFrequency_pos ht
  have hB : 0 ≤ B := by
    unfold B
    have hlog : 0 ≤ Real.log (2 + taoLogFrequency t) := Real.log_nonneg (by linarith)
    positivity
  have hprefix (m : Nat) (hm : m ≤ M) : ‖taoPrefixSum z m‖ ≤ B := by
    have hmN := hm.trans hMN
    have h := taoLogDirichlet_short_band_bound t k N m hk hN hmN ht hlow
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

end

end Erdos1212Kernel
