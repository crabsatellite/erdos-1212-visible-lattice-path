import Erdos1212Kernel.TaoDyadicComplexPower

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1700000

theorem taoFrequencyOrder_exists (N : Nat) (T : Real) (hN : 2 ≤ N) :
    ∃ k : Nat, T ≤ (N : Real) ^ k := by
  obtain ⟨m, hm⟩ := exists_nat_gt T
  have hm2 : (m : Real) ≤ (2 : Real) ^ m := by exact_mod_cast taoLog_nat_le_two_pow m
  have h2N : (2 : Real) ≤ N := by exact_mod_cast hN
  have hpow : (2 : Real) ^ m ≤ (N : Real) ^ m := pow_le_pow_left₀ (by norm_num) h2N m
  exact ⟨m, hm.le.trans (hm2.trans hpow)⟩

def taoFrequencyOrder (N : Nat) (T : Real) (hN : 2 ≤ N) : Nat :=
  max 2 (Nat.find (taoFrequencyOrder_exists N T hN))

theorem taoFrequencyOrder_two_le (N : Nat) (T : Real) (hN : 2 ≤ N) :
    2 ≤ taoFrequencyOrder N T hN := by
  unfold taoFrequencyOrder
  exact Nat.le_max_left _ _

theorem taoFrequencyOrder_upper (N : Nat) (T : Real) (hN : 2 ≤ N) :
    T ≤ (N : Real) ^ (taoFrequencyOrder N T hN) := by
  let hex := taoFrequencyOrder_exists N T hN
  have hspec := Nat.find_spec hex
  have hindex : Nat.find hex ≤ taoFrequencyOrder N T hN := by
    unfold taoFrequencyOrder
    exact Nat.le_max_right _ _
  have hN1 : 1 ≤ N := by omega
  have hNR : 1 ≤ (N : Real) := by exact_mod_cast hN1
  exact hspec.trans (pow_le_pow_right₀ hNR hindex)

theorem taoFrequencyOrder_lower (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hNT : (N : Real) ≤ T) :
    (N : Real) ^ (taoFrequencyOrder N T hN - 1) ≤ T := by
  let hex := taoFrequencyOrder_exists N T hN
  let f := Nat.find hex
  change (N : Real) ^ (max 2 f - 1) ≤ T
  by_cases hf : f ≤ 2
  · rw [max_eq_left hf]
    norm_num
    exact hNT
  · have h2f : 2 ≤ f := by omega
    rw [max_eq_right h2f]
    have hpred : f - 1 < f := by omega
    have hnot := Nat.find_min hex hpred
    exact (lt_of_not_ge hnot).le

theorem taoFrequencyOrder_band (N : Nat) (T : Real) (hN : 2 ≤ N)
    (hNT : (N : Real) ≤ T) :
    (N : Real) ^ (taoFrequencyOrder N T hN - 1) ≤ T ∧
      T ≤ (N : Real) ^ (taoFrequencyOrder N T hN) :=
  ⟨taoFrequencyOrder_lower N T hN hNT, taoFrequencyOrder_upper N T hN⟩

/-- The order is now selected internally from the actual dyadic scale
and logarithmic frequency. -/
theorem taoDyadicComplexPower_selected_order_bound (t σ : Real) (N M : Nat)
    (hN : 2 ≤ N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hNT : (N : Real) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ (taoFrequencyOrder N (taoLogFrequency t) hN)) ^
          (taoVdcBeta (taoFrequencyOrder N (taoLogFrequency t) hN))) := by
  let k := taoFrequencyOrder N (taoLogFrequency t) hN
  have hk := taoFrequencyOrder_two_le N (taoLogFrequency t) hN
  have hNpos : 0 < N := by omega
  have hlow := taoFrequencyOrder_lower N (taoLogFrequency t) hN hNT
  exact taoDyadicComplexPower_band_bound t σ k N M hk hNpos hMN ht hσ hlow

theorem taoFrequencyOrder_selected_ratio_le_one (t : Real) (N : Nat)
    (hN : 2 ≤ N) (ht : t ≠ 0) :
    (taoLogFrequency t / (N : Real) ^ (taoFrequencyOrder N (taoLogFrequency t) hN)) ^
        (taoVdcBeta (taoFrequencyOrder N (taoLogFrequency t) hN)) ≤ 1 := by
  have hT := taoLogFrequency_pos ht
  have hupper := taoFrequencyOrder_upper N (taoLogFrequency t) hN
  have hden : 0 < (N : Real) ^ (taoFrequencyOrder N (taoLogFrequency t) hN) := by positivity
  have hratio : taoLogFrequency t /
      (N : Real) ^ (taoFrequencyOrder N (taoLogFrequency t) hN) ≤ 1 :=
    (div_le_one hden).2 hupper
  have hb := taoVdcBeta_pos (taoFrequencyOrder_two_le N (taoLogFrequency t) hN)
  simpa only [Real.one_rpow] using Real.rpow_le_rpow (by positivity) hratio hb.le

end

end Erdos1212Kernel
