import Erdos1212Kernel.IwaniecPaperAStirlingTail

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

/-- A short layer has index at most `degree`, not `degree+1`.  Keeping this
endpoint is essential when the real splitting point is rounded upward. -/
theorem iwaniecCubicRealProductCount_sum_short_le_degree
    (offset : Nat) (level : Real) (factors : List Nat) (upper degree : Nat)
    {z : Real} (hz : 1 ≤ z) (hsize : (factors.length : Real) ≤ z)
    (hupper : upper ≤ degree + 1) :
    (∑ k ∈ Finset.range upper,
      (iwaniecCubicRealProductCount offset level factors k : Real)) ≤ 3 * z ^ degree := by
  have hterm : ∀ k ∈ Finset.range upper,
      (iwaniecCubicRealProductCount offset level factors k : Real) ≤
        z ^ degree * (1 / (k.factorial : Real)) := by
    intro k hk
    have hcount : (iwaniecCubicRealProductCount offset level factors k : Real) ≤
        factors.length.choose k := by
      exact_mod_cast iwaniecCubicRealProductCount_le_choose offset level factors k
    have hchoose := Nat.choose_le_pow_div (α := Real) k factors.length
    have hpower : (factors.length : Real) ^ k ≤ z ^ degree := by
      exact (pow_le_pow_left₀ (by positivity) hsize k).trans
        (pow_le_pow_right₀ hz (by have := Finset.mem_range.mp hk; omega))
    have hdiv := div_le_div_of_nonneg_right hpower
      (by positivity : (0 : Real) ≤ k.factorial)
    exact (hcount.trans hchoose).trans (by simpa [div_eq_mul_inv] using hdiv)
  have hexp : (∑ k ∈ Finset.range upper, (1 : Real) / k.factorial) ≤ Real.exp 1 := by
    simpa using Real.sum_le_exp_of_nonneg (x := (1 : Real)) (by norm_num) upper
  calc
    (∑ k ∈ Finset.range upper,
        (iwaniecCubicRealProductCount offset level factors k : Real)) ≤
        ∑ k ∈ Finset.range upper, z ^ degree * (1 / (k.factorial : Real)) :=
      Finset.sum_le_sum hterm
    _ = z ^ degree * ∑ k ∈ Finset.range upper, (1 : Real) / k.factorial := by
      rw [Finset.mul_sum]
    _ ≤ z ^ degree * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hexp (pow_nonneg (by linarith) _)
    _ ≤ z ^ degree * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
      (pow_nonneg (by linarith) _)
    _ = 3 * z ^ degree := by ring

theorem iwaniecPaperSupportCount_sharp_short_long_bound
    (rank K : Nat) (hKPos : 0 < K) {level z : Real}
    (hlevel : 0 ≤ level) (hz : 1 ≤ z)
    (hthreshold : 2 * iwaniecStrictPrimeReciprocalSum z ≤ (K + 1 : Nat)) :
    (iwaniecPaperSupportCount rank level z : Real) ≤
      3 * z ^ (K - 1) +
        2 * level * (iwaniecStrictPrimeReciprocalSum z) ^ K / K.factorial := by
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  let offset := if Even rank then 1 else 0
  have hsize : (factors.length : Real) ≤ z := by
    simpa [factors, iwaniecDescendingFactors] using
      iwaniecStrictPrimePool_card_le (by linarith : 0 ≤ z)
  have hpos : ∀ p ∈ factors, 0 < p := by
    apply iwaniecDescendingFactors_positive
    intro p hp
    exact (mem_iwaniecStrictPrimePool.mp hp).1
  have hrecip : (factors.map (fun p : Nat => (p : Real)⁻¹)).sum =
      iwaniecStrictPrimeReciprocalSum z := iwaniecStrictPrimeReciprocalSum_eq_list z
  have hnonneg : 0 ≤ iwaniecStrictPrimeReciprocalSum z := by
    unfold iwaniecStrictPrimeReciprocalSum
    exact Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  unfold iwaniecPaperSupportCount
  rw [Nat.cast_sum]
  change (∑ k ∈ Finset.range (rank + 1),
    (iwaniecCubicRealProductCount offset level factors k : Real)) ≤ _
  by_cases hK : K ≤ rank + 1
  · have hshort := iwaniecCubicRealProductCount_sum_short_le_degree
      offset level factors K (K - 1) hz hsize (by omega)
    have hlong := iwaniecCubicRealProductCount_sum_tail_le
      offset level factors K (rank + 1) hlevel hpos (by rwa [hrecip])
    rw [hrecip] at hlong
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => (iwaniecCubicRealProductCount offset level factors k : Real)) hK
    rw [← hsplit]
    exact add_le_add hshort hlong
  · have hshort := iwaniecCubicRealProductCount_sum_short_le_degree
      offset level factors (rank + 1) (K - 1) hz hsize (by omega)
    have htailNonneg : 0 ≤
        2 * level * (iwaniecStrictPrimeReciprocalSum z) ^ K / K.factorial := by positivity
    exact hshort.trans (le_add_of_nonneg_right htailNonneg)

theorem eventually_iwaniecPaperA_sharp_stirling_bound :
    ∀ᶠ level : Real in atTop, ∀ rank K : Nat, ∀ s : Real,
      0 < K → 1 ≤ s → 6 * Real.log (Real.log level) ≤ (K + 1 : Nat) →
      (iwaniecPaperA rank level s : Real) ≤
        3 * Real.exp (((K - 1 : Nat) : Real) * Real.log level / s) +
          2 * level * (3 * Real.log (Real.log level) / K) ^ K := by
  filter_upwards [eventually_iwaniecExp_mul_primeReciprocal_le_three_loglog,
    eventually_gt_atTop (1 : Real)] with level hM hlevel
  intro rank K s hK hs hthreshold
  let z := Real.exp (Real.log level / s)
  have hzOne : 1 ≤ z := Real.one_le_exp_iff.mpr
    (div_nonneg (Real.log_pos hlevel).le (by linarith))
  have hzLevel : z ≤ level := iwaniecPaperCutoff_le_level hlevel hs
  let M := iwaniecStrictPrimeReciprocalSum z
  have hMNonneg : 0 ≤ M := by
    exact Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have heM : Real.exp 1 * M ≤ 3 * Real.log (Real.log level) := hM z hzLevel
  have hMLe : M ≤ 3 * Real.log (Real.log level) := by
    have he : 1 ≤ Real.exp 1 := by have := Real.exp_one_gt_two; linarith
    nlinarith
  have hcount := iwaniecPaperSupportCount_sharp_short_long_bound rank K hK
    (zero_le_one.trans hlevel.le) hzOne (by change 2 * M ≤ (K + 1 : Nat); linarith)
  have htail := iwaniecFactorialTerm_le_stirling_power hMNonneg K hK
  have hKPos : (0 : Real) < K := by exact_mod_cast hK
  have hbase := div_le_div_of_nonneg_right heM hKPos.le
  have hbaseNonneg : 0 ≤ Real.exp 1 * M / K := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    (htail.trans (pow_le_pow_left₀ hbaseNonneg hbase K))
    (by positivity : (0 : Real) ≤ 2 * level)
  have hzPower : z ^ (K - 1) =
      Real.exp (((K - 1 : Nat) : Real) * Real.log level / s) := by
    dsimp [z]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hzPower] at hcount
  change (iwaniecPaperA rank level s : Real) ≤
    3 * Real.exp (((K - 1 : Nat) : Real) * Real.log level / s) +
      2 * level * M ^ K / K.factorial at hcount
  unfold iwaniecFactorialTerm at hscaled
  have htailScaled : 2 * level * M ^ K / K.factorial ≤
      2 * level * (3 * Real.log (Real.log level) / K) ^ K := by
    simpa only [mul_div_assoc] using hscaled
  exact hcount.trans (add_le_add le_rfl htailScaled)

end

end Erdos1212Kernel
