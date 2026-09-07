import Erdos1212Kernel.IwaniecCorollaryThreeStrictBand

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

theorem iwaniecPaperChild_weight_base_eq {level : Real} (hy : 1 < level)
    {p : Nat} (hp : p.Prime) (ht : 2 ≤ Real.log level / Real.log (p : Real)) :
    iwaniecAuxWeightBase (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) =
      1 + Real.log (Real.log level / Real.log (p : Real) - 1) ^ 5 / Real.log (p : Real) ^ 2 := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hl : Real.log (p : Real) ≠ 0 := hp.log_ne_zero
  have hshift : Real.log level / Real.log (p : Real) - 1 ≠ 0 := by linarith
  have hdiff : Real.log level - Real.log (p : Real) ≠ 0 := by
    intro heq
    have hsame := sub_eq_zero.mp heq
    rw [hsame, div_self hl] at ht
    norm_num at ht
  have hlogchild : Real.log (level / (p : Real)) =
      (Real.log level / Real.log (p : Real) - 1) * Real.log (p : Real) := by
    rw [Real.log_div (by linarith : level ≠ 0) hp0.ne']
    field_simp [hl]
  unfold iwaniecAuxWeightBase
  rw [hlogchild]
  field_simp [hl, hshift, hdiff]
  <;> ring

theorem iwaniecPaperChild_weight_le_source_base {level : Real} (hy : 1 < level)
    {p : Nat} (hp : p.Prime) (ht : 2 ≤ Real.log level / Real.log (p : Real)) :
    iwaniecAuxWeightPower (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) ≤
      (1 + Real.log (Real.log level / Real.log (p : Real)) ^ 5 / Real.log (p : Real) ^ 2) ^
        (5 * (Real.log level / Real.log (p : Real) - 1)) := by
  let t := Real.log level / Real.log (p : Real)
  have ht1 : 1 ≤ t - 1 := by dsimp [t]; linarith
  have hlog := Real.log_le_log (show 0 < t - 1 by linarith) (show t - 1 ≤ t by linarith)
  have hpow := pow_le_pow_left₀ (Real.log_nonneg ht1) hlog 5
  have hbase : iwaniecAuxWeightBase (level / (p : Real)) (t - 1) ≤
      1 + Real.log t ^ 5 / Real.log (p : Real) ^ 2 := by
    rw [iwaniecPaperChild_weight_base_eq hy hp ht]
    have hh := div_le_div_of_nonneg_right hpow (sq_nonneg (Real.log (p : Real)))
    linarith only [hh]
  exact Real.rpow_le_rpow (iwaniecAuxWeightBase_pos (level / (p : Real)) ht1).le hbase (by linarith)

/-- Literal child level y/p and child parameter log(y/p)/log(p).
The equalities are proved before the log(t-1)<=log(t) estimate is used. -/
theorem iwaniecPaperChild_weighted_majorant_le_source (rank : Nat)
    {level : Real} (hy : 1 < level) {p : Nat} (hp : p.Prime)
    (ht : iwaniecCorollaryThreeDomainStart rank ≤ Real.log level / Real.log (p : Real)) :
    (iwaniecAuxWeightPower (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) *
      iwaniecAuxG rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
        Real.log (level / (p : Real)) ^ 2) * (level / (p : Real)) ≤
      level * (iwaniecCorollaryThreePrimeWeight rank level p / (p : Real)) := by
  rw [iwaniecPaperChild_logParameter (by linarith : 0 < level) hp]
  have ht2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans ht
  have hW := iwaniecPaperChild_weight_le_source_base hy hp ht2
  have harg : iwaniecAuxGStart rank ≤ Real.log level / Real.log (p : Real) - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at ht
    linarith only [ht]
  have hG := (iwaniecAuxG_pos_exactDomain rank harg).le
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hW hG)
      (sq_nonneg (Real.log (level / (p : Real)))))
    (show 0 ≤ level / (p : Real) by positivity)
  convert hh using 1 <;> unfold iwaniecCorollaryThreePrimeWeight <;> ring

theorem iwaniecPaperBand_child_parameter_lower
    {level s R : Real} (hy : 1 < level) (hs : 0 < s) {p : Nat}
    (hp : p ∈ iwaniecStrictPrimeBand R (Real.exp (Real.log level / s))) :
    s ≤ Real.log level / Real.log (p : Real) := by
  obtain ⟨hpPool, _hpR⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprime, hpA⟩ := mem_iwaniecStrictPrimePool.mp hpPool
  have hp0 : (0 : Real) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : Real) < p := by exact_mod_cast hprime.one_lt
  have hlog := Real.log_le_log hp0 hpA.le
  rw [Real.log_exp] at hlog
  apply (le_div_iff₀ (Real.log_pos hp1)).mpr
  have hh := (le_div_iff₀ hs).mp hlog
  linarith only [hh]

theorem iwaniecPaperBand_child_majorant_sum_le (rank : Nat)
    {level s R : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    (∑ p ∈ iwaniecStrictPrimeBand R (Real.exp (Real.log level / s)),
      (iwaniecAuxWeightPower (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) *
        iwaniecAuxG rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
          Real.log (level / (p : Real)) ^ 2) * (level / (p : Real))) ≤
      level * ∑ p ∈ iwaniecStrictPrimeBand R (Real.exp (Real.log level / s)),
        iwaniecCorollaryThreePrimeWeight rank level p / (p : Real) := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1).1
  exact iwaniecPaperChild_weighted_majorant_le_source rank hy hprime
    (hs.trans (iwaniecPaperBand_child_parameter_lower hy (by linarith) hp))

theorem exists_iwaniecPaperBand_child_majorant_bound :
    ∃ C : Real, 0 < C ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        (iwaniecAuxWeightPower (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) *
          iwaniecAuxG rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
            Real.log (level / (p : Real)) ^ 2) * (level / (p : Real))) ≤
      level * ((iwaniecAuxWeightPower level (max iwaniecAuxSZero s) * iwaniecAuxG (rank + 1) s /
        Real.log level ^ 2) *
        (1 + 100 * C * iwaniecPaperXi level ^ 2 *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_iwaniecCorollaryThree_strict_band_constant
  refine ⟨C, hC, ?_⟩
  intro rank level s hy hξ hs hsξ
  exact (iwaniecPaperBand_child_majorant_sum_le rank hy hs).trans
    (mul_le_mul_of_nonneg_left (hbound rank level s hy hξ hs hsξ) (by linarith))

end

end Erdos1212Kernel
