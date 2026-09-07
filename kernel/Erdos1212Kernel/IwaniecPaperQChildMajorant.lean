import Erdos1212Kernel.IwaniecPaperQBoundedLevel
import Erdos1212Kernel.IwaniecPaperAChildDomain

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 600000

def iwaniecPaperQChildMainTerm (rank : Nat) (level : Real) (p : Nat) : Real :=
  iwaniecParitySieveProfile rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
    Real.log (level / (p : Real)) / (p : Real)

def iwaniecPaperQChildErrorTerm (rank : Nat) (level : Real) (p : Nat) : Real :=
  (iwaniecAuxWeightPower (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) *
    iwaniecAuxG rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
      Real.log (level / (p : Real)) ^ 2) / (p : Real)

/-- Exact child normalization for Q. There is no support count, y factor,
or replacement of the reciprocal-prime weight in this inequality. -/
theorem iwaniecPaperQChild_error_le_source (rank : Nat) {level : Real}
    (hy : 1 < level) {p : Nat} (hp : p.Prime)
    (ht : iwaniecCorollaryThreeDomainStart rank ≤ Real.log level / Real.log (p : Real)) :
    iwaniecPaperQChildErrorTerm rank level p ≤
      iwaniecCorollaryThreePrimeWeight rank level p / (p : Real) := by
  unfold iwaniecPaperQChildErrorTerm
  rw [iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hp]
  have ht2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans ht
  have hW := iwaniecPaperChild_weight_le_source_base hy hp ht2
  have harg : iwaniecAuxGStart rank ≤ Real.log level / Real.log (p : Real) - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at ht
    linarith only [ht]
  have hG := (iwaniecAuxG_pos_exactDomain rank harg).le
  have hh := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hW hG)
      (sq_nonneg (Real.log (level / (p : Real))))) (Nat.cast_nonneg p : (0 : Real) ≤ p)
  convert hh using 1 <;> unfold iwaniecCorollaryThreePrimeWeight <;> ring

theorem iwaniecPaperQBand_child_error_sum_le (rank : Nat) {level s R : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    (∑ p ∈ iwaniecStrictPrimeBand R (Real.exp (Real.log level / s)),
      iwaniecPaperQChildErrorTerm rank level p) ≤
    ∑ p ∈ iwaniecStrictPrimeBand R (Real.exp (Real.log level / s)),
      iwaniecCorollaryThreePrimeWeight rank level p / (p : Real) := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1).1
  exact iwaniecPaperQChild_error_le_source rank hy hprime
    (hs.trans (iwaniecPaperBand_child_parameter_lower hy (by linarith) hp))

theorem exists_iwaniecPaperQBand_child_error_bound :
    ∃ K : Real, 0 < K ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperQChildErrorTerm rank level p) ≤
      (iwaniecAuxWeightPower level (max iwaniecAuxSZero s) * iwaniecAuxG (rank + 1) s /
        Real.log level ^ 2) *
        (1 + 100 * K * iwaniecPaperXi level ^ 2 *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level))) := by
  obtain ⟨K, hK, hsource⟩ := exists_iwaniecCorollaryThree_strict_band_constant
  refine ⟨K, hK, ?_⟩
  intro rank level s hy hξ hs hsξ
  exact (iwaniecPaperQBand_child_error_sum_le rank hy hs).trans
    (hsource rank level s hy hξ hs hsξ)

/-- Consume the rank-n Q induction hypothesis on the literal child
levels and xi(child) domains, with main and error masses kept separate. -/
theorem iwaniecPaperQ_child_sum_le (rank : Nat) {C level s : Real}
    (hy : 1 < level) (hξ : iwaniecAuxSZero ≤ iwaniecPaperXi level)
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s)
    (hIH : ∀ y t : Real, 1 < y → iwaniecAuxGStart rank ≤ t → t ≤ iwaniecPaperXi y →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank y t <
        iwaniecPaperQMajorant C rank y t) :
    Real.exp Real.eulerMascheroniConstant *
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperQ rank (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) ≤
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperQChildMainTerm rank level p) +
      (C * ((rank : Real) / ((rank : Real) + 1))) *
        ∑ p ∈ iwaniecStrictPrimeBand
          (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
          iwaniecPaperQChildErrorTerm rank level p := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1).1
  obtain ⟨hchild, hstart, hxi⟩ := iwaniecPaperBand_child_domain rank hy hξ hs hp
  have hh := div_le_div_of_nonneg_right
    (hIH (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real))
      hchild hstart hxi).le (Nat.cast_nonneg p : (0 : Real) ≤ p)
  rw [← iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hprime]
  dsimp only [iwaniecPaperQMajorant, iwaniecPaperQChildMainTerm, iwaniecPaperQChildErrorTerm] at hh ⊢
  convert hh using 1 <;> ring

end

end Erdos1212Kernel
