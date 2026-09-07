import Erdos1212Kernel.IwaniecCorollaryThreeBound
import Erdos1212Kernel.IwaniecPaperABandRecursion

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 600000

theorem iwaniecStrictPrimeBand_weighted_le_real (b : Real → Real)
    {B R A : Real} (hB : 2 ≤ B) (hBA : B ≤ A) (hBR : B ≤ R)
    (hb : ∀ x ∈ Set.Icc B A, 0 ≤ b x) :
    (∑ p ∈ iwaniecStrictPrimeBand R A, b p / (p : Real)) ≤
      iwaniecPrimeReciprocalWeightedRealInterval b B A := by
  have hA0 : 0 ≤ A := by linarith
  have hsub : iwaniecStrictPrimeBand R A ⊆
      (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real)) := by
    intro p hp
    obtain ⟨hpA, hpR⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprime, hpA⟩ := mem_iwaniecStrictPrimePool.mp hpA
    exact (iwaniec_real_prime_interval_mem hA0 p).mpr ⟨hprime, hBR.trans hpR, hpA.le⟩
  unfold iwaniecPrimeReciprocalWeightedRealInterval
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _hnot
  have hpdata := (iwaniec_real_prime_interval_mem hA0 p).mp hp
  exact div_nonneg (hb p ⟨hpdata.2.1, hpdata.2.2⟩) (Nat.cast_nonneg p)

/-- The actual strict band in the paper's support-count recursion. The
lower cutoff is xi-1, not xi; its exact inclusion is proved and consumed. -/
theorem exists_iwaniecCorollaryThree_strict_band_constant :
    ∃ C : Real, 0 < C ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1)))
        (Real.exp (Real.log level / s)),
        iwaniecCorollaryThreePrimeWeight rank level p / (p : Real)) ≤
      (iwaniecAuxWeightPower level (max iwaniecAuxSZero s) * iwaniecAuxG (rank + 1) s /
        Real.log level ^ 2) *
        (1 + 100 * C * iwaniecPaperXi level ^ 2 *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level))) := by
  obtain ⟨C, hC, hbound⟩ := exists_iwaniecCorollaryThree_exactDomain_constant
  refine ⟨C, hC, ?_⟩
  intro rank level s hy hξ hs hsξ
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hspos : 0 < s := by linarith
  have hξsub : 0 < iwaniecPaperXi level - 1 := by linarith [iwaniecAuxSZero_large]
  have hL := Real.log_pos hy
  have hBA : Real.exp (Real.log level / iwaniecPaperXi level) ≤ Real.exp (Real.log level / s) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hspos hsξ)
  have hBR : Real.exp (Real.log level / iwaniecPaperXi level) ≤
      Real.exp (Real.log level / (iwaniecPaperXi level - 1)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hξsub (by linarith))
  have hsum := iwaniecStrictPrimeBand_weighted_le_real (iwaniecCorollaryThreePrimeWeight rank level)
    (iwaniecCorollaryThree_left_cutoff_two hy hξ) hBA hBR
    (fun x hx => (iwaniecCorollaryThreePrimeWeight_pos_exactDomain rank hy hs hsξ hx).le)
  exact hsum.trans (hbound rank level s hy hξ hs hsξ)

end

end Erdos1212Kernel
