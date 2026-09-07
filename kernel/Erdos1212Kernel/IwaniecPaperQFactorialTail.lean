import Erdos1212Kernel.IwaniecStoppedElementaryBound
import Erdos1212Kernel.IwaniecPaperAStirlingTail

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecPaperD_le_factorial_term (rank : Nat) {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) :
    iwaniecPaperD rank level s ≤ iwaniecFactorialTerm (iwaniecStrictPrimeReciprocalSum level) rank := by
  let t := if Even rank then s else max 3 s
  let z := Real.exp (Real.log level / t)
  have ht : 1 ≤ t := by dsimp [t]; split; exact hs; exact hs.trans (le_max_right 3 s)
  have hz : z ≤ level := iwaniecPaperCutoff_le_level hy ht
  have hM := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : Nat => (p : Real)⁻¹)
    (iwaniecStrictPrimePool_mono hz) (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hM0 : 0 ≤ ∑ p ∈ iwaniecStrictPrimePool z, (p : Real)⁻¹ :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hp := pow_le_pow_left₀ hM0 hM rank
  have hd := div_le_div_of_nonneg_right hp (Nat.cast_nonneg rank.factorial : (0 : Real) ≤ rank.factorial)
  have hl := iwaniecPaperStoppedLayer_le_reciprocal_factorial (if Even rank then 0 else 1) level z rank
  exact hl.trans hd

/-- Only ranks beyond the proved support cutoff remain. The upper
bound is the source's finite reciprocal-factorial tail on primes p<y. -/
theorem iwaniecPaperQ_le_factorial_tail (rank K : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) (hK : ((K + 1 : Nat) : Real) ≤ s) :
    iwaniecPaperQ rank level s ≤
      ∑ k ∈ Finset.Ico K (rank + 1), iwaniecFactorialTerm (iwaniecStrictPrimeReciprocalSum level) k := by
  classical
  let f := fun k : Nat => if (Even k ↔ Even rank) then iwaniecPaperD k level s else 0
  have hsub : Finset.Ico K (rank + 1) ⊆ Finset.range (rank + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hsum := Finset.sum_subset (f := f) hsub (by
    intro k hk hknot
    have hupper := Finset.mem_range.mp hk
    have hsmall : k < K := by
      by_contra hn
      exact hknot (Finset.mem_Ico.mpr ⟨by omega, hupper⟩)
    have hkr : (k : Real) + 2 ≤ ((K + 1 : Nat) : Real) := by exact_mod_cast (show k + 2 ≤ K + 1 by omega)
    have hz := iwaniecPaperD_zero_of_parameter k hy (hkr.trans hK)
    simp only [f, hz, ite_self])
  unfold iwaniecPaperQ
  change (∑ k ∈ Finset.range (rank + 1), f k) ≤ _
  rw [← hsum]
  apply Finset.sum_le_sum
  intro k hk
  dsimp only [f]
  split
  · exact iwaniecPaperD_le_factorial_term k hy hs
  · exact iwaniecFactorialTerm_nonneg
      (Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))) k

theorem iwaniecPaperQ_le_twice_factorial (rank K : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) (hK : ((K + 1 : Nat) : Real) ≤ s)
    (hthreshold : 2 * iwaniecStrictPrimeReciprocalSum level ≤ ((K + 1 : Nat) : Real)) :
    iwaniecPaperQ rank level s ≤ 2 * iwaniecFactorialTerm (iwaniecStrictPrimeReciprocalSum level) K := by
  have hM : 0 ≤ iwaniecStrictPrimeReciprocalSum level :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  exact (iwaniecPaperQ_le_factorial_tail rank K hy hs hK).trans
    (iwaniecFactorialTerm_sum_tail_le hM K (rank + 1) hthreshold)

theorem iwaniecPaperQ_le_stirling_tail (rank K : Nat) (hKpos : 0 < K) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) (hK : ((K + 1 : Nat) : Real) ≤ s)
    (hthreshold : 2 * iwaniecStrictPrimeReciprocalSum level ≤ ((K + 1 : Nat) : Real)) :
    iwaniecPaperQ rank level s ≤
      2 * (Real.exp 1 * iwaniecStrictPrimeReciprocalSum level / (K : Real)) ^ K := by
  have hM : 0 ≤ iwaniecStrictPrimeReciprocalSum level :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  exact (iwaniecPaperQ_le_twice_factorial rank K hy hs hK hthreshold).trans
    (mul_le_mul_of_nonneg_left (iwaniecFactorialTerm_le_stirling_power hM K hKpos) (by norm_num))

end

end Erdos1212Kernel
