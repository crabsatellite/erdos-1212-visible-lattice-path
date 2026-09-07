import Erdos1212Kernel.IwaniecPaperARecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

def iwaniecStrictPrimeBand (lower upper : Real) : Finset Nat :=
  (iwaniecStrictPrimePool upper).filter (fun p => lower ≤ (p : Real))

theorem iwaniecStrictPrimePool_mono {lower upper : Real} (h : lower ≤ upper) :
    iwaniecStrictPrimePool lower ⊆ iwaniecStrictPrimePool upper := by
  intro p hp
  obtain ⟨hprime, hlt⟩ := mem_iwaniecStrictPrimePool.mp hp
  exact mem_iwaniecStrictPrimePool.mpr ⟨hprime, hlt.trans_le h⟩

theorem iwaniecStrictPrimePool_sdiff_eq_band (lower upper : Real) :
    iwaniecStrictPrimePool upper \ iwaniecStrictPrimePool lower =
      iwaniecStrictPrimeBand lower upper := by
  ext p
  simp only [Finset.mem_sdiff, mem_iwaniecStrictPrimePool,
    iwaniecStrictPrimeBand, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hprime, hupper⟩, hnot⟩
    refine ⟨⟨hprime, hupper⟩, ?_⟩
    by_contra h
    exact hnot ⟨hprime, lt_of_not_ge h⟩
  · rintro ⟨⟨hprime, hupper⟩, hlower⟩
    exact ⟨⟨hprime, hupper⟩, fun h => (not_lt.mpr hlower) h.2⟩

theorem iwaniecStrictPrimePool_sum_split
    (weight : Nat → Nat) {lower upper : Real} (h : lower ≤ upper) :
    (∑ p ∈ iwaniecStrictPrimePool upper, weight p) =
      (∑ p ∈ iwaniecStrictPrimePool lower, weight p) +
        ∑ p ∈ iwaniecStrictPrimeBand lower upper, weight p := by
  have hsum := Finset.sum_sdiff (f := weight) (iwaniecStrictPrimePool_mono h)
  rw [iwaniecStrictPrimePool_sdiff_eq_band] at hsum
  omega

theorem iwaniecPaperCutoff_antitone
    {level s S : Real} (hlevel : 1 < level) (hs : 0 < s) (hsS : s ≤ S) :
    Real.exp (Real.log level / S) ≤ Real.exp (Real.log level / s) := by
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (Real.log_pos hlevel).le hs hsS

/-- Exact finite band recursion used at the start of the proof of Theorem 5.
The empty tuple appears in both cutoffs, so it cancels identically here. -/
theorem iwaniecPaperA_odd_band_recursion
    (r : Nat) {level s S : Real}
    (hlevel : 1 < level) (hs : 2 ≤ s) (hsS : s ≤ S) :
    iwaniecPaperA (2 * r + 1) level s =
      iwaniecPaperA (2 * r + 1) level S +
        ∑ p ∈ iwaniecStrictPrimeBand
          (Real.exp (Real.log level / S)) (Real.exp (Real.log level / s)),
          iwaniecPaperA (2 * r) (level / p) (Real.log level / Real.log p - 1) := by
  have hleft := iwaniecPaperA_odd_recursion r hlevel hs
  have hright := iwaniecPaperA_odd_recursion r hlevel (hs.trans hsS)
  have hsplit := iwaniecStrictPrimePool_sum_split
    (fun p => iwaniecPaperA (2 * r) (level / p) (Real.log level / Real.log p - 1))
    (iwaniecPaperCutoff_antitone hlevel (by linarith) hsS)
  dsimp only at hsplit
  omega

theorem iwaniecPaperA_even_band_recursion
    (r : Nat) {level s S : Real}
    (hlevel : 1 < level) (hs : 3 ≤ s) (hsS : s ≤ S) :
    iwaniecPaperA (2 * r + 2) level s =
      iwaniecPaperA (2 * r + 2) level S +
        ∑ p ∈ iwaniecStrictPrimeBand
          (Real.exp (Real.log level / S)) (Real.exp (Real.log level / s)),
          iwaniecPaperA (2 * r + 1) (level / p) (Real.log level / Real.log p - 1) := by
  have hleft := iwaniecPaperA_even_recursion_with_unit r hlevel hs
  have hright := iwaniecPaperA_even_recursion_with_unit r hlevel (hs.trans hsS)
  have hsplit := iwaniecStrictPrimePool_sum_split
    (fun p => iwaniecPaperA (2 * r + 1) (level / p) (Real.log level / Real.log p - 1))
    (iwaniecPaperCutoff_antitone hlevel (by linarith) hsS)
  dsimp only at hsplit
  omega

end

end Erdos1212Kernel
