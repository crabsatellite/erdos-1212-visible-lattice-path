import Erdos1212Kernel.IwaniecPaperQChildMajorant

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecStrictPrimePool_real_sum_split (weight : Nat → Real)
    {lower upper : Real} (h : lower ≤ upper) :
    (∑ p ∈ iwaniecStrictPrimePool upper, weight p) =
      (∑ p ∈ iwaniecStrictPrimePool lower, weight p) +
        ∑ p ∈ iwaniecStrictPrimeBand lower upper, weight p := by
  have hsum := Finset.sum_sdiff (f := weight) (iwaniecStrictPrimePool_mono h)
  rw [iwaniecStrictPrimePool_sdiff_eq_band] at hsum
  linarith only [hsum]

theorem iwaniecPaperQ_successor_recursion (n : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart n ≤ s) :
    iwaniecPaperQ (n + 1) level s =
      (∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperQ n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) +
      if Even (n + 1) then iwaniecPaperD2 level s else 0 := by
  by_cases hn : Even n
  · obtain ⟨k, hk⟩ := hn
    have heq : n = 2 * k := by omega
    clear hk
    subst n
    have he : Even (2 * k) := ⟨k, by omega⟩
    have hs3 : 3 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, he] at hs
      exact hs
    simpa only [Nat.even_add_one, he, not_true_eq_false, if_false, add_zero] using
      iwaniecPaperQ_odd_recursion_unbanded k hy hs3
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
    have heq : n = 2 * k + 1 := by omega
    clear hk
    subst n
    have ho : ¬Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
    have he : Even (2 * k + 2) := ⟨k + 1, by omega⟩
    have hs2 : 2 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, ho] at hs
      exact hs
    simpa only [Nat.add_assoc, show (1 : Nat) + 1 = 2 by rfl, he, if_true] using
      iwaniecPaperQ_even_recursion_unbanded k hy hs2

/-- Exact band splitting before any support vanishing is applied. Both
endpoint d2 contributions remain explicit. -/
theorem iwaniecPaperQ_band_recursion_with_corrections (n : Nat) {level s T : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart n ≤ s) (hsT : s ≤ T) :
    iwaniecPaperQ (n + 1) level s = iwaniecPaperQ (n + 1) level T +
      (∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / T)) (Real.exp (Real.log level / s)),
        iwaniecPaperQ n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) +
      (if Even (n + 1) then iwaniecPaperD2 level s else 0) -
      (if Even (n + 1) then iwaniecPaperD2 level T else 0) := by
  have hleft := iwaniecPaperQ_successor_recursion n hy hs
  have hright := iwaniecPaperQ_successor_recursion n hy (hs.trans hsT)
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds n).1.trans hs
  have hsplit := iwaniecStrictPrimePool_real_sum_split
    (fun p => iwaniecPaperQ n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real))
    (iwaniecPaperCutoff_antitone hy (by linarith) hsT)
  linarith only [hleft, hright, hsplit]

/-- The source's middle-rank band identity. The far d2 term is removed
only after its quartic support has been proved empty. -/
theorem iwaniecPaperQ_successor_band_recursion (n : Nat) {level s T : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart n ≤ s)
    (hsT : s ≤ T) (hT : 4 ≤ T) :
    iwaniecPaperQ (n + 1) level s = iwaniecPaperQ (n + 1) level T +
      (∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / T)) (Real.exp (Real.log level / s)),
        iwaniecPaperQ n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) +
      if Even (n + 1) then iwaniecPaperD2 level s else 0 := by
  rw [iwaniecPaperQ_band_recursion_with_corrections n hy hs hsT,
    iwaniecPaperD2_eq_zero_of_four_le hy hT, ite_self, sub_zero]

/-- The source's extension from the recursion domain to 1<=s<=3 for
odd parent rank, keeping Q, G, and the full profile synchronized. -/
theorem iwaniecPaperQ_recursion_parameter (n : Nat) {level s : Real}
    (hs : iwaniecAuxGStart (n + 1) ≤ s) :
    iwaniecPaperQ (n + 1) level s =
        iwaniecPaperQ (n + 1) level (max (iwaniecCorollaryThreeDomainStart n) s) ∧
      iwaniecAuxG (n + 1) (max (iwaniecCorollaryThreeDomainStart n) s) = iwaniecAuxG (n + 1) s ∧
      iwaniecParitySieveProfile (n + 1) (max (iwaniecCorollaryThreeDomainStart n) s) =
        iwaniecParitySieveProfile (n + 1) s := by
  by_cases hn : Even n
  · have hn1 : ¬Even (n + 1) := by simp only [Nat.even_add_one, not_not]; exact hn
    have hstart : iwaniecCorollaryThreeDomainStart n = 3 := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hn]
    have hs1 : 1 ≤ s := by simpa [iwaniecAuxGStart, hn1] using hs
    rw [hstart]
    by_cases hs3 : 3 ≤ s
    · rw [max_eq_right hs3]
      exact ⟨rfl, rfl, rfl⟩
    · have hsle : s ≤ 3 := le_of_not_ge hs3
      rw [max_eq_left hsle]
      refine ⟨iwaniecPaperQ_odd_initial hn1 level hs1 hsle, ?_, ?_⟩
      · simp only [iwaniecAuxG, hn1, if_false]
        rw [iwaniecAuxUpper_initial (le_refl 3), iwaniecAuxUpper_initial hsle]
      · simp only [iwaniecParitySieveProfile, hn1, if_false]
        exact (iwaniecOddSieveSeries_eq_three hs1 hsle).symm
  · have hstart : iwaniecCorollaryThreeDomainStart n = 2 := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hn]
    have hs2 : 2 ≤ s := by simpa [iwaniecAuxGStart, Nat.even_add_one, hn] using hs
    rw [hstart, max_eq_right hs2]
    exact ⟨rfl, rfl, rfl⟩

end

end Erdos1212Kernel
