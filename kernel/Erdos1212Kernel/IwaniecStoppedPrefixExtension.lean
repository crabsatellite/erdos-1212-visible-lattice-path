import Erdos1212Kernel.IwaniecStoppedPrefixCount

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecCubicRealCount_successor_zero (offset : Nat) (level : Real) (factors : List Nat) (k : Nat)
    (hcount : iwaniecCubicRealCount offset level factors k = 0) :
    iwaniecCubicRealCount offset level factors (k + 1) = 0 := by
  induction factors generalizing offset level k with
  | nil => simp [iwaniecCubicRealCount]
  | cons p tail ih =>
      cases k with
      | zero => simp at hcount
      | succ k =>
          rw [iwaniecCubicRealCount_succ_cons] at hcount ⊢
          by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
          · rw [if_pos hc] at hcount ⊢
            obtain ⟨hskip, hchild⟩ := Nat.add_eq_zero.mp hcount
            rw [ih offset level (k + 1) hskip, ih (offset + 1) (level / p) k hchild]
          · rw [if_neg hc] at hcount ⊢
            have hskip : iwaniecCubicRealCount offset level tail (k + 1) = 0 := by simpa using hcount
            rw [ih offset level (k + 1) hskip]

/-- The exact shorter prefix used in the source's large-rank argument. -/
theorem iwaniecCubicRealThresholdLayer_zero_after_prefix (offset : Nat) (level : Real)
    (factors : List Nat) (k : Nat) (hcount : iwaniecCubicRealCount offset level factors k = 0) :
    iwaniecCubicRealThresholdLayer offset level factors (k + 2) = 0 :=
  iwaniecCubicRealThresholdLayer_zero_of_prefix_count offset level factors (k + 1)
    (iwaniecCubicRealCount_successor_zero offset level factors k hcount)

theorem iwaniecPaperPrefixCount_zero (offset : Nat) (hoffset : offset = 0 ∨ offset = 1)
    {level z : Real} (hy : 1 < level) (hz : z ≤ level) (k : Nat)
    (hfactorial : level ≤ ((k + 1).factorial : Real)) :
    iwaniecCubicRealCount offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) k = 0 := by
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  have hmin : ∀ p ∈ factors, 2 ≤ p := by
    intro p hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by simpa [factors, iwaniecDescendingFactors] using hp
    exact (mem_iwaniecStrictPrimePool.mp hpPool).1.two_le
  have hpos : ∀ p ∈ factors, 0 < p := by intro p hp; have hh := hmin p hp; omega
  have hcutoff : ∀ p ∈ factors, (p : Real) < level := by
    intro p hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by simpa [factors, iwaniecDescendingFactors] using hp
    exact (mem_iwaniecStrictPrimePool.mp hpPool).2.trans_le hz
  have hzero := iwaniecCubicRealProductCount_eq_zero_of_factorial offset level factors k
    (iwaniecDescendingFactors_strict _) hmin hfactorial
  rcases hoffset with rfl | rfl
  · rw [iwaniecCubicRealProductCount_eq_of_cutoff level factors k hy hpos (Finset.pairwise_sort _ _) hcutoff] at hzero
    exact hzero
  · rw [iwaniecCubicRealProductCount_eq_cubicFirst level factors k hy hpos (Finset.pairwise_sort _ _)] at hzero
    exact hzero

theorem iwaniecPaperD_add_two_zero_of_factorial (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) (hfactorial : level ≤ ((rank + 1).factorial : Real)) :
    iwaniecPaperD (rank + 2) level s = 0 := by
  let offset := if Even (rank + 2) then 0 else 1
  let t := if Even (rank + 2) then s else max 3 s
  have ht : 1 ≤ t := by dsimp [t]; split; exact hs; exact hs.trans (le_max_right 3 s)
  have ho : offset = 0 ∨ offset = 1 := by dsimp [offset]; split <;> simp
  have hz := iwaniecPaperCutoff_le_level hy ht
  have hc := iwaniecPaperPrefixCount_zero offset ho hy hz rank hfactorial
  exact iwaniecCubicRealThresholdLayer_zero_after_prefix offset level _ rank hc

theorem iwaniecPaperQ_add_two_factorial_saturated (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) (hfactorial : level ≤ ((rank + 1).factorial : Real)) :
    iwaniecPaperQ (rank + 2) level s = iwaniecPaperQ rank level s := by
  have hd := iwaniecPaperD_add_two_zero_of_factorial rank hy hs hfactorial
  by_cases he : Even rank
  · obtain ⟨n, hn⟩ := he
    have hr : rank = 2 * n := by omega
    rw [hr] at hd ⊢
    rw [iwaniecPaperQ_even_succ, hd, add_zero]
  · obtain ⟨n, hn⟩ := Nat.not_even_iff_odd.mp he
    have hr : rank = 2 * n + 1 := by omega
    rw [hr] at hd ⊢
    rw [iwaniecPaperQ_odd_succ, hd, add_zero]

end

end Erdos1212Kernel
