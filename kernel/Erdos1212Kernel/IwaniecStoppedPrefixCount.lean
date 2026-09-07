import Erdos1212Kernel.IwaniecStoppedElementaryBound
import Erdos1212Kernel.IwaniecPaperAFactorialSaturation

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Every stop at depth k+1 has a successful length-k prefix. This is
proved on the actual recursive carrier, including the empty-prefix case. -/
theorem iwaniecCubicRealThresholdLayer_zero_of_prefix_count (offset : Nat) (level : Real)
    (factors : List Nat) (k : Nat) (hcount : iwaniecCubicRealCount offset level factors k = 0) :
    iwaniecCubicRealThresholdLayer offset level factors (k + 1) = 0 := by
  induction factors generalizing offset level k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp at hcount
      | succ k =>
          rw [iwaniecCubicRealCount_succ_cons] at hcount
          rw [iwaniecCubicRealThresholdLayer]
          by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
          · rw [if_pos hc] at hcount ⊢
            obtain ⟨hskip, hchild⟩ := Nat.add_eq_zero.mp hcount
            rw [ih offset level (k + 1) hskip, ih (offset + 1) (level / p) k hchild]
            ring
          · rw [if_neg hc] at hcount ⊢
            have hskip : iwaniecCubicRealCount offset level tail (k + 1) = 0 := by simpa using hcount
            rw [ih offset level (k + 1) hskip, if_neg (by omega : k + 1 ≠ 0)]
            ring

theorem iwaniecPaperStoppedLayer_even_zero_of_factorial {level z : Real} (hy : 1 < level)
    (hz : z ≤ level) (k : Nat) (hfactorial : level ≤ ((k + 1).factorial : Real)) :
    iwaniecPaperStoppedLayer 0 level z (k + 1) = 0 := by
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
  have hzCount := iwaniecCubicRealProductCount_eq_zero_of_factorial 0 level factors k
    (iwaniecDescendingFactors_strict _) hmin hfactorial
  rw [iwaniecCubicRealProductCount_eq_of_cutoff level factors k hy hpos (Finset.pairwise_sort _ _) hcutoff] at hzCount
  exact iwaniecCubicRealThresholdLayer_zero_of_prefix_count 0 level factors k hzCount

theorem iwaniecPaperStoppedLayer_odd_zero_of_factorial {level : Real} (hy : 1 < level)
    (z : Real) (k : Nat) (hfactorial : level ≤ ((k + 1).factorial : Real)) :
    iwaniecPaperStoppedLayer 1 level z (k + 1) = 0 := by
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  have hmin : ∀ p ∈ factors, 2 ≤ p := by
    intro p hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by simpa [factors, iwaniecDescendingFactors] using hp
    exact (mem_iwaniecStrictPrimePool.mp hpPool).1.two_le
  have hpos : ∀ p ∈ factors, 0 < p := by intro p hp; have hh := hmin p hp; omega
  have hzCount := iwaniecCubicRealProductCount_eq_zero_of_factorial 1 level factors k
    (iwaniecDescendingFactors_strict _) hmin hfactorial
  rw [iwaniecCubicRealProductCount_eq_cubicFirst level factors k hy hpos (Finset.pairwise_sort _ _)] at hzCount
  exact iwaniecCubicRealThresholdLayer_zero_of_prefix_count 1 level factors k hzCount

end

end Erdos1212Kernel
