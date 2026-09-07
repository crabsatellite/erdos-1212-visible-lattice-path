import Erdos1212Kernel.IwaniecStoppedFactorialShift

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 550000

/-- The source large-rank branch, including both vanishing layers.
The shifted factorial estimate keeps the actual shorter prefix indices. -/
theorem eventually_iwaniecPaperQ_large_rank_saturated :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real), 1 ≤ s →
      2 * Real.log level / Real.log (Real.log level) ≤ ((rank + 2 : Nat) : Real) →
      iwaniecPaperQ (rank + 2) level s = iwaniecPaperQ rank level s ∧
        iwaniecPaperD (rank + 2) level s = 0 ∧ iwaniecPaperD rank level s = 0 := by
  filter_upwards [eventually_iwaniecFactorial_shifted_dominates_level] with level hdata
  obtain ⟨hy, hfac⟩ := hdata
  refine ⟨hy, ?_⟩
  intro rank s hs hr
  have hupper : ((rank + 2 : Nat) : Real) ≤ ((rank + 1 + 3 : Nat) : Real) := by
    exact_mod_cast (show rank + 2 ≤ rank + 1 + 3 by omega)
  have hfactorial := hfac (rank + 1) (hr.trans hupper)
  refine ⟨iwaniecPaperQ_add_two_factorial_saturated rank hy hs hfactorial,
    iwaniecPaperD_add_two_zero_of_factorial rank hy hs hfactorial, ?_⟩
  by_cases hr2 : 2 ≤ rank
  · have hindex : rank - 1 + 3 = rank + 2 := by omega
    have hsmallFac := hfac (rank - 1) (by simpa only [hindex] using hr)
    have hprefix : rank - 2 + 1 = rank - 1 := by omega
    have hzero := iwaniecPaperD_add_two_zero_of_factorial (rank - 2) hy hs
      (by simpa only [hprefix] using hsmallFac)
    simpa only [show rank - 2 + 2 = rank by omega] using hzero
  · have hcases : rank = 0 ∨ rank = 1 := by omega
    rcases hcases with rfl | rfl
    · exact iwaniecPaperD_zero level s
    · exact iwaniecPaperD_one hy s

end

end Erdos1212Kernel
