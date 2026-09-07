import Erdos1212Kernel.IwaniecPaperQRecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecPaperD_child_sum_eq_band (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) :
    (∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
      iwaniecPaperD rank (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) =
    ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((rank + 3 : Nat) : Real)))
        (Real.exp (Real.log level / s)),
      iwaniecPaperD rank (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  classical
  unfold iwaniecStrictPrimeBand
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : Real.exp (Real.log level / ((rank + 3 : Nat) : Real)) ≤ (p : Real)
  · rw [if_pos hband]
  · rw [if_neg hband]
    have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
    have hchild := (iwaniecStoppedChild_domain hy hs hp).1
    have ht := iwaniecStoppedChild_parameter_below_root rank hy hprime (lt_of_not_ge hband)
    rw [iwaniecPaperD_zero_of_parameter rank hchild ht, zero_div]

theorem iwaniecPaperQ_child_sum_eq_band (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : 1 ≤ s) :
    (∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
      iwaniecPaperQ rank (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) =
    ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((rank + 3 : Nat) : Real)))
        (Real.exp (Real.log level / s)),
      iwaniecPaperQ rank (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  classical
  unfold iwaniecStrictPrimeBand
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : Real.exp (Real.log level / ((rank + 3 : Nat) : Real)) ≤ (p : Real)
  · rw [if_pos hband]
  · rw [if_neg hband]
    have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
    have hchild := (iwaniecStoppedChild_domain hy hs hp).1
    have ht := iwaniecStoppedChild_parameter_below_root rank hy hprime (lt_of_not_ge hband)
    rw [iwaniecPaperQ_zero_of_parameter rank hchild ht, zero_div]

end

end Erdos1212Kernel
