import Erdos1212Kernel.IwaniecStoppedChildBands

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Iwaniec 1971, Lemma 15, odd case with the displayed first-prime
lower root, strict upper endpoint, and exact logarithmic child parameter. -/
theorem iwaniecLemma15_odd (n : Nat) (hn : 1 ≤ n) {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s) :
    iwaniecPaperD (2 * n + 1) level s =
      ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((2 * n + 3 : Nat) : Real)))
          (Real.exp (Real.log level / s)),
        iwaniecPaperD (2 * n) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  rw [iwaniecPaperD_odd_recursion_unbanded n hy hs,
    iwaniecPaperD_child_sum_eq_band (2 * n) hy (show 1 ≤ s by linarith)]

/-- Lemma 15, even case. The hypothesis n>=1 keeps the d2 base separate. -/
theorem iwaniecLemma15_even (n : Nat) (hn : 1 ≤ n) {level s : Real}
    (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperD (2 * n + 2) level s =
      ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((2 * n + 4 : Nat) : Real)))
          (Real.exp (Real.log level / s)),
        iwaniecPaperD (2 * n + 1) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  rw [iwaniecPaperD_even_recursion_unbanded n hn hy hs,
    iwaniecPaperD_child_sum_eq_band (2 * n + 1) hy (show 1 ≤ s by linarith)]

/-- The odd Q corollary on printed page 22. -/
theorem iwaniecPaperQ_odd_recursion (n : Nat) (hn : 1 ≤ n) {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s) :
    iwaniecPaperQ (2 * n + 1) level s =
      ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((2 * n + 3 : Nat) : Real)))
          (Real.exp (Real.log level / s)),
        iwaniecPaperQ (2 * n) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  rw [iwaniecPaperQ_odd_recursion_unbanded n hy hs,
    iwaniecPaperQ_child_sum_eq_band (2 * n) hy (show 1 ≤ s by linarith)]

/-- The even Q corollary, including the literal d2 correction term. -/
theorem iwaniecPaperQ_even_recursion (n : Nat) (hn : 1 ≤ n) {level s : Real}
    (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperQ (2 * n + 2) level s =
      (∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((2 * n + 4 : Nat) : Real)))
          (Real.exp (Real.log level / s)),
        iwaniecPaperQ (2 * n + 1) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) +
      iwaniecPaperD2 level s := by
  rw [iwaniecPaperQ_even_recursion_unbanded n hy hs,
    iwaniecPaperQ_child_sum_eq_band (2 * n + 1) hy (show 1 ≤ s by linarith)]

end

end Erdos1212Kernel
