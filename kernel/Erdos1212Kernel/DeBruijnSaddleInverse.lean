import Erdos1212Kernel.DeBruijnSaddlePoint

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

theorem deBruijnSaddle_eq_zero {u : Real} (hu : u ≤ 1) : deBruijnSaddle u = 0 := by
  unfold deBruijnSaddle
  rw [dif_neg (not_lt.mpr hu)]

theorem deBruijnSaddle_nonneg (u : Real) : 0 ≤ deBruijnSaddle u := by
  by_cases hu : 1 < u
  · exact (deBruijnSaddle_pos hu).le
  · rw [deBruijnSaddle_eq_zero (le_of_not_gt hu)]

theorem deBruijnSaddle_average_of_ge {u : Real} (hu : 1 ≤ u) : deBruijnSaddleAverage (deBruijnSaddle u) = u := by
  rcases hu.eq_or_lt with rfl | hu
  · rw [deBruijnSaddle_eq_zero le_rfl, deBruijnSaddleAverage_zero]
  · exact deBruijnSaddle_average hu

/-- The exact inverse substitution in (1.7), including its endpoint s=0. -/
theorem deBruijnSaddle_average_inverse {x : Real} (hx : 0 ≤ x) :
    deBruijnSaddle (deBruijnSaddleAverage x) = x := by
  have hA : 1 ≤ deBruijnSaddleAverage x := by
    simpa only [deBruijnSaddleAverage_zero] using deBruijnSaddleAverage_strictMono.monotone hx
  exact deBruijnSaddleAverage_strictMono.injective (deBruijnSaddle_average_of_ge hA)

theorem deBruijnSaddle_monotone : Monotone deBruijnSaddle := by
  intro u v huv
  by_cases hu : 1 < u
  · exact deBruijnSaddle_strictMonoOn.monotoneOn hu (hu.trans_le huv) huv
  · rw [deBruijnSaddle_eq_zero (le_of_not_gt hu)]
    exact deBruijnSaddle_nonneg v

theorem deBruijnSaddle_intervalIntegrable (a b : Real) : IntervalIntegrable deBruijnSaddle volume a b :=
  deBruijnSaddle_monotone.intervalIntegrable

end

end Erdos1212Kernel
