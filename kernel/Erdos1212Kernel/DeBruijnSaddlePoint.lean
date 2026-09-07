import Erdos1212Kernel.DeBruijnSaddleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnSaddle_exists_unique {u : Real} (hu : 1 < u) :
    ∃! x : Real, 0 < x ∧ Real.exp x - 1 = u * x := by
  have hlow : deBruijnSaddleAverage 0 ≤ u := by rw [deBruijnSaddleAverage_zero]; exact hu.le
  have hhigh : u ≤ deBruijnSaddleAverage (2 * u) := by
    have h := deBruijnSaddleAverage_lower (2 * u)
    linarith
  obtain ⟨x, hx, hAx⟩ := intermediate_value_Icc (by linarith : (0 : Real) ≤ 2 * u)
    deBruijnSaddleAverage_continuous.continuousOn ⟨hlow, hhigh⟩
  have hxPos : 0 < x := by
    by_contra hnot
    have hx0 : x = 0 := le_antisymm (le_of_not_gt hnot) hx.1
    rw [hx0, deBruijnSaddleAverage_zero] at hAx
    linarith
  have hroot : Real.exp x - 1 = u * x := by
    rw [← deBruijnSaddleAverage_mul, hAx]
    ring
  refine ⟨x, ⟨hxPos, hroot⟩, ?_⟩
  intro y hy
  have hyA : deBruijnSaddleAverage y = u := by
    rw [deBruijnSaddleAverage_eq_quot hy.1.ne', hy.2, mul_div_cancel_right₀ _ hy.1.ne']
  exact deBruijnSaddleAverage_strictMono.injective (hyA.trans hAx.symm)

/-- The positive root in the source. Its harmless totalization outside
u>1 is never used as a saddle in any theorem below. -/
def deBruijnSaddle (u : Real) : Real :=
  if hu : 1 < u then Classical.choose (deBruijnSaddle_exists_unique hu) else 0

theorem deBruijnSaddle_spec {u : Real} (hu : 1 < u) :
    0 < deBruijnSaddle u ∧ Real.exp (deBruijnSaddle u) - 1 = u * deBruijnSaddle u := by
  unfold deBruijnSaddle
  rw [dif_pos hu]
  exact (Classical.choose_spec (deBruijnSaddle_exists_unique hu)).1

theorem deBruijnSaddle_pos {u : Real} (hu : 1 < u) : 0 < deBruijnSaddle u := (deBruijnSaddle_spec hu).1

theorem deBruijnSaddle_equation {u : Real} (hu : 1 < u) :
    Real.exp (deBruijnSaddle u) - 1 = u * deBruijnSaddle u := (deBruijnSaddle_spec hu).2

theorem deBruijnSaddle_average {u : Real} (hu : 1 < u) : deBruijnSaddleAverage (deBruijnSaddle u) = u := by
  rw [deBruijnSaddleAverage_eq_quot (deBruijnSaddle_pos hu).ne', deBruijnSaddle_equation hu,
    mul_div_cancel_right₀ _ (deBruijnSaddle_pos hu).ne']

theorem deBruijnSaddle_unique {u x : Real} (hu : 1 < u) (hx : 0 < x) (hroot : Real.exp x - 1 = u * x) :
    x = deBruijnSaddle u := by
  unfold deBruijnSaddle
  rw [dif_pos hu]
  exact (Classical.choose_spec (deBruijnSaddle_exists_unique hu)).2 x ⟨hx, hroot⟩

theorem deBruijnSaddle_strictMonoOn : StrictMonoOn deBruijnSaddle (Set.Ioi (1 : Real)) := by
  intro u hu v hv huv
  apply deBruijnSaddleAverage_strictMono.lt_iff_lt.mp
  rw [deBruijnSaddle_average hu, deBruijnSaddle_average hv]
  exact huv

theorem deBruijnSaddle_log_lower {u : Real} (hu : 1 < u) : Real.log u < deBruijnSaddle u := by
  apply (Real.log_lt_iff_lt_exp (by linarith : 0 < u)).mpr
  calc
    u = deBruijnSaddleAverage (deBruijnSaddle u) := (deBruijnSaddle_average hu).symm
    _ < _ := deBruijnSaddleAverage_lt_exp (deBruijnSaddle_pos hu)

theorem tendsto_deBruijnSaddle : Tendsto deBruijnSaddle atTop atTop := by
  apply tendsto_atTop_mono' atTop _ Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact (deBruijnSaddle_log_lower hu).le

end

end Erdos1212Kernel
