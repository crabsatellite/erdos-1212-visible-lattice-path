import Erdos1212Kernel.DeBruijnF1SaddleNormalized
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

/-- The full displayed main term in de Bruijn 1951 (2.5), retaining
the actual source curvature rather than substituting u. -/
def deBruijnF1SaddleMain (u : Real) : Real :=
  deBruijnSaddleHeight u / (2 * Real.pi) * Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u)

theorem deBruijnF1SaddleMain_pos (u : Real) : 0 < deBruijnF1SaddleMain u := by
  have hH := deBruijnSaddleHeight_pos u
  have hC := deBruijnSaddleCurvature_pos u
  unfold deBruijnF1SaddleMain
  positivity

theorem deBruijnF1SaddleMain_eq (u : Real) :
    deBruijnF1SaddleMain u = deBruijnSaddleHeight u / Real.sqrt (deBruijnSaddleCurvature u) * deBruijnF1GaussianCoefficient := by
  unfold deBruijnF1SaddleMain deBruijnF1GaussianCoefficient
  rw [Real.sqrt_div (show 0 ≤ 2 * Real.pi by positivity) (deBruijnSaddleCurvature u)]
  ring

theorem deBruijnF1_saddle_ratio_eq (u : Real) :
    deBruijnF1 u / deBruijnF1SaddleMain u = deBruijnF1Normalized u / deBruijnF1GaussianCoefficient := by
  rw [deBruijnF1SaddleMain_eq]
  unfold deBruijnF1Normalized
  have hs : 0 < Real.sqrt (deBruijnSaddleCurvature u) := Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)
  field_simp [(deBruijnSaddleHeight_pos u).ne', hs.ne', deBruijnF1GaussianCoefficient_pos.ne']
  <;> ring

theorem tendsto_deBruijnF1_saddle_ratio :
    Tendsto (fun u : Real => deBruijnF1 u / deBruijnF1SaddleMain u) atTop (nhds 1) := by
  have h := tendsto_deBruijnF1Normalized.div_const deBruijnF1GaussianCoefficient
  rw [div_self deBruijnF1GaussianCoefficient_pos.ne'] at h
  apply h.congr'
  filter_upwards with u
  exact (deBruijnF1_saddle_ratio_eq u).symm

theorem deBruijnF1_saddle_asymptotic :
    Asymptotics.IsEquivalent atTop deBruijnF1 deBruijnF1SaddleMain :=
  Asymptotics.isEquivalent_of_tendsto_one tendsto_deBruijnF1_saddle_ratio

/-- Literal real display of (2.5) for the source contour function. -/
theorem deBruijn1951_F1_saddle_formula :
    Tendsto (fun u : Real => deBruijnF1 u /
      (Real.exp (-u * deBruijnSaddle u + deBruijn1951ExpIntegral (deBruijnSaddle u)) / (2 * Real.pi) *
        Real.sqrt (2 * Real.pi / deBruijnSaddleCurvature u))) atTop (nhds 1) :=
  tendsto_deBruijnF1_saddle_ratio

end

end Erdos1212Kernel
