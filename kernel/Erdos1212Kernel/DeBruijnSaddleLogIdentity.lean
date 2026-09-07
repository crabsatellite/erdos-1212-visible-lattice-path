import Erdos1212Kernel.DeBruijnSaddleInverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem deBruijn_log_one_add_error {t : Real} (ht : 0 ≤ t) :
    0 ≤ t - Real.log (1 + t) ∧ t - Real.log (1 + t) ≤ t ^ 2 := by
  have hupper := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
  have hlower := Real.le_log_one_add_of_nonneg ht
  have hpoly : t - t ^ 2 ≤ 2 * t / (t + 2) := by
    rw [le_div_iff₀ (show 0 < t + 2 by linarith)]
    nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)]
  constructor <;> linarith

theorem deBruijnSaddle_log_fixed_point {u : Real} (hu : 1 < u) :
    deBruijnSaddle u = Real.log (1 + u * deBruijnSaddle u) := by
  have he : Real.exp (deBruijnSaddle u) = 1 + u * deBruijnSaddle u := by linarith [deBruijnSaddle_equation hu]
  rw [← he, Real.log_exp]

def deBruijnSaddleLogCorrection (u : Real) : Real :=
  Real.log (1 + 1 / (u * deBruijnSaddle u))

theorem deBruijnSaddle_log_split {u : Real} (hu : 1 < u) :
    deBruijnSaddle u = Real.log u + Real.log (deBruijnSaddle u) + deBruijnSaddleLogCorrection u := by
  have hu0 : 0 < u := by linarith
  have hξ := deBruijnSaddle_pos hu
  have hp : 0 < u * deBruijnSaddle u := mul_pos hu0 hξ
  have hcor : 0 < 1 + 1 / (u * deBruijnSaddle u) := by positivity
  have hfactor : 1 + u * deBruijnSaddle u = (u * deBruijnSaddle u) * (1 + 1 / (u * deBruijnSaddle u)) := by
    field_simp
    ring
  calc
    _ = Real.log (1 + u * deBruijnSaddle u) := deBruijnSaddle_log_fixed_point hu
    _ = Real.log (u * deBruijnSaddle u) + Real.log (1 + 1 / (u * deBruijnSaddle u)) := by
      rw [hfactor, Real.log_mul hp.ne' hcor.ne']
    _ = _ := by rw [Real.log_mul hu0.ne' hξ.ne']; rfl

theorem deBruijnSaddleLogCorrection_bounds {u : Real} (hu : 1 < u) :
    0 ≤ deBruijnSaddleLogCorrection u ∧ deBruijnSaddleLogCorrection u ≤ 1 / (u * deBruijnSaddle u) := by
  have ht : 0 ≤ 1 / (u * deBruijnSaddle u) := by have hξ := deBruijnSaddle_pos hu; positivity
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have h := (deBruijn_log_one_add_error ht).1
  change Real.log (1 + 1 / (u * deBruijnSaddle u)) ≤ _
  linarith

theorem deBruijnSaddleLogCorrection_le_inverse {u : Real} (hu : 1 < u) (hξ : 1 ≤ deBruijnSaddle u) :
    deBruijnSaddleLogCorrection u ≤ 1 / u := by
  have hu0 : 0 < u := by linarith
  apply (deBruijnSaddleLogCorrection_bounds hu).2.trans
  apply one_div_le_one_div_of_le hu0
  nlinarith

end

end Erdos1212Kernel
