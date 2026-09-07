import Erdos1212Kernel.TaoCorputPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1300000

theorem taoCorputPhase_add (x y : Real) : taoCorputPhase (x + y) = taoCorputPhase x * taoCorputPhase y := by
  unfold taoCorputPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem taoCorputPhase_sub_one_norm (u : Real) :
    ‖taoCorputPhase u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
  unfold taoCorputPhase
  rw [mul_comm ((2 * Real.pi * u : Real) : Complex) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * u) / 2 = Real.pi * u by ring, Real.norm_eq_abs, abs_mul]
  norm_num

/-- The source small-increment denominator bound, valid for both signs. -/
theorem taoCorputPhase_chord_lower {u : Real} (hu : |u| ≤ 1 / 2) :
    4 * |u| ≤ ‖taoCorputPhase u - 1‖ := by
  have harg : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]
  have h := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  have he : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by field_simp
  rw [he] at h
  rw [taoCorputPhase_sub_one_norm]
  linarith

theorem taoCorputPhase_denominator_bound {δ u : Real} (hδ : 0 < δ) (hlow : δ ≤ |u|) (hhigh : |u| ≤ 1 / 2) :
    δ ≤ ‖taoCorputPhase u - 1‖ := by
  have h := taoCorputPhase_chord_lower hhigh
  linarith

theorem taoCorputPhase_denominator_ne_zero {δ u : Real} (hδ : 0 < δ) (hlow : δ ≤ |u|) (hhigh : |u| ≤ 1 / 2) :
    taoCorputPhase u - 1 ≠ 0 := by
  exact norm_pos_iff.mp (hδ.trans_le (taoCorputPhase_denominator_bound hδ hlow hhigh))

def taoCorputInversePhase (u : Real) : Complex := (taoCorputPhase u - 1)⁻¹

theorem taoCorputInversePhase_norm_bound {δ u : Real} (hδ : 0 < δ) (hlow : δ ≤ |u|) (hhigh : |u| ≤ 1 / 2) :
    ‖taoCorputInversePhase u‖ ≤ 1 / δ := by
  unfold taoCorputInversePhase
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le hδ (taoCorputPhase_denominator_bound hδ hlow hhigh)

end

end Erdos1212Kernel
