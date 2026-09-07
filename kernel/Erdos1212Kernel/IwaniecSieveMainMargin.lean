import Erdos1212Kernel.IwaniecBuchstabInvariant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecNormalizedLowerMain (s : Real) : Real :=
  1 - iwaniecEvenSieveSeries s / s

theorem iwaniecNormalizedLowerMain_explicit
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecNormalizedLowerMain s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [iwaniecNormalizedLowerMain, iwaniecEvenSieveSeries_explicit hlower hupper]
  field_simp [show s ≠ 0 by linarith]
  ring

theorem iwaniecNormalizedLowerMain_pos
    {s : Real} (hlower : 2 < s) (hupper : s ≤ 4) :
    0 < iwaniecNormalizedLowerMain s := by
  rw [iwaniecNormalizedLowerMain_explicit hlower.le hupper]
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (Real.log_pos (by linarith : 1 < s - 1)))
    (by linarith)

/-- The explicit quantitative margin at the moving sieve limit used in
Iwaniec 1971, Theorem 2.  It is deliberately stated without an asymptotic
wrapper so the later finite-prime error must fit into a real positive gap. -/
theorem iwaniecNormalizedLowerMain_two_add_margin
    {δ : Real} (hδ : 0 ≤ δ) (hδOne : δ ≤ 1) :
    δ / 3 ≤ iwaniecNormalizedLowerMain (2 + δ) := by
  have hsLower : (2 : Real) ≤ 2 + δ := by linarith
  have hsUpper : (2 : Real) + δ ≤ 4 := by linarith
  rw [iwaniecNormalizedLowerMain_explicit hsLower hsUpper]
  have hlog := Real.le_log_one_add_of_nonneg hδ
  have hgamma : 1 ≤ Real.exp Real.eulerMascheroniConstant := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have hdenPos : 0 < 2 + δ := by linarith
  have hauxPos : 0 < δ + 2 := by linarith
  have hscaled :
      4 * δ / (δ + 2) ≤
        2 * Real.exp Real.eulerMascheroniConstant * Real.log (1 + δ) := by
    have htwoExp : (2 : Real) ≤ 2 * Real.exp Real.eulerMascheroniConstant := by
      nlinarith
    have hlogNonneg : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
    calc
      4 * δ / (δ + 2) = 2 * (2 * δ / (δ + 2)) := by ring
      _ ≤ 2 * Real.log (1 + δ) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ ≤ 2 * Real.exp Real.eulerMascheroniConstant * Real.log (1 + δ) := by
        nlinarith
  have hdenBound : (2 + δ) * (δ + 2) ≤ 9 := by nlinarith
  have hleft : δ / 3 ≤ (4 * δ / (δ + 2)) / (2 + δ) := by
    by_cases hδZero : δ = 0
    · simp [hδZero]
    · have hδPos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδZero)
      rw [div_div]
      apply (div_le_div_iff₀ (by norm_num : (0 : Real) < 3)
        (mul_pos hauxPos hdenPos)).2
      field_simp [hauxPos.ne', hdenPos.ne']
      nlinarith
  calc
    δ / 3 ≤ (4 * δ / (δ + 2)) / (2 + δ) := hleft
    _ ≤ (2 * Real.exp Real.eulerMascheroniConstant * Real.log (1 + δ)) /
        (2 + δ) := div_le_div_of_nonneg_right hscaled hdenPos.le
    _ = 2 * Real.exp Real.eulerMascheroniConstant *
        Real.log ((2 + δ) - 1) / (2 + δ) := by ring_nf

end

end Erdos1212Kernel
