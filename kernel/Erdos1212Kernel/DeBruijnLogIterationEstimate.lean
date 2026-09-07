import Erdos1212Kernel.DeBruijnSaddleLogIdentity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- Quantitative error accounting for the source iteration
x=L+l+log(1+(x-L)/L)+delta. -/
theorem deBruijn_log_iteration_estimate {L l x δ : Real} (hL : 4 ≤ L) (hl : 1 ≤ l)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / L ^ 2)
    (hx0 : 0 ≤ x - L) (hx : x - L ≤ l + 2)
    (hid : x = L + l + Real.log (1 + (x - L) / L) + δ) :
    |x - (L + l + l / L)| ≤ 10 * l ^ 2 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hl0 : 0 ≤ l := by linarith
  let t := (x - L) / L
  let b := x - L - l
  have ht0 : 0 ≤ t := div_nonneg hx0 hL0.le
  have ht : t ≤ 3 * l / L := by
    apply div_le_div_of_nonneg_right _ hL0.le
    linarith
  have hTaylor := deBruijn_log_one_add_error ht0
  have hbEq : b = Real.log (1 + t) + δ := by dsimp [b, t]; linarith
  have hb0 : 0 ≤ b := by rw [hbEq]; exact add_nonneg (Real.log_nonneg (by linarith)) hδ0
  have hb : b ≤ 3 * l / L + 1 / L ^ 2 := by
    rw [hbEq]
    linarith [hTaylor.1]
  have hbDiv : b / L ≤ 4 * l ^ 2 / L ^ 2 := by
    have hi : 1 / L ^ 3 ≤ 1 / L ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hL0)
      nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ L - 1 by linarith)]
    calc
      _ ≤ (3 * l / L + 1 / L ^ 2) / L := div_le_div_of_nonneg_right hb hL0.le
      _ = 3 * l / L ^ 2 + 1 / L ^ 3 := by field_simp
      _ ≤ 3 * l / L ^ 2 + 1 / L ^ 2 := add_le_add le_rfl hi
      _ = (3 * l + 1) / L ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg L)
  have htSq : t ^ 2 ≤ 9 * l ^ 2 / L ^ 2 := by
    calc
      _ ≤ (3 * l / L) ^ 2 := pow_le_pow_left₀ ht0 ht 2
      _ = _ := by ring
  have hδScale : δ ≤ l ^ 2 / L ^ 2 := by
    apply hδ.trans
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg L)
  have hscale : 0 ≤ l ^ 2 / L ^ 2 := div_nonneg (sq_nonneg l) (sq_nonneg L)
  have herr : x - (L + l + l / L) = b / L + (Real.log (1 + t) - t) + δ := by
    have hbt : b - l / L = b / L + (b - t) := by dsimp [b, t]; field_simp; ring
    calc
      _ = b - l / L := by dsimp [b]; ring
      _ = b / L + (b - t) := hbt
      _ = _ := by rw [hbEq]; ring
  rw [herr]
  simp only [mul_div_assoc] at hbDiv htSq ⊢
  apply abs_le.mpr
  constructor
  · have hbD0 : 0 ≤ b / L := div_nonneg hb0 hL0.le
    linarith only [hTaylor.2, htSq, hbD0, hδ0, hscale]
  · linarith only [hTaylor.1, hbDiv, hδScale, hscale]

end

end Erdos1212Kernel
