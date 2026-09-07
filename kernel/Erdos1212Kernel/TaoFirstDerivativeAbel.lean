import Erdos1212Kernel.TaoPhaseChordBounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

/-- The source finite summation-by-parts identity, with both endpoint
coefficients and every interior difference retained. -/
theorem taoFirstDerivative_abel_identity (z w : Nat → Complex) (m : Nat) :
    (∑ n ∈ Finset.range (m + 1), (z (n + 1) - z n) * w n) =
      z (m + 1) * w m - z 0 * w 0 +
      ∑ n ∈ Finset.range m, z (n + 1) * (w n - w (n + 1)) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

theorem taoFirstDerivative_abel_norm_bound (z w : Nat → Complex) (m : Nat) {W V : Real}
    (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hz : ∀ n ≤ m + 1, ‖z n‖ ≤ 1)
    (hw : ∀ n ≤ m, ‖w n‖ ≤ W)
    (hvar : ∀ n < m, ‖w (n + 1) - w n‖ ≤ V) :
    ‖∑ n ∈ Finset.range (m + 1), (z (n + 1) - z n) * w n‖ ≤ 2 * W + (m : Real) * V := by
  have hleft : ‖z (m + 1) * w m‖ ≤ W := by
    rw [Complex.norm_mul]
    exact (mul_le_mul (hz (m + 1) le_rfl) (hw m le_rfl) (norm_nonneg _) (by norm_num)).trans_eq (one_mul W)
  have hright : ‖z 0 * w 0‖ ≤ W := by
    rw [Complex.norm_mul]
    exact (mul_le_mul (hz 0 (by omega)) (hw 0 (by omega)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul W)
  have hmiddle : ‖∑ n ∈ Finset.range m, z (n + 1) * (w n - w (n + 1))‖ ≤ (m : Real) * V := by
    calc
      _ ≤ ∑ n ∈ Finset.range m, ‖z (n + 1) * (w n - w (n + 1))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range m, V := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [Complex.norm_mul, norm_sub_rev]
        exact (mul_le_mul (hz (n + 1) (by omega)) (hvar n hn') (norm_nonneg _) (by norm_num)).trans_eq (one_mul V)
      _ = _ := by simp [nsmul_eq_mul]
  rw [taoFirstDerivative_abel_identity]
  have h := (norm_add_le (z (m + 1) * w m - z 0 * w 0)
    (∑ n ∈ Finset.range m, z (n + 1) * (w n - w (n + 1))))
  have hsub := norm_sub_le (z (m + 1) * w m) (z 0 * w 0)
  linarith

theorem taoFirstDerivative_phase_identity (u v : Real) (hne : taoCorputPhase (v - u) - 1 ≠ 0) :
    taoCorputPhase u = (taoCorputPhase v - taoCorputPhase u) * taoCorputInversePhase (v - u) := by
  have hphase : taoCorputPhase v = taoCorputPhase u * taoCorputPhase (v - u) := by
    rw [← taoCorputPhase_add, show u + (v - u) = v by ring]
  rw [hphase]
  unfold taoCorputInversePhase
  have hmul := mul_inv_cancel₀ hne
  calc
    _ = taoCorputPhase u * 1 := by ring
    _ = taoCorputPhase u * ((taoCorputPhase (v - u) - 1) * (taoCorputPhase (v - u) - 1)⁻¹) := by rw [hmul]
    _ = _ := by ring

end

end Erdos1212Kernel
