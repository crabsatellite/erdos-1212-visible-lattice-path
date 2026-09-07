import Erdos1212Kernel.IwaniecSurvivalLayer

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Split the last finite-depth cut into successful and failed last
selections. Earlier failures do not reach this layer. -/
theorem iwaniecCubicTerminalMass_eq_survival_add_failure {α : Type*} (r : Nat)
    (restriction : List α → α → Bool) (w : α → Real) (selected tail : List α) (k : Nat)
    (hdepth : selected.length + k + 1 = 2 * r) :
    iwaniecCubicTerminalMass r restriction w selected tail =
      iwaniecSurvivalLayer restriction w selected tail (k + 1) +
        iwaniecThresholdLayer restriction w selected tail (k + 1) := by
  induction tail generalizing selected k with
  | nil => simp [iwaniecCubicTerminalMass]
  | cons p tail ih =>
      cases k with
      | zero =>
          have hterminal : 2 * r ≤ selected.length + 1 := by omega
          have hnot : ¬(selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)) := by omega
          rw [iwaniecCubicTerminalMass, dif_neg hnot, if_pos hterminal,
            iwaniecSurvivalLayer, iwaniecThresholdLayer, ih selected 0 hdepth]
          by_cases hc : Even selected.length ∨ restriction selected p
          · simp only [if_pos hc, iwaniecSurvivalLayer_zero, iwaniecThresholdLayer_zero, mul_zero]
            ring
          · simp only [if_neg hc, if_true]
            ring
      | succ k =>
          have hroom : selected.length + 1 < 2 * r := by omega
          have hchild : (selected ++ [p]).length + k + 1 = 2 * r := by
            simp only [List.length_append, List.length_singleton]
            omega
          by_cases hc : Even selected.length ∨ restriction selected p
          · rw [iwaniecCubicTerminalMass, dif_pos ⟨hroom, hc⟩,
              iwaniecSurvivalLayer, iwaniecThresholdLayer]
            simp only [if_pos hc]
            rw [ih selected (k + 1) hdepth, ih (selected ++ [p]) k hchild]
            ring
          · have hnot : ¬(selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)) :=
              fun hh => hc hh.2
            have hk0 : k + 1 ≠ 0 := by omega
            rw [iwaniecCubicTerminalMass, dif_neg hnot, if_neg (by omega : ¬2 * r ≤ selected.length + 1),
              iwaniecSurvivalLayer, iwaniecThresholdLayer]
            simp only [if_neg hc, if_neg hk0, add_zero]
            exact ih selected (k + 1) hdepth

theorem iwaniecCubicTerminalMass_root_eq_layers {α : Type*} {r : Nat} (hr : 0 < r)
    (restriction : List α → α → Bool) (w : α → Real) (tail : List α) :
    iwaniecCubicTerminalMass r restriction w [] tail =
      iwaniecSurvivalLayer restriction w [] tail (2 * r) +
        iwaniecThresholdLayer restriction w [] tail (2 * r) := by
  have hk : 2 * r - 1 + 1 = 2 * r := by omega
  have hh := iwaniecCubicTerminalMass_eq_survival_add_failure r restriction w [] tail (2 * r - 1)
    (by simp only [List.length_nil, zero_add]; omega)
  simpa only [hk] using hh

end

end Erdos1212Kernel
