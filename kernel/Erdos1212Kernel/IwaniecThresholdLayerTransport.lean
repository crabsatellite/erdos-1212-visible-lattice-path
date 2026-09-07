import Erdos1212Kernel.IwaniecThresholdPartialMass

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- The canonical threshold mass contains precisely the first-failure
layers strictly before the terminal depth 2r. -/
theorem iwaniecCubicThresholdMass_eq_partialLayers {α : Type*} (r : Nat)
    (restriction : List α → α → Bool) (w : α → Real) (selected tail : List α)
    (hselected : selected.length < 2 * r) :
    iwaniecCubicThresholdMass r restriction w selected tail =
      iwaniecThresholdPartialMass restriction w selected tail (2 * r - selected.length - 1) := by
  induction tail generalizing selected with
  | nil => simp [iwaniecCubicThresholdMass]
  | cons p tail ih =>
      by_cases hroom : selected.length + 1 < 2 * r
      · have hcap : 2 * r - selected.length - 1 = (2 * r - selected.length - 2) + 1 := by omega
        have hchild : (selected ++ [p]).length < 2 * r := by simpa using hroom
        have hchildCap : 2 * r - (selected ++ [p]).length - 1 = 2 * r - selected.length - 2 := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [iwaniecCubicThresholdMass, hcap, iwaniecThresholdPartialMass_cons_succ]
        by_cases hc : Even selected.length ∨ restriction selected p
        · rw [dif_pos ⟨hroom, hc⟩, if_pos hc, ih selected hselected, ih (selected ++ [p]) hchild,
            hcap, hchildCap]
        · have hnot : ¬(selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)) :=
            fun hh => hc hh.2
          rw [dif_neg hnot, if_neg (by omega : ¬2 * r ≤ selected.length + 1), if_neg hc,
            ih selected hselected, hcap]
      · have hterminal : 2 * r ≤ selected.length + 1 := by omega
        have hcap : 2 * r - selected.length - 1 = 0 := by omega
        have hnot : ¬(selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)) :=
          fun hh => hroom hh.1
        rw [iwaniecCubicThresholdMass, dif_neg hnot, if_pos hterminal, ih selected hselected, hcap]
        simp

theorem iwaniecCubicThresholdMass_root_eq_layers {α : Type*} {r : Nat} (hr : 0 < r)
    (restriction : List α → α → Bool) (w : α → Real) (tail : List α) :
    iwaniecCubicThresholdMass r restriction w [] tail =
      iwaniecThresholdPartialMass restriction w [] tail (2 * r - 1) := by
  simpa only [List.length_nil, Nat.sub_zero] using
    iwaniecCubicThresholdMass_eq_partialLayers r restriction w [] tail (by simp; omega)

end

end Erdos1212Kernel
