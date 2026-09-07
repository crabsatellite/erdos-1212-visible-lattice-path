import Erdos1212Kernel.IwaniecCubicStoppedMassSplit

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniecListEulerProduct_nonneg {α : Type*} (w : α → Real) (tail : List α)
    (hw : ∀ p ∈ tail, w p ≤ 1) : 0 ≤ iwaniecListEulerProduct w tail := by
  induction tail with
  | nil => simp [iwaniecListEulerProduct]
  | cons p tail ih =>
      rw [iwaniecListEulerProduct_cons]
      exact mul_nonneg (sub_nonneg.mpr (hw p (by simp))) (ih (fun q hq => hw q (by simp [hq])))

theorem iwaniecLowerTree_stop_depth_not_even {α : Type*} (r : Nat)
    (restriction : List α → α → Bool) (selected : List α) (p : α)
    (hdepth : selected.length < 2 * r)
    (hstop : ¬(selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p))) :
    ¬Even selected.length := by
  intro heven
  obtain ⟨k, hk⟩ := heven
  apply hstop
  exact ⟨by omega, Or.inl ⟨k, hk⟩⟩

/-- Every stop of this lower tree has even total depth. Thus the Euler
defect has the exact prefix-parity sign, not just an absolute majorant. -/
theorem iwaniecWeightedTreeDefect_eq_signed_stoppedMass {α : Type*}
    (r : Nat) (restriction : List α → α → Bool) (w : α → Real)
    (selected tail : List α) (hdepth : selected.length < 2 * r)
    (hw : ∀ p ∈ tail, 0 ≤ w p ∧ w p ≤ 1) :
    iwaniecWeightedTreeDefect r restriction w selected tail =
      (-1 : Real) ^ selected.length * iwaniecWeightedStoppedMass r restriction w selected tail := by
  induction tail generalizing selected with
  | nil => simp [iwaniecWeightedTreeDefect, iwaniecWeightedLowerTreeSum, iwaniecListEulerProduct, iwaniecWeightedStoppedMass]
  | cons p tail ih =>
      have hwp := (hw p (by simp)).1
      have htail : ∀ q ∈ tail, 0 ≤ w q ∧ w q ≤ 1 := fun q hq => hw q (by simp [hq])
      have hskip := ih selected hdepth htail
      by_cases hselect : selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)
      · have hchild := ih (selected ++ [p]) (by simpa using hselect.1) htail
        have hsign : (-1 : Real) ^ (selected ++ [p]).length = -((-1 : Real) ^ selected.length) := by
          rw [List.length_append, List.length_singleton, pow_succ]
          ring
        rw [iwaniecWeightedTreeDefect_cons_of_select r restriction w selected p tail hselect,
          iwaniecWeightedStoppedMass, if_pos hselect, abs_of_nonneg hwp, hskip, hchild, hsign]
        ring
      · have hnotEven := iwaniecLowerTree_stop_depth_not_even r restriction selected p hdepth hselect
        have hsign : (-1 : Real) ^ selected.length = -1 := by simp [neg_one_pow_eq_ite, hnotEven]
        have hEuler := iwaniecListEulerProduct_nonneg w tail (fun q hq => (htail q hq).2)
        rw [iwaniecWeightedTreeDefect_cons_of_not_select r restriction w selected p tail hselect,
          iwaniecWeightedStoppedMass, if_neg hselect, abs_of_nonneg hwp, abs_of_nonneg hEuler, hskip, hsign]
        ring

theorem iwaniecLowerTree_eq_euler_sub_stoppedMass {α : Type*}
    {r : Nat} (hr : 0 < r) (restriction : List α → α → Bool) (w : α → Real) (tail : List α)
    (hw : ∀ p ∈ tail, 0 ≤ w p ∧ w p ≤ 1) :
    iwaniecWeightedLowerTreeSum r restriction w [] tail =
      iwaniecListEulerProduct w tail - iwaniecWeightedStoppedMass r restriction w [] tail := by
  have hh := iwaniecWeightedTreeDefect_eq_signed_stoppedMass r restriction w [] tail
    (by simp only [List.length_nil]; omega) hw
  simp only [List.length_nil, pow_zero, one_mul, iwaniecWeightedTreeDefect] at hh
  linarith only [hh]

end

end Erdos1212Kernel
