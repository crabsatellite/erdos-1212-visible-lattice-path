import Erdos1212Kernel.IwaniecCubicStoppedMassSplit
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- Exact first-failure layer of the original skip/select tree.
The last selected factor fails the rule; all earlier selections pass.
The full unused suffix Euler product is retained at that last factor. -/
def iwaniecThresholdLayer {α : Type*} (restriction : List α → α → Bool) (w : α → Real) :
    List α → List α → Nat → Real
  | _, [], _ => 0
  | _, _ :: _, 0 => 0
  | selected, p :: tail, k + 1 =>
      iwaniecThresholdLayer restriction w selected tail (k + 1) +
        if Even selected.length ∨ restriction selected p then
          |w p| * iwaniecThresholdLayer restriction w (selected ++ [p]) tail k
        else if k = 0 then |w p| * |iwaniecListEulerProduct w tail| else 0

@[simp] theorem iwaniecThresholdLayer_zero {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) :
    iwaniecThresholdLayer restriction w selected tail 0 = 0 := by cases tail <;> rfl

@[simp] theorem iwaniecThresholdLayer_nil {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected : List α) (k : Nat) :
    iwaniecThresholdLayer restriction w selected [] k = 0 := rfl

theorem iwaniecThresholdLayer_nonneg {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (k : Nat) :
    0 ≤ iwaniecThresholdLayer restriction w selected tail k := by
  induction tail generalizing selected k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [iwaniecThresholdLayer]
          apply add_nonneg (ih selected (k + 1))
          split
          · exact mul_nonneg (abs_nonneg _) (ih (selected ++ [p]) k)
          · split
            · positivity
            · exact le_rfl

theorem iwaniecThresholdLayer_eq_zero_of_length {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (k : Nat) (hk : tail.length < k) :
    iwaniecThresholdLayer restriction w selected tail k = 0 := by
  induction tail generalizing selected k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => omega
      | succ k =>
          have htail : tail.length < k := by simp only [List.length_cons] at hk; omega
          have hk0 : k ≠ 0 := by omega
          rw [iwaniecThresholdLayer, ih selected (k + 1) (by omega),
            ih (selected ++ [p]) k htail]
          simp [hk0]

/-- First-factor disintegration keeps both the successful child and
the failed last factor. It is an equality of the original finite layer. -/
theorem iwaniecThresholdLayer_eq_sum_firstFactor {α : Type*}
    (restriction : List α → α → Bool) (w : α → Real) (selected tail : List α) (k : Nat) :
    iwaniecThresholdLayer restriction w selected tail (k + 1) =
      ∑ i : Fin tail.length,
        if Even selected.length ∨ restriction selected tail[i] then
          |w tail[i]| * iwaniecThresholdLayer restriction w (selected ++ [tail[i]]) (tail.drop (i.val + 1)) k
        else if k = 0 then |w tail[i]| * |iwaniecListEulerProduct w (tail.drop (i.val + 1))| else 0 := by
  induction tail with
  | nil => simp
  | cons p tail ih =>
      rw [iwaniecThresholdLayer, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero,
        List.getElem_cons_zero, zero_add, List.drop_succ_cons, List.drop_zero,
        Fin.val_succ, List.getElem_cons_succ]
      exact add_comm _ _

end

end Erdos1212Kernel
