import Erdos1212Kernel.IwaniecThresholdLayerTransport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- The exact surviving depth-k term: every selection, including the
last, passes the rule, and the complete unused suffix is retained. -/
def iwaniecSurvivalLayer {α : Type*} (restriction : List α → α → Bool) (w : α → Real) :
    List α → List α → Nat → Real
  | _, tail, 0 => |iwaniecListEulerProduct w tail|
  | _, [], _ + 1 => 0
  | selected, p :: tail, k + 1 =>
      iwaniecSurvivalLayer restriction w selected tail (k + 1) +
        if Even selected.length ∨ restriction selected p then
          |w p| * iwaniecSurvivalLayer restriction w (selected ++ [p]) tail k
        else 0

@[simp] theorem iwaniecSurvivalLayer_zero {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) :
    iwaniecSurvivalLayer restriction w selected tail 0 = |iwaniecListEulerProduct w tail| := by cases tail <;> rfl

@[simp] theorem iwaniecSurvivalLayer_nil_succ {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected : List α) (k : Nat) :
    iwaniecSurvivalLayer restriction w selected [] (k + 1) = 0 := rfl

theorem iwaniecSurvivalLayer_nonneg {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (k : Nat) :
    0 ≤ iwaniecSurvivalLayer restriction w selected tail k := by
  induction tail generalizing selected k with
  | nil => cases k <;> simp
  | cons p tail ih =>
      cases k with
      | zero => exact abs_nonneg _
      | succ k =>
          rw [iwaniecSurvivalLayer]
          apply add_nonneg (ih selected (k + 1))
          split
          · exact mul_nonneg (abs_nonneg _) (ih (selected ++ [p]) k)
          · exact le_rfl

theorem iwaniecSurvivalLayer_eq_zero_of_length {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (k : Nat) (hk : tail.length < k) :
    iwaniecSurvivalLayer restriction w selected tail k = 0 := by
  induction tail generalizing selected k with
  | nil => cases k <;> simp_all
  | cons p tail ih =>
      cases k with
      | zero => omega
      | succ k =>
          have htail : tail.length < k := by simp only [List.length_cons] at hk; omega
          rw [iwaniecSurvivalLayer, ih selected (k + 1) (by omega), ih (selected ++ [p]) k htail]
          simp

theorem iwaniecSurvivalLayer_eq_sum_firstFactor {α : Type*}
    (restriction : List α → α → Bool) (w : α → Real) (selected tail : List α) (k : Nat) :
    iwaniecSurvivalLayer restriction w selected tail (k + 1) =
      ∑ i : Fin tail.length,
        if Even selected.length ∨ restriction selected tail[i] then
          |w tail[i]| * iwaniecSurvivalLayer restriction w (selected ++ [tail[i]]) (tail.drop (i.val + 1)) k
        else 0 := by
  induction tail with
  | nil => simp
  | cons p tail ih =>
      rw [iwaniecSurvivalLayer, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero,
        List.getElem_cons_zero, zero_add, List.drop_succ_cons, List.drop_zero,
        Fin.val_succ, List.getElem_cons_succ]
      exact add_comm _ _

end

end Erdos1212Kernel
