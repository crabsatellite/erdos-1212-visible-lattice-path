import Erdos1212Kernel.IwaniecThresholdLayer
import Erdos1212Kernel.IwaniecCubicRealLevelTransport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- The same exact first-failure layer in the paper's real child level.
Every successful selection divides level by that prime; the last failure
retains the complete suffix Euler product. -/
def iwaniecCubicRealThresholdLayer : Nat → Real → List Nat → Nat → Real
  | _, _, [], _ => 0
  | _, _, _ :: _, 0 => 0
  | offset, level, p :: tail, k + 1 =>
      iwaniecCubicRealThresholdLayer offset level tail (k + 1) +
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecCubicRealThresholdLayer (offset + 1) (level / p) tail k
        else if k = 0 then (p : Real)⁻¹ * |iwaniecListEulerProduct iwaniecReciprocalFactorWeight tail| else 0

@[simp] theorem iwaniecCubicRealThresholdLayer_zero (offset : Nat) (level : Real) (tail : List Nat) :
    iwaniecCubicRealThresholdLayer offset level tail 0 = 0 := by cases tail <;> rfl

@[simp] theorem iwaniecCubicRealThresholdLayer_nil (offset : Nat) (level : Real) (k : Nat) :
    iwaniecCubicRealThresholdLayer offset level [] k = 0 := rfl

theorem iwaniecCubicRealThresholdLayer_nonneg (offset : Nat) (level : Real) (tail : List Nat) (k : Nat) :
    0 ≤ iwaniecCubicRealThresholdLayer offset level tail k := by
  induction tail generalizing offset level k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [iwaniecCubicRealThresholdLayer]
          apply add_nonneg (ih offset level (k + 1))
          split
          · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (ih (offset + 1) (level / p) k)
          · split
            · positivity
            · exact le_rfl

theorem iwaniecCubicRealThresholdLayer_eq_zero_of_length
    (offset : Nat) (level : Real) (tail : List Nat) (k : Nat) (hk : tail.length < k) :
    iwaniecCubicRealThresholdLayer offset level tail k = 0 := by
  induction tail generalizing offset level k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => omega
      | succ k =>
          have ht : tail.length < k := by simp only [List.length_cons] at hk; omega
          have hk0 : k ≠ 0 := by omega
          rw [iwaniecCubicRealThresholdLayer, ih offset level (k + 1) (by omega),
            ih (offset + 1) (level / p) k ht]
          simp [hk0]

theorem iwaniecCubicRealThresholdLayer_eq_sum_firstFactor
    (offset : Nat) (level : Real) (tail : List Nat) (k : Nat) :
    iwaniecCubicRealThresholdLayer offset level tail (k + 1) =
      ∑ i : Fin tail.length,
        if Even offset ∨ (tail[i] : Real) ^ 3 < level then
          (tail[i] : Real)⁻¹ * iwaniecCubicRealThresholdLayer (offset + 1) (level / tail[i])
            (tail.drop (i.val + 1)) k
        else if k = 0 then (tail[i] : Real)⁻¹ *
          |iwaniecListEulerProduct iwaniecReciprocalFactorWeight (tail.drop (i.val + 1))| else 0 := by
  induction tail with
  | nil => simp
  | cons p tail ih =>
      rw [iwaniecCubicRealThresholdLayer, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero,
        List.getElem_cons_zero, zero_add, List.drop_succ_cons, List.drop_zero,
        Fin.val_succ, List.getElem_cons_succ]
      exact add_comm _ _

theorem iwaniecCubicRealThresholdLayer_add_two
    (offset : Nat) (level : Real) (tail : List Nat) (k : Nat) :
    iwaniecCubicRealThresholdLayer (offset + 2) level tail k =
      iwaniecCubicRealThresholdLayer offset level tail k := by
  induction tail generalizing offset level k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp
      | succ k =>
          have heven : Even (offset + 2) ↔ Even offset := by
            simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
            omega
          rw [iwaniecCubicRealThresholdLayer, iwaniecCubicRealThresholdLayer]
          simp only [heven]
          rw [ih offset level (k + 1)]
          have hoff : offset + 2 + 1 = (offset + 1) + 2 := by omega
          rw [hoff, ih (offset + 1) (level / p) k]

theorem iwaniecCubicRealThresholdLayer_parity
    (offset : Nat) (level : Real) (tail : List Nat) (k : Nat) (hparity : ¬Even (offset + k)) :
    iwaniecCubicRealThresholdLayer offset level tail k = 0 := by
  induction tail generalizing offset level k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [iwaniecCubicRealThresholdLayer, ih offset level (k + 1) hparity]
          by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
          · have hchild : ¬Even (offset + 1 + k) := by
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hparity
            rw [if_pos hc, ih (offset + 1) (level / p) k hchild]
            ring
          · rw [if_neg hc]
            by_cases hk0 : k = 0
            · subst k
              have hodd : Odd offset := Nat.not_even_iff_odd.mp (fun hh => hc (Or.inl hh))
              obtain ⟨m, hm⟩ := hodd
              have heven : Even (offset + 1) := ⟨m + 1, by omega⟩
              exact (hparity heven).elim
            · rw [if_neg hk0]
              ring

end

end Erdos1212Kernel
