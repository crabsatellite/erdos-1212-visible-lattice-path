import Erdos1212Kernel.IwaniecCubicStoppedMassSplit
import Mathlib.Algebra.Order.Ring.Pow

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

def iwaniecElementaryMass
    {α : Type*} (factorWeight : α → Real) : Nat → List α → Real
  | 0, _tail => 1
  | _k + 1, [] => 0
  | k + 1, factor :: tail =>
      iwaniecElementaryMass factorWeight (k + 1) tail +
        |factorWeight factor| * iwaniecElementaryMass factorWeight k tail

theorem iwaniecElementaryMass_nonneg
    {α : Type*} (factorWeight : α → Real) (k : Nat) (tail : List α) :
    0 ≤ iwaniecElementaryMass factorWeight k tail := by
  induction tail generalizing k with
  | nil =>
      cases k <;> simp [iwaniecElementaryMass]
  | cons factor tail ih =>
      cases k with
      | zero => simp [iwaniecElementaryMass]
      | succ k =>
          rw [iwaniecElementaryMass]
          exact add_nonneg (ih (k + 1))
            (mul_nonneg (abs_nonneg _) (ih k))

theorem iwaniecElementaryMass_le_cons
    {α : Type*} (factorWeight : α → Real) (k : Nat)
    (factor : α) (tail : List α) :
    iwaniecElementaryMass factorWeight k tail ≤
      iwaniecElementaryMass factorWeight k (factor :: tail) := by
  cases k with
  | zero => simp [iwaniecElementaryMass]
  | succ k =>
      rw [iwaniecElementaryMass]
      exact le_add_of_nonneg_right
        (mul_nonneg (abs_nonneg _)
          (iwaniecElementaryMass_nonneg factorWeight k tail))

theorem abs_iwaniecListEulerProduct_le_one
    {α : Type*} (factorWeight : α → Real) (tail : List α)
    (hfactor : ∀ factor ∈ tail, |1 - factorWeight factor| ≤ 1) :
    |iwaniecListEulerProduct factorWeight tail| ≤ 1 := by
  induction tail with
  | nil => simp [iwaniecListEulerProduct]
  | cons factor tail ih =>
      rw [iwaniecListEulerProduct_cons, abs_mul]
      have hhead := hfactor factor (by simp)
      have htail : ∀ next ∈ tail, |1 - factorWeight next| ≤ 1 := by
        intro next hnext
        exact hfactor next (by simp [hnext])
      exact mul_le_one₀ hhead (abs_nonneg _) (ih htail)

/-- Terminal stopped mass is bounded by the elementary symmetric mass of the
remaining number of selections. -/
theorem iwaniecCubicTerminalMass_le_elementary
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (factorWeight : α → Real) (selected tail : List α)
    (hdepth : selected.length < 2 * r)
    (hfactor : ∀ factor ∈ tail, |1 - factorWeight factor| ≤ 1) :
    iwaniecCubicTerminalMass r evenRestriction factorWeight selected tail ≤
      iwaniecElementaryMass factorWeight
        (2 * r - selected.length) tail := by
  induction tail generalizing selected with
  | nil =>
      simp [iwaniecCubicTerminalMass,
        iwaniecElementaryMass_nonneg]
  | cons factor tail ih =>
      have htailFactor :
          ∀ next ∈ tail, |1 - factorWeight next| ≤ 1 := by
        intro next hnext
        exact hfactor next (by simp [hnext])
      have hremainPos : 0 < 2 * r - selected.length :=
        Nat.sub_pos_of_lt hdepth
      obtain ⟨remaining, hremain⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hremainPos)
      rw [iwaniecCubicTerminalMass]
      rw [hremain]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ evenRestriction selected factor)
      · rw [dif_pos hselect]
        rw [iwaniecElementaryMass]
        have hskip := ih selected hdepth htailFactor
        rw [hremain] at hskip
        have hchildDepth : (selected ++ [factor]).length < 2 * r := by
          simpa using hselect.1
        have hchild := ih (selected ++ [factor]) hchildDepth htailFactor
        have hchildIndex :
            2 * r - (selected ++ [factor]).length = remaining := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [hchildIndex] at hchild
        exact add_le_add hskip
          (mul_le_mul_of_nonneg_left hchild (abs_nonneg _))
      · rw [dif_neg hselect]
        by_cases hterminal : 2 * r ≤ selected.length + 1
        · rw [if_pos hterminal]
          have hremaining : remaining = 0 := by omega
          subst remaining
          rw [iwaniecElementaryMass]
          have hskip := ih selected hdepth htailFactor
          rw [hremain] at hskip
          have heuler := abs_iwaniecListEulerProduct_le_one
            factorWeight tail htailFactor
          simpa [iwaniecElementaryMass] using
            add_le_add hskip
              (mul_le_mul_of_nonneg_left heuler (abs_nonneg _))
        · rw [if_neg hterminal]
          rw [iwaniecElementaryMass]
          have hskip := ih selected hdepth htailFactor
          rw [hremain] at hskip
          exact hskip.trans
            (iwaniecElementaryMass_le_cons factorWeight (remaining + 1)
              factor tail)

/-- Sharp elementary-symmetric inequality for the list carrier. -/
theorem factorial_mul_iwaniecElementaryMass_le_sum_pow
    {α : Type*} (factorWeight : α → Real) (k : Nat) (tail : List α) :
    (k.factorial : Real) * iwaniecElementaryMass factorWeight k tail ≤
      (tail.map fun factor => |factorWeight factor|).sum ^ k := by
  induction tail generalizing k with
  | nil =>
      cases k with
      | zero => simp [iwaniecElementaryMass]
      | succ k => simp [iwaniecElementaryMass]
  | cons factor tail ih =>
      cases k with
      | zero => simp [iwaniecElementaryMass]
      | succ k =>
          let total := (tail.map fun next => |factorWeight next|).sum
          let atom := |factorWeight factor|
          have htotal : 0 ≤ total := by
            dsimp [total]
            apply List.sum_nonneg
            intro value hvalue
            obtain ⟨next, _hnext, rfl⟩ := List.mem_map.mp hvalue
            exact abs_nonneg _
          have hatom : 0 ≤ atom := abs_nonneg _
          have hsame := ih (k + 1)
          have hprevious := ih k
          have hscaled :
              (((k + 1 : Nat) : Real) * atom) *
                  ((k.factorial : Real) *
                    iwaniecElementaryMass factorWeight k tail) ≤
                (((k + 1 : Nat) : Real) * atom) * total ^ k :=
            mul_le_mul_of_nonneg_left hprevious
              (mul_nonneg (by positivity) hatom)
          have hbernoulli :
              total ^ (k + 1) +
                  (((k + 1 : Nat) : Real) * total ^ k) * atom ≤
                (total + atom) ^ (k + 1) := by
            simpa [Nat.add_sub_cancel, mul_assoc, mul_comm, mul_left_comm] using
              (pow_add_mul_le_add_pow htotal
                (by positivity : 0 ≤ 2 * total + atom) (k + 1))
          rw [iwaniecElementaryMass, Nat.factorial_succ, Nat.cast_mul]
          change
            (((k + 1 : Nat) : Real) * (k.factorial : Real)) *
                (iwaniecElementaryMass factorWeight (k + 1) tail +
                  atom * iwaniecElementaryMass factorWeight k tail) ≤
              (atom :: tail.map fun next => |factorWeight next|).sum ^ (k + 1)
          change _ ≤ (atom + total) ^ (k + 1)
          calc
            (((k + 1 : Nat) : Real) * (k.factorial : Real)) *
                (iwaniecElementaryMass factorWeight (k + 1) tail +
                  atom * iwaniecElementaryMass factorWeight k tail) =
              (k + 1).factorial *
                  iwaniecElementaryMass factorWeight (k + 1) tail +
                (((k + 1 : Nat) : Real) * atom) *
                  ((k.factorial : Real) *
                    iwaniecElementaryMass factorWeight k tail) := by
                rw [Nat.factorial_succ, Nat.cast_mul]
                ring
            _ ≤ total ^ (k + 1) +
                (((k + 1 : Nat) : Real) * atom) * total ^ k :=
              add_le_add hsame hscaled
            _ = total ^ (k + 1) +
                (((k + 1 : Nat) : Real) * total ^ k) * atom := by ring
            _ ≤ (total + atom) ^ (k + 1) := hbernoulli
            _ = (atom + total) ^ (k + 1) := by rw [add_comm]

end

end Erdos1212Kernel
