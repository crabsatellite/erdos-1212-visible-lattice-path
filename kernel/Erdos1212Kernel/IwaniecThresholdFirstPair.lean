import Erdos1212Kernel.IwaniecCubicMainExact
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- In the last two available depths the only possible failure is the
finite terminal cut, never a cubic threshold failure. -/
theorem iwaniecCubicThresholdMass_eq_zero_of_last_pair
    {α : Type*} (r : Nat) (restriction : List α → α → Bool) (w : α → Real)
    (selected tail : List α) (hdepth : 2 * r ≤ selected.length + 2) :
    iwaniecCubicThresholdMass r restriction w selected tail = 0 := by
  induction tail generalizing selected with
  | nil => rfl
  | cons p tail ih =>
      rw [iwaniecCubicThresholdMass]
      by_cases hselect : selected.length + 1 < 2 * r ∧
          (Even selected.length ∨ restriction selected p)
      · rw [dif_pos hselect, ih selected hdepth,
          ih (selected ++ [p]) (by simp only [List.length_append, List.length_singleton]; omega)]
        ring
      · have hterminal : 2 * r ≤ selected.length + 1 := by
          by_contra hn
          have heven : Even selected.length := ⟨r - 1, by omega⟩
          exact hselect ⟨by omega, Or.inl heven⟩
        rw [dif_neg hselect, if_pos hterminal, ih selected hdepth]

/-- Exact first-factor decomposition of the actual stopped threshold tree. -/
theorem iwaniecCubicThresholdMass_eq_sum_firstFactor
    {α : Type*} (r : Nat) (restriction : List α → α → Bool) (w : α → Real)
    (selected tail : List α) :
    iwaniecCubicThresholdMass r restriction w selected tail =
      ∑ i : Fin tail.length,
        if selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected tail[i]) then
          |w tail[i]| * iwaniecCubicThresholdMass r restriction w
            (selected ++ [tail[i]]) (tail.drop (i.val + 1))
        else if 2 * r ≤ selected.length + 1 then 0
        else |w tail[i]| * |iwaniecListEulerProduct w (tail.drop (i.val + 1))| := by
  induction tail with
  | nil => simp [iwaniecCubicThresholdMass]
  | cons p tail ih =>
      rw [iwaniecCubicThresholdMass, ih]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.getElem_fin, Fin.val_zero,
        List.getElem_cons_zero, zero_add, List.drop_succ_cons, List.drop_zero,
        Fin.val_succ, List.getElem_cons_succ]
      by_cases hs : selected.length + 1 < 2 * r ∧ (Even selected.length ∨ restriction selected p)
      · simp only [dif_pos hs, if_pos hs]
        exact add_comm _ _
      · simp only [dif_neg hs, if_neg hs]
        by_cases ht : 2 * r ≤ selected.length + 1
        · simp only [if_pos ht, zero_add]
        · simp only [if_neg ht]
          exact add_comm _ _

/-- At depth one with r=2 only the second-prime cubic failure is charged. -/
theorem iwaniecCubicThresholdMass_firstPair_singleton
    (y p : Nat) (tail : List Nat) :
    iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight [p] tail =
      ∑ i : Fin tail.length,
        if y ≤ tail[i] ^ 3 * p then
          |iwaniecReciprocalFactorWeight tail[i]| *
            |iwaniecListEulerProduct iwaniecReciprocalFactorWeight (tail.drop (i.val + 1))|
        else 0 := by
  rw [iwaniecCubicThresholdMass_eq_sum_firstFactor]
  apply Finset.sum_congr rfl
  intro i hi
  have hzero := iwaniecCubicThresholdMass_eq_zero_of_last_pair 2
    (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight
    ([p] ++ [tail[i]]) (tail.drop (i.val + 1)) (by simp)
  have hzero' : iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight [p, tail[i]] (tail.drop (i.val + 1)) = 0 := hzero
  simp only [List.length_singleton, iwaniecCubicEvenRestriction, List.prod_cons,
    List.prod_nil, mul_one, decide_eq_true_eq]
  by_cases hfail : y ≤ tail[i] ^ 3 * p
  · have hlt : ¬tail[i] ^ 3 * p < y := by omega
    simp only [Fin.getElem_fin] at hfail hlt
    norm_num [hfail, hlt]
  · have hlt : tail[i] ^ 3 * p < y := by omega
    simp only [Fin.getElem_fin] at hfail hlt hzero'
    norm_num [hfail, hlt, hzero']

theorem iwaniecCubicThresholdMass_firstPair_root (y : Nat) (tail : List Nat) :
    iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight [] tail =
      ∑ i : Fin tail.length, |iwaniecReciprocalFactorWeight tail[i]| *
        iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [tail[i]] (tail.drop (i.val + 1)) := by
  rw [iwaniecCubicThresholdMass_eq_sum_firstFactor]
  simp

end

end Erdos1212Kernel
