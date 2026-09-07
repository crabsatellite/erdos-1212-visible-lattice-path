import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Erdos1212Kernel

set_option maxHeartbeats 0

/-! A prime-free majorant for the entire repeat-prime tail. -/

theorem reciprocal_square_le_telescope (n : Nat) (hn : 2 <= n) :
    (1 : Rat) / (n : Rat) ^ 2 <=
      1 / ((n : Rat) - 1) - 1 / (n : Rat) := by
  have hnpos : (0 : Rat) < n := by exact_mod_cast (by omega : 0 < n)
  have hnone : (1 : Rat) < n := by exact_mod_cast (by omega : (1 : Nat) < n)
  have hnminus : (0 : Rat) < (n : Rat) - 1 := by
    linarith
  have hdiff : (n : Rat) - ((n - 1 : Nat) : Rat) = 1 := by
    rw [Nat.cast_sub (by omega : 1 <= n)]
    norm_num
  field_simp [ne_of_gt hnpos, ne_of_gt hnminus]
  nlinarith

theorem integer_reciprocal_square_partial_tail (start count : Nat)
    (hstart : 2 <= start) :
    (Finset.range count).sum (fun offset =>
        (1 : Rat) / (start + offset : Nat) ^ 2) <=
      1 / ((start : Rat) - 1) -
        1 / ((start + count : Nat) - 1 : Rat) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Finset.sum_range_succ]
      calc
        (Finset.range count).sum (fun offset =>
              (1 : Rat) / (start + offset : Nat) ^ 2) +
            (1 : Rat) / (start + count : Nat) ^ 2 <=
            (1 / ((start : Rat) - 1) -
                1 / ((start + count : Nat) - 1 : Rat)) +
              (1 : Rat) / (start + count : Nat) ^ 2 :=
          add_le_add ih le_rfl
        _ <= (1 / ((start : Rat) - 1) -
                1 / ((start + count : Nat) - 1 : Rat)) +
              (1 / ((start + count : Nat) - 1 : Rat) -
                1 / (start + count : Nat)) := by
          exact add_le_add le_rfl
            (reciprocal_square_le_telescope (start + count) (by omega))
        _ = 1 / ((start : Rat) - 1) -
              1 / ((start + (count + 1) : Nat) - 1 : Rat) := by
          push_cast
          ring

theorem integer_reciprocal_square_tail_from_61 (count : Nat) :
    (Finset.range count).sum (fun offset =>
        (1 : Rat) / (61 + offset : Nat) ^ 2) <= 1 / 60 := by
  calc
    (Finset.range count).sum (fun offset =>
        (1 : Rat) / (61 + offset : Nat) ^ 2) <=
      1 / ((61 : Rat) - 1) -
        1 / ((61 + count : Nat) - 1 : Rat) :=
      integer_reciprocal_square_partial_tail 61 count (by omega)
    _ <= 1 / 60 := by
      have hden : (0 : Rat) <=
          1 / ((61 + count : Nat) - 1 : Rat) := by
        have hpositive : (0 : Rat) < (61 + count : Nat) - 1 := by
          have hcount : (0 : Rat) <= count := by positivity
          push_cast
          linarith
        exact div_nonneg (by norm_num) (le_of_lt hpositive)
      norm_num
      linarith

/-- An arbitrary finite set of distinct integers above `start` is dominated
by the complete reciprocal-square tail beginning at `start`.  The proof
fills the gaps up to the largest member of the set and then invokes the
finite telescoping estimate; no infinite-series principle is needed. -/
theorem finite_integer_reciprocal_square_tail
    {pool : Finset Nat} {start : Nat}
    (hstart : 2 <= start)
    (hpool : ∀ n ∈ pool, start ≤ n) :
    (∑ n ∈ pool, (1 : Rat) / (n : Rat) ^ 2) ≤
      1 / ((start : Rat) - 1) := by
  classical
  let stop := pool.sup (fun n : Nat => n) + 1
  have hsubset : pool ⊆ Finset.Ico start stop := by
    intro n hn
    apply Finset.mem_Ico.mpr
    refine ⟨hpool n hn, ?_⟩
    have hnSup : n ≤ pool.sup (fun other : Nat => other) :=
      Finset.le_sup (f := fun other : Nat => other) hn
    exact hnSup.trans_lt (Nat.lt_succ_self _)
  calc
    (∑ n ∈ pool, (1 : Rat) / (n : Rat) ^ 2) ≤
        ∑ n ∈ Finset.Ico start stop,
          (1 : Rat) / (n : Rat) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ => by positivity)
    _ = ∑ offset ∈ Finset.range (stop - start),
          (1 : Rat) / (start + offset : Nat) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ <= 1 / ((start : Rat) - 1) -
          1 / ((start + (stop - start) : Nat) - 1 : Rat) :=
      integer_reciprocal_square_partial_tail start (stop - start) hstart
    _ <= 1 / ((start : Rat) - 1) := by
      have hdenominator :
          (0 : Rat) < ((start + (stop - start) : Nat) : Rat) - 1 := by
        apply sub_pos.mpr
        exact_mod_cast (by omega : 1 < start + (stop - start))
      have hnonnegative :
          (0 : Rat) <=
            1 / ((start + (stop - start) : Nat) - 1 : Rat) :=
        one_div_nonneg.mpr hdenominator.le
      linarith

end Erdos1212Kernel
