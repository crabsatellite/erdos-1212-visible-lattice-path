import Erdos1212Kernel.IwaniecEffectivePrimeRemainder

namespace Erdos1212Kernel

noncomputable section

open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 650000

def iwaniecEulerTailTerm (n : Nat) : Real :=
  if n.Prime then Real.log (1 / (1 - 1 / (n : Real))) - 1 / (n : Real) else 0

theorem iwaniecEulerTailTerm_nonneg (n : Nat) : 0 ≤ iwaniecEulerTailTerm n := by
  by_cases hn : n.Prime
  · have hp := Erdos696.Mertens.one_sub_inv_prime_pos n hn
    have hh := Real.log_le_sub_one_of_pos hp
    unfold iwaniecEulerTailTerm
    rw [if_pos hn, one_div, Real.log_inv]
    linarith only [hh]
  · simp [iwaniecEulerTailTerm, hn]

theorem iwaniecEulerTailTerm_le {n : Nat} (hn : 2 ≤ n) :
    iwaniecEulerTailTerm n ≤ 1 / ((n : Real) * ((n : Real) - 1)) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 0 < (n : Real) - 1 := by
    have h : (2 : Real) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hp : n.Prime
  · have heq : 1 / (1 - 1 / (n : Real)) = 1 + 1 / ((n : Real) - 1) := by
      field_simp [hn0.ne', hn1.ne']
      <;> ring
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / ((n : Real) - 1) by positivity)
    unfold iwaniecEulerTailTerm
    rw [if_pos hp, heq]
    have hbound : Real.log (1 + 1 / ((n : Real) - 1)) - 1 / (n : Real) ≤
        1 / ((n : Real) - 1) - 1 / (n : Real) := by linarith only [hh]
    apply hbound.trans_eq
    field_simp [hn0.ne', hn1.ne']
    <;> ring
  · rw [iwaniecEulerTailTerm, if_neg hp]
    positivity

theorem iwaniecMertensTail_eq_sum (N : Nat) :
    Erdos696.Mertens.mertensTail N = ∑ n ∈ Finset.range (N + 1), iwaniecEulerTailTerm n := by
  unfold Erdos696.Mertens.mertensTail iwaniecEulerTailTerm
  rw [Finset.sum_filter]

theorem iwaniec_reciprocal_tail_interval {N M : Nat} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico (N + 1) (M + 1), 1 / ((n : Real) * ((n : Real) - 1))) =
      1 / (N : Real) - 1 / (M : Real) := by
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have hM : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
      have hM1 : (M : Real) + 1 ≠ 0 := by positivity
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      field_simp [hN0, hM.ne', hM1]
      <;> ring

theorem iwaniecMertensTail_interval_bound {N M : Nat} (hN : 1 ≤ N) (hNM : N ≤ M) :
    0 ≤ Erdos696.Mertens.mertensTail M - Erdos696.Mertens.mertensTail N ∧
      Erdos696.Mertens.mertensTail M - Erdos696.Mertens.mertensTail N ≤ 1 / (N : Real) := by
  have hsplit := Finset.sum_range_add_sum_Ico iwaniecEulerTailTerm (show N + 1 ≤ M + 1 by omega)
  have heq : Erdos696.Mertens.mertensTail M - Erdos696.Mertens.mertensTail N =
      ∑ n ∈ Finset.Ico (N + 1) (M + 1), iwaniecEulerTailTerm n := by
    rw [iwaniecMertensTail_eq_sum, iwaniecMertensTail_eq_sum]
    linarith only [hsplit]
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun n _ => iwaniecEulerTailTerm_nonneg n), ?_⟩
  have hsum : (∑ n ∈ Finset.Ico (N + 1) (M + 1), iwaniecEulerTailTerm n) ≤
      ∑ n ∈ Finset.Ico (N + 1) (M + 1), 1 / ((n : Real) * ((n : Real) - 1)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact iwaniecEulerTailTerm_le (by have hh := (Finset.mem_Ico.mp hn).1; omega)
  rw [iwaniec_reciprocal_tail_interval hN hNM] at hsum
  exact hsum.trans (sub_le_self _ (by positivity))

theorem iwaniecMertensTail_limit_bound {N : Nat} (hN : 1 ≤ N) :
    0 ≤ Erdos696.Mertens.mertensH' - Erdos696.Mertens.mertensTail N ∧
      |Erdos696.Mertens.mertensH' - Erdos696.Mertens.mertensTail N| ≤ 1 / (N : Real) := by
  have hlim := Erdos696.Mertens.mertensTail_tendsto.sub_const (Erdos696.Mertens.mertensTail N)
  have hnonneg : 0 ≤ Erdos696.Mertens.mertensH' - Erdos696.Mertens.mertensTail N := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (iwaniecMertensTail_interval_bound hN hM).1
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with M hM
  exact (iwaniecMertensTail_interval_bound hN hM).2

end

end Erdos1212Kernel
