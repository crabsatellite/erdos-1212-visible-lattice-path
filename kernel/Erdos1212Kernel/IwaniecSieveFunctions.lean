import Erdos1212Kernel.IwaniecCubicPaperMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-!
# Iwaniec 1971 Section 3 sieve functions

These are the literal functions in equations (3.1)--(3.3).  `gEven n` is
`g_(2n+2)` and `gOdd n` is `g_(2n+3)` in the paper.
-/

def iwaniecGTwo (s : Real) : Real :=
  if 2 ≤ s ∧ s ≤ 4 then 3 * Real.log (3 / (s - 1)) + s - 4 else 0

mutual
  noncomputable def iwaniecGEven : Nat → Real → Real
    | 0 => iwaniecGTwo
    | n + 1 => fun s =>
        if s ≤ (6 : Real) + 2 * n then
          ∫ t in s..((6 : Real) + 2 * n),
            iwaniecGOdd n (t - 1) / (t - 1)
        else 0

  noncomputable def iwaniecGOdd : Nat → Real → Real
    | n => fun s =>
        if s ≤ 3 then
          ∫ t in (3 : Real)..((5 : Real) + 2 * n),
            iwaniecGEven n (t - 1) / (t - 1)
        else if s ≤ (5 : Real) + 2 * n then
          ∫ t in s..((5 : Real) + 2 * n),
            iwaniecGEven n (t - 1) / (t - 1)
        else 0
end

@[simp]
theorem iwaniecGEven_zero (s : Real) :
    iwaniecGEven 0 s = iwaniecGTwo s := by
  rw [iwaniecGEven]

theorem iwaniecGEven_succ (n : Nat) {s : Real}
    (hupper : s ≤ (6 : Real) + 2 * n) :
    iwaniecGEven (n + 1) s =
      ∫ t in s..((6 : Real) + 2 * n),
        iwaniecGOdd n (t - 1) / (t - 1) := by
  simp [iwaniecGEven, hupper]

theorem iwaniecGEven_succ_eq_zero
    (n : Nat) {s : Real} (hupper : (6 : Real) + 2 * n ≤ s) :
    iwaniecGEven (n + 1) s = 0 := by
  rcases hupper.eq_or_lt with heq | hlt
  · subst s
    simp [iwaniecGEven]
  · simp [iwaniecGEven, not_le.mpr hlt]

theorem iwaniecGOdd_of_three_le
    (n : Nat) {s : Real} (hlower : 3 ≤ s)
    (hupper : s ≤ (5 : Real) + 2 * n) :
    iwaniecGOdd n s =
      ∫ t in s..((5 : Real) + 2 * n),
        iwaniecGEven n (t - 1) / (t - 1) := by
  rcases hlower.eq_or_lt with heq | hlt
  · subst s
    simp [iwaniecGOdd]
  · simp [iwaniecGOdd, not_le.mpr hlt, hupper]

theorem iwaniecGOdd_of_le_three
    (n : Nat) {s : Real} (hs : s ≤ 3) :
    iwaniecGOdd n s = iwaniecGOdd n 3 := by
  rcases hs.eq_or_lt with heq | hlt
  · subst s
    rfl
  · simp [iwaniecGOdd, hlt.le]

theorem iwaniecGOdd_eq_zero
    (n : Nat) {s : Real} (hupper : (5 : Real) + 2 * n ≤ s) :
    iwaniecGOdd n s = 0 := by
  rcases hupper.eq_or_lt with heq | hlt
  · subst s
    have hn : (0 : Real) ≤ n := by positivity
    have hthree : ¬(5 + 2 * (n : Real)) ≤ 3 := by linarith
    simp [iwaniecGOdd, hthree]
  · have hn : (0 : Real) ≤ n := by positivity
    have hthreeLt : (3 : Real) < 5 + 2 * (n : Real) := by linarith
    have hthree : ¬s ≤ 3 := not_le.mpr (hthreeLt.trans hlt)
    simp [iwaniecGOdd, hthree, not_le.mpr hlt]

theorem iwaniecGTwo_eq
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecGTwo s = 3 * Real.log (3 / (s - 1)) + s - 4 := by
  simp [iwaniecGTwo, hlower, hupper]

theorem iwaniecGTwo_eq_zero_of_four_le
    {s : Real} (hs : 4 ≤ s) :
    iwaniecGTwo s = 0 := by
  rcases hs.eq_or_lt with heq | hlt
  · subst s
    norm_num [iwaniecGTwo]
  · simp [iwaniecGTwo, not_le.mpr hlt]

theorem iwaniecGEven_eq_zero_of_boundary
    (n : Nat) {s : Real} (hboundary : (4 : Real) + 2 * n ≤ s) :
    iwaniecGEven n s = 0 := by
  cases n with
  | zero =>
      rw [iwaniecGEven_zero]
      apply iwaniecGTwo_eq_zero_of_four_le
      simpa using hboundary
  | succ n =>
      apply iwaniecGEven_succ_eq_zero n
      push_cast at hboundary ⊢
      ring_nf at hboundary ⊢
      exact hboundary

theorem iwaniecGOdd_eq_zero_of_boundary
    (n : Nat) {s : Real} (hboundary : (5 : Real) + 2 * n ≤ s) :
    iwaniecGOdd n s = 0 :=
  iwaniecGOdd_eq_zero n hboundary

theorem iwaniecGTwo_nonneg
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    0 ≤ iwaniecGTwo s := by
  rw [iwaniecGTwo_eq hlower hupper]
  have hden : 0 < s - 1 := by linarith
  have hx : 0 < (3 : Real) / (s - 1) := div_pos (by norm_num) hden
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hinv : ((3 : Real) / (s - 1))⁻¹ = (s - 1) / 3 := by
    field_simp
  rw [hinv] at hlog
  nlinarith

theorem iwaniecGTwo_nonneg_of_two_le
    {s : Real} (hs : 2 ≤ s) :
    0 ≤ iwaniecGTwo s := by
  by_cases hupper : s ≤ 4
  · exact iwaniecGTwo_nonneg hs hupper
  · rw [iwaniecGTwo_eq_zero_of_four_le (by linarith)]

theorem iwaniecGOdd_nonneg_of_even_nonneg
    (n : Nat)
    (heven : ∀ s : Real, 2 ≤ s → 0 ≤ iwaniecGEven n s) :
    ∀ s : Real, 1 ≤ s → 0 ≤ iwaniecGOdd n s := by
  intro s hs
  by_cases hthree : s ≤ 3
  · rw [iwaniecGOdd_of_le_three n hthree]
    have hn : (0 : Real) ≤ n := by positivity
    have hupper : (3 : Real) ≤ 5 + 2 * (n : Real) := by linarith
    rw [iwaniecGOdd_of_three_le n (le_refl 3) hupper]
    apply intervalIntegral.integral_nonneg hupper
    intro t ht
    have htDen : 0 < t - 1 := by linarith [ht.1]
    exact div_nonneg (heven (t - 1) (by linarith [ht.1])) (le_of_lt htDen)
  · have hlower : 3 ≤ s := le_of_not_ge hthree
    by_cases hupper : s ≤ 5 + 2 * (n : Real)
    · rw [iwaniecGOdd_of_three_le n hlower hupper]
      apply intervalIntegral.integral_nonneg hupper
      intro t ht
      have htDen : 0 < t - 1 := by linarith [ht.1]
      exact div_nonneg (heven (t - 1) (by linarith [ht.1])) (le_of_lt htDen)
    · rw [iwaniecGOdd_eq_zero n (le_of_not_ge hupper)]

theorem iwaniecGEven_succ_nonneg_of_odd_nonneg
    (n : Nat)
    (hodd : ∀ s : Real, 1 ≤ s → 0 ≤ iwaniecGOdd n s) :
    ∀ s : Real, 2 ≤ s → 0 ≤ iwaniecGEven (n + 1) s := by
  intro s hs
  by_cases hupper : s ≤ 6 + 2 * (n : Real)
  · rw [iwaniecGEven_succ n hupper]
    apply intervalIntegral.integral_nonneg hupper
    intro t ht
    have htDen : 0 < t - 1 := by linarith [ht.1]
    exact div_nonneg (hodd (t - 1) (by linarith [ht.1])) (le_of_lt htDen)
  · rw [iwaniecGEven_succ_eq_zero n (le_of_not_ge hupper)]

theorem iwaniecGEven_GOdd_nonneg (n : Nat) :
    (∀ s : Real, 2 ≤ s → 0 ≤ iwaniecGEven n s) ∧
      (∀ s : Real, 1 ≤ s → 0 ≤ iwaniecGOdd n s) := by
  induction n with
  | zero =>
      have heven : ∀ s : Real, 2 ≤ s → 0 ≤ iwaniecGEven 0 s := by
        intro s hs
        rw [iwaniecGEven_zero]
        exact iwaniecGTwo_nonneg_of_two_le hs
      exact ⟨heven, iwaniecGOdd_nonneg_of_even_nonneg 0 heven⟩
  | succ n ih =>
      have heven := iwaniecGEven_succ_nonneg_of_odd_nonneg n ih.2
      exact ⟨heven, iwaniecGOdd_nonneg_of_even_nonneg (n + 1) heven⟩

theorem iwaniecGEven_nonneg (n : Nat) {s : Real} (hs : 2 ≤ s) :
    0 ≤ iwaniecGEven n s :=
  (iwaniecGEven_GOdd_nonneg n).1 s hs

theorem iwaniecGOdd_nonneg (n : Nat) {s : Real} (hs : 1 ≤ s) :
    0 ≤ iwaniecGOdd n s :=
  (iwaniecGEven_GOdd_nonneg n).2 s hs

theorem iwaniecGTwo_le_three_mul_log_three
    {s : Real} (hlower : 2 ≤ s) :
    iwaniecGTwo s ≤ 3 * Real.log 3 := by
  by_cases hupper : s ≤ 4
  · rw [iwaniecGTwo_eq hlower hupper]
    have hden : 0 < s - 1 := by linarith
    have hratioPos : 0 < (3 : Real) / (s - 1) :=
      div_pos (by norm_num) hden
    have hratio : (3 : Real) / (s - 1) ≤ 3 := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hlog : Real.log ((3 : Real) / (s - 1)) ≤ Real.log 3 :=
      Real.strictMonoOn_log.monotoneOn hratioPos (by norm_num) hratio
    linarith
  · rw [iwaniecGTwo_eq_zero_of_four_le (by linarith)]
    have : (0 : Real) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity

def iwaniecEvenSievePartialSum (m : Nat) (s : Real) : Real :=
  ∑ n ∈ Finset.range m, iwaniecGEven n s

def iwaniecOddSievePartialSum (m : Nat) (s : Real) : Real :=
  ∑ n ∈ Finset.range m, iwaniecGOdd n s

theorem iwaniecEvenSievePartialSum_nonneg
    (m : Nat) {s : Real} (hs : 2 ≤ s) :
    0 ≤ iwaniecEvenSievePartialSum m s := by
  unfold iwaniecEvenSievePartialSum
  exact Finset.sum_nonneg fun n _hn => iwaniecGEven_nonneg n hs

theorem iwaniecOddSievePartialSum_nonneg
    (m : Nat) {s : Real} (hs : 1 ≤ s) :
    0 ≤ iwaniecOddSievePartialSum m s := by
  unfold iwaniecOddSievePartialSum
  exact Finset.sum_nonneg fun n _hn => iwaniecGOdd_nonneg n hs

theorem iwaniecEvenSievePartialSum_mono
    {left right : Nat} (h : left ≤ right) {s : Real} (hs : 2 ≤ s) :
    iwaniecEvenSievePartialSum left s ≤
      iwaniecEvenSievePartialSum right s := by
  unfold iwaniecEvenSievePartialSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono h
  · intro n _hn _hnot
    exact iwaniecGEven_nonneg n hs

theorem iwaniecOddSievePartialSum_mono
    {left right : Nat} (h : left ≤ right) {s : Real} (hs : 1 ≤ s) :
    iwaniecOddSievePartialSum left s ≤
      iwaniecOddSievePartialSum right s := by
  unfold iwaniecOddSievePartialSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono h
  · intro n _hn _hnot
    exact iwaniecGOdd_nonneg n hs

noncomputable def iwaniecEvenSieveSeries (s : Real) : Real :=
  ∑' n : Nat, iwaniecGEven n s

noncomputable def iwaniecOddSieveSeries (s : Real) : Real :=
  ∑' n : Nat, iwaniecGOdd n s

def iwaniecLowerSieveFunction (s : Real) : Real :=
  if 2 ≤ s ∧ s ≤ 4 then
    s - 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1)
  else 0

def iwaniecUpperSieveFunction (s : Real) : Real :=
  if 3 ≤ s ∧ s ≤ 5 then
    s - 6 + 2 * Real.exp Real.eulerMascheroniConstant *
      (1 - ∫ x in (1 : Real)..(s - 2), Real.log x / (x + 1))
  else 0

def iwaniecLowerSieveGain (s : Real) : Real :=
  1 - iwaniecLowerSieveFunction s / s

theorem iwaniecLowerSieveGain_eq
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecLowerSieveGain s =
      2 * Real.exp Real.eulerMascheroniConstant *
        Real.log (s - 1) / s := by
  have hs : s ≠ 0 := by linarith
  unfold iwaniecLowerSieveGain iwaniecLowerSieveFunction
  rw [if_pos ⟨hlower, hupper⟩]
  field_simp
  ring

theorem iwaniecLowerSieveGain_pos
    {s : Real} (hlower : 2 < s) (hupper : s ≤ 4) :
    0 < iwaniecLowerSieveGain s := by
  rw [iwaniecLowerSieveGain_eq hlower.le hupper]
  have hlog : 0 < Real.log (s - 1) := Real.log_pos (by linarith)
  positivity

end

end Erdos1212Kernel
