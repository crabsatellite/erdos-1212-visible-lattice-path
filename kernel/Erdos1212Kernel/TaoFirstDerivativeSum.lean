import Erdos1212Kernel.TaoFirstDerivativeWeight
import Erdos1212Kernel.TaoFirstDerivativeAbel

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

/-- The literal one-unit increment proof, retaining both endpoint costs and
the number of interior weight differences. -/
theorem taoFirstDerivative_sum_succ_bound (f f' f'' : Real → Real) (a : Real) (m : Nat) {δ D : Real}
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Set.Icc a (a + (m + 1 : Nat)), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc a (a + (m + 1 : Nat)), HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc a (a + (m + 1 : Nat)), δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc a (a + (m + 1 : Nat)), |f' t| ≤ 1 / 2)
    (hsecond : ∀ t ∈ Set.Icc a (a + (m + 1 : Nat)), |f'' t| ≤ D) :
    ‖∑ n ∈ Finset.range (m + 1), taoCorputPhase (f (a + n))‖ ≤
      2 * (1 / δ) + (m : Real) * (D * ((2 * Real.pi) / δ ^ 2)) := by
  let z : Nat → Complex := fun n => taoCorputPhase (f (a + n))
  let w : Nat → Complex := fun n => taoFirstDerivativeWeight f (a + n)
  have hloc : ∀ n ≤ m, a + (n : Real) ∈ Set.Icc a (a + (m + 1 : Nat) - 1) := by
    intro n hn
    have hnR : (n : Real) ≤ m := by exact_mod_cast hn
    constructor
    · linarith [Nat.cast_nonneg (α := Real) n]
    · push_cast
      linarith
  have hz : ∀ n ≤ m + 1, ‖z n‖ ≤ 1 := by
    intro n _hn
    exact (taoCorputPhase_norm _).le
  have hw : ∀ n ≤ m, ‖w n‖ ≤ 1 / δ := by
    intro n hn
    exact taoFirstDerivativeWeight_norm_bound f f' hδ hf hlow hhigh (hloc n hn)
  have hvar : ∀ n < m, ‖w (n + 1) - w n‖ ≤ D * ((2 * Real.pi) / δ ^ 2) := by
    intro n hn
    have h := taoFirstDerivativeWeight_variation f f' f'' hδ hD hf hf' hlow hhigh hsecond
      (hloc n (by omega)) (hloc (n + 1) (by omega))
    have hdist : |(a + ((n + 1 : Nat) : Real)) - (a + (n : Real))| = 1 := by
      push_cast
      ring_nf
      norm_num
    simpa only [w, hdist, mul_one] using h
  have hid : (∑ n ∈ Finset.range (m + 1), taoCorputPhase (f (a + n))) =
      ∑ n ∈ Finset.range (m + 1), (z (n + 1) - z n) * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ m := by have := Finset.mem_range.mp hn; omega
    obtain ⟨hlo, hhi⟩ := taoPhaseIncrement_bounds f f' hf hlow hhigh (hloc n hn')
    have hne := taoCorputPhase_denominator_ne_zero hδ hlo hhi
    have h := taoFirstDerivative_phase_identity (f (a + n)) (f (a + n + 1)) hne
    simpa only [z, w, taoFirstDerivativeWeight, taoPhaseIncrement, Nat.cast_add, Nat.cast_one, add_assoc] using h
  rw [hid]
  exact taoFirstDerivative_abel_norm_bound z w m (by positivity) (by positivity) hz hw hvar

theorem taoFirstDerivative_sum_bound (f f' f'' : Real → Real) (a : Real) (M : Nat) {δ D : Real}
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc a (a + M), HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc a (a + M), δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc a (a + M), |f' t| ≤ 1 / 2)
    (hsecond : ∀ t ∈ Set.Icc a (a + M), |f'' t| ≤ D) :
    ‖∑ n ∈ Finset.range M, taoCorputPhase (f (a + n))‖ ≤
      2 * (1 / δ) + (M : Real) * (D * ((2 * Real.pi) / δ ^ 2)) := by
  cases M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, zero_mul, add_zero]
      positivity
  | succ m =>
      have h := taoFirstDerivative_sum_succ_bound f f' f'' a m hδ hD hf hf' hlow hhigh hsecond
      apply h.trans
      have hV : 0 ≤ D * ((2 * Real.pi) / δ ^ 2) := by positivity
      push_cast
      nlinarith

end

end Erdos1212Kernel
