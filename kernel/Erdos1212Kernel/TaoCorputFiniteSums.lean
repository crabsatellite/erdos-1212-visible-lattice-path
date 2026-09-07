import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1300000

def taoCorputInterval (a : Int) (N : Nat) : Finset Int := Finset.Ico a (a + N)

def taoCorputPadding (a : Int) (N H : Nat) : Finset Int := Finset.Ico (a - H) (a + N)

def taoCorputSum (z : Int → Complex) (a : Int) (N : Nat) : Complex :=
  ∑ n ∈ taoCorputInterval a N, z n

def taoCorputCorrelation (z : Int → Complex) (a : Int) (N h : Nat) : Complex :=
  ∑ n ∈ taoCorputInterval a N, z (n + h) * star (z n)

theorem taoCorputInterval_card (a : Int) (N : Nat) : (taoCorputInterval a N).card = N := by
  simp [taoCorputInterval]

theorem taoCorputPadding_card (a : Int) (N H : Nat) : (taoCorputPadding a N H).card = N + H := by
  simp only [taoCorputPadding, Int.card_Ico]
  omega

/-- Exact translation of a zero-extended interval sum into the source's
padded averaging interval. The support condition is consumed on both sides. -/
theorem taoCorput_shift_sum {M : Type*} [AddCommMonoid M] (z : Int → M)
    (a : Int) (N H : Nat) {h : Int} (hh0 : 0 ≤ h) (hhH : h ≤ H)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (∑ n ∈ taoCorputPadding a N H, z (n + h)) = ∑ n ∈ taoCorputInterval a N, z n := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _hn _hz => n + h)
  · intro n _hn hnz
    by_contra hn
    exact hnz (hz (n + h) hn)
  · intro n₁ _h₁ _hz₁ n₂ _h₂ _hz₂ heq
    omega
  · intro m hm hmz
    have hmI : a ≤ m ∧ m < a + N := Finset.mem_Ico.mp hm
    have hn : m - h ∈ taoCorputPadding a N H := by
      apply Finset.mem_Ico.mpr
      constructor <;> omega
    refine ⟨m - h, hn, ?_, by omega⟩
    simpa only [sub_add_cancel] using hmz
  · intro n _hn _hnz
    rfl

theorem taoCorput_complex_cauchy {ι : Type*} (s : Finset ι) (z : ι → Complex) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : Real) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have hn := norm_sum_le s z
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : Real)) (fun i => ‖z i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans hs

end

end Erdos1212Kernel
