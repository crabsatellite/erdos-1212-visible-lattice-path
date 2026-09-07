import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1000000

/-- Method of steps for the rho defined in Iwaniec's Lemma 9. Values at
nonpositive arguments are a constant totalization; all source consumers
use its restriction to nonnegative arguments. -/
def iwaniecDickmanApprox : Nat → Real → Real
  | 0 => fun _s => 1
  | n + 1 => fun s => 1 - ∫ t in (1 : Real)..(max 1 s), iwaniecDickmanApprox n (t - 1) / t

theorem iwaniecDickmanApprox_stable_succ (n : Nat) {s : Real} (hs : s ≤ (n : Real) + 1) :
    iwaniecDickmanApprox (n + 1) s = iwaniecDickmanApprox n s := by
  induction n generalizing s with
  | zero => simp [iwaniecDickmanApprox, max_eq_left (by simpa using hs)]
  | succ n ih =>
      change 1 - (∫ t in (1 : Real)..(max 1 s), iwaniecDickmanApprox (n + 1) (t - 1) / t) =
        1 - (∫ t in (1 : Real)..(max 1 s), iwaniecDickmanApprox n (t - 1) / t)
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (1 : Real) s)] at ht
      have hup : max (1 : Real) s ≤ (n : Real) + 2 := by
        apply max_le
        · have hn : (0 : Real) ≤ n := by positivity
          linarith
        · push_cast at hs
          linarith
      dsimp only
      rw [ih (s := t - 1) (by have := ht.2.trans hup; linarith)]

theorem iwaniecDickmanApprox_stable {m n : Nat} (hmn : m ≤ n) {s : Real} (hs : s ≤ (m : Real) + 1) :
    iwaniecDickmanApprox n s = iwaniecDickmanApprox m s := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [iwaniecDickmanApprox_stable_succ n (by
        have hcast : (m : Real) ≤ n := by exact_mod_cast hmn
        linarith), ih]

def iwaniecDickman (s : Real) : Real := iwaniecDickmanApprox ⌈s⌉₊ s

theorem iwaniecDickman_eq_approx (n : Nat) {s : Real} (hs : s ≤ (n : Real) + 1) :
    iwaniecDickman s = iwaniecDickmanApprox n s := by
  unfold iwaniecDickman
  rcases le_total n ⌈s⌉₊ with hle | hge
  · exact iwaniecDickmanApprox_stable hle hs
  · symm
    apply iwaniecDickmanApprox_stable hge
    have hceil := Nat.le_ceil s
    linarith

theorem iwaniecDickman_initial {s : Real} (hs : s ≤ 1) : iwaniecDickman s = 1 := by
  rw [iwaniecDickman_eq_approx 0 (by simpa using hs)]
  rfl

theorem iwaniecDickman_eventuallyEq_approx (n : Nat) {s : Real} (hs : s < (n : Real) + 1) :
    iwaniecDickman =ᶠ[nhds s] iwaniecDickmanApprox n := by
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact iwaniecDickman_eq_approx n ht.le

end

end Erdos1212Kernel
