import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1000000

/-- `sigma=1` gives the paper's auxiliary W initial values; `sigma=-1`
gives its auxiliary M initial values. -/
def iwaniecAuxInitial (sigma s : Real) : Real :=
  (1 - sigma) + (s - 1)⁻¹ - Real.log (s - 1)

def iwaniecAuxBase (sigma s : Real) : Real :=
  iwaniecAuxInitial sigma (min s 3)

def iwaniecAuxDelayKernel (s : Real) : Real := s / (s - 1) ^ 2

/-- Method-of-steps construction of the literal delay equation.  Each
iteration propagates the original data only one unit farther. -/
def iwaniecAuxApprox (sigma : Real) : Nat → Real → Real
  | 0 => iwaniecAuxBase sigma
  | n + 1 => fun s => iwaniecAuxBase sigma s +
      sigma * ∫ t in (3 : Real)..(max 3 s),
        iwaniecAuxDelayKernel t * iwaniecAuxApprox sigma n (t - 1)

theorem iwaniecAuxApprox_stable_succ
    (sigma : Real) (n : Nat) {s : Real} (hs : s ≤ (n : Real) + 3) :
    iwaniecAuxApprox sigma (n + 1) s = iwaniecAuxApprox sigma n s := by
  induction n generalizing s with
  | zero => simp [iwaniecAuxApprox, max_eq_left (by simpa using hs)]
  | succ n ih =>
      change iwaniecAuxBase sigma s + sigma *
        (∫ t in (3 : Real)..(max 3 s),
          iwaniecAuxDelayKernel t * iwaniecAuxApprox sigma (n + 1) (t - 1)) =
        iwaniecAuxBase sigma s + sigma *
        (∫ t in (3 : Real)..(max 3 s),
          iwaniecAuxDelayKernel t * iwaniecAuxApprox sigma n (t - 1))
      apply congrArg (fun u : Real => iwaniecAuxBase sigma s + sigma * u)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (3 : Real) s)] at ht
      have hupper : max 3 s ≤ (n : Real) + 4 := by
        apply max_le
        · have hn : (0 : Real) ≤ n := by positivity
          linarith
        · push_cast at hs
          linarith
      dsimp only
      rw [ih (s := t - 1) (by have := ht.2.trans hupper; linarith)]

theorem iwaniecAuxApprox_stable
    (sigma : Real) {m n : Nat} (hmn : m ≤ n) {s : Real} (hs : s ≤ (m : Real) + 3) :
    iwaniecAuxApprox sigma n s = iwaniecAuxApprox sigma m s := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [iwaniecAuxApprox_stable_succ sigma n (by
        have hcast : (m : Real) ≤ n := by exact_mod_cast hmn
        linarith), ih]

/-- A total function whose restriction to the paper's domain `[2,infinity)`
will satisfy its displayed initial data and delay differential equation. -/
def iwaniecAuxFunction (sigma s : Real) : Real :=
  iwaniecAuxApprox sigma ⌈s⌉₊ s

theorem iwaniecAuxFunction_eq_approx
    (sigma : Real) (n : Nat) {s : Real} (hs : s ≤ (n : Real) + 3) :
    iwaniecAuxFunction sigma s = iwaniecAuxApprox sigma n s := by
  unfold iwaniecAuxFunction
  rcases le_total n ⌈s⌉₊ with hle | hge
  · exact iwaniecAuxApprox_stable sigma hle hs
  · symm
    apply iwaniecAuxApprox_stable sigma hge
    have hceil := Nat.le_ceil s
    linarith

theorem iwaniecAuxFunction_initial
    (sigma : Real) {s : Real} (hs : s ≤ 3) :
    iwaniecAuxFunction sigma s = iwaniecAuxInitial sigma s := by
  rw [iwaniecAuxFunction_eq_approx sigma 0 (by simpa using hs)]
  simp [iwaniecAuxApprox, iwaniecAuxBase, min_eq_left hs]

theorem iwaniecAuxFunction_eventuallyEq_approx
    (sigma : Real) (n : Nat) {s : Real} (hs : s < (n : Real) + 3) :
    iwaniecAuxFunction sigma =ᶠ[nhds s] iwaniecAuxApprox sigma n := by
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact iwaniecAuxFunction_eq_approx sigma n ht.le

def iwaniecAuxW : Real → Real := iwaniecAuxFunction 1

def iwaniecAuxM : Real → Real := iwaniecAuxFunction (-1)

theorem iwaniecAuxW_initial {s : Real} (hs : s ≤ 3) :
    iwaniecAuxW s = 1 / (s - 1) - Real.log (s - 1) := by
  unfold iwaniecAuxW
  rw [iwaniecAuxFunction_initial 1 hs]
  simp [iwaniecAuxInitial, one_div]

theorem iwaniecAuxM_initial {s : Real} (hs : s ≤ 3) :
    iwaniecAuxM s = 2 + 1 / (s - 1) - Real.log (s - 1) := by
  unfold iwaniecAuxM
  rw [iwaniecAuxFunction_initial (-1) hs]
  norm_num [iwaniecAuxInitial, one_div]

end

end Erdos1212Kernel
