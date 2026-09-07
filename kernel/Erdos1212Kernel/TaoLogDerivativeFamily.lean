import Erdos1212Kernel.TaoVdcFull
import Erdos1212Kernel.TaoCorputLogPhase
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

def taoLogDerivativeCoeff (t : Real) : Nat → Real
  | 0 => -(t / (2 * Real.pi))
  | n + 1 => -(n + 1 : Real) * taoLogDerivativeCoeff t n

theorem taoLogDerivativeCoeff_zero (t : Real) :
    taoLogDerivativeCoeff t 0 = -(t / (2 * Real.pi)) := rfl

theorem taoLogDerivativeCoeff_succ (t : Real) (n : Nat) :
    taoLogDerivativeCoeff t (n + 1) = -(n + 1 : Real) * taoLogDerivativeCoeff t n := rfl

theorem taoLogDerivativeCoeff_abs (t : Real) (n : Nat) :
    |taoLogDerivativeCoeff t n| = (n.factorial : Real) * |t| / (2 * Real.pi) := by
  induction n with
  | zero =>
      simp only [taoLogDerivativeCoeff_zero, Nat.factorial_zero, Nat.cast_one, one_mul, abs_neg,
        abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
  | succ n ih =>
      rw [taoLogDerivativeCoeff_succ, abs_mul, abs_neg, ih, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (n : Real) + 1 := by positivity
      rw [abs_of_nonneg hn]
      ring

def taoLogDerivativeFamily (t : Real) : Nat → Real → Real
  | 0 => taoCorputLogPhase t
  | n + 1 => fun x => taoLogDerivativeCoeff t n * x ^ (-(n + 1 : Nat) : Int)

theorem taoLogDerivativeFamily_zero (t : Real) :
    taoLogDerivativeFamily t 0 = taoCorputLogPhase t := rfl

theorem taoLogDerivativeFamily_succ (t : Real) (n : Nat) (x : Real) :
    taoLogDerivativeFamily t (n + 1) x =
      taoLogDerivativeCoeff t n * x ^ (-(n + 1 : Nat) : Int) := rfl

theorem taoLogDerivativeFamily_hasDerivAt (t : Real) (j : Nat) {x : Real} (hx : 0 < x) :
    HasDerivAt (taoLogDerivativeFamily t j) (taoLogDerivativeFamily t (j + 1) x) x := by
  cases j with
  | zero =>
      have h := taoCorputLogPhase_hasDerivAt t hx
      apply h.congr_deriv
      simp only [taoLogDerivativeFamily_succ, taoLogDerivativeCoeff_zero]
      rw [zpow_neg, zpow_natCast]
      norm_num
      field_simp [Real.pi_ne_zero, hx.ne']
      <;> ring
  | succ n =>
      have h := (hasDerivAt_zpow (-(n + 1 : Nat) : Int) x (Or.inl hx.ne')).const_mul
        (taoLogDerivativeCoeff t n)
      apply h.congr_deriv
      change _ = taoLogDerivativeCoeff t (n + 1) * x ^ (-((n + 2 : Nat) : Int))
      have he : (-((n + 1 : Nat) : Int) - 1) = -((n + 2 : Nat) : Int) := by omega
      rw [he, taoLogDerivativeCoeff_succ]
      push_cast
      ring

end

end Erdos1212Kernel
