import Erdos1212Kernel.IwaniecPrimeWeightedIntegral
import Mathlib.NumberTheory.Chebyshev

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- The positive negative-derivative kernel in RS 1962 (4.18),(4.20). -/
def iwaniecMertensThetaKernel (x : Real) : Real :=
  (1 + Real.log x) / (x ^ 2 * Real.log x ^ 2)

theorem iwaniecMertensThetaKernel_pos {x : Real} (hx : 1 < x) : 0 < iwaniecMertensThetaKernel x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  unfold iwaniecMertensThetaKernel
  positivity

theorem iwaniecLogKernel_hasDerivAt {x : Real} (hx : 1 < x) :
    HasDerivAt iwaniecLogKernel (-iwaniecMertensThetaKernel x) x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have h := (hasDerivAt_const x (1 : Real)).div ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne'))
    (mul_ne_zero hx0.ne' hlog.ne')
  apply h.congr_deriv
  simp only [Pi.mul_apply, id_eq]
  unfold iwaniecMertensThetaKernel
  field_simp [hx0.ne', hlog.ne']
  <;> ring

theorem iwaniecMertensThetaKernel_continuousOn :
    ContinuousOn iwaniecMertensThetaKernel (Set.Ioi (1 : Real)) := by
  intro x hx
  have hx0 : 0 < x := by linarith [hx.out]
  have hlog := Real.log_pos hx
  have hc : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_const.add hc).div ((continuousAt_id.pow 2).mul (hc.pow 2))
    (mul_ne_zero (pow_ne_zero 2 hx0.ne') (pow_ne_zero 2 hlog.ne'))

def iwaniecThetaPrimeCoefficient (n : Nat) : Real := if n.Prime then Real.log n else 0

theorem iwaniecThetaPrimeCoefficient_sum (x : Real) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, iwaniecThetaPrimeCoefficient n) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem iwaniecThetaPrimeCoefficient_zero : iwaniecThetaPrimeCoefficient 0 = 0 := by simp [iwaniecThetaPrimeCoefficient]

theorem iwaniecThetaPrimeCoefficient_one : iwaniecThetaPrimeCoefficient 1 = 0 := by simp [iwaniecThetaPrimeCoefficient]

def iwaniecPrimeReciprocalReal (x : Real) : Real := Erdos696.Mertens.primeReciprocalSum ⌊x⌋₊

theorem iwaniecPrimeReciprocalReal_nat (N : Nat) :
    iwaniecPrimeReciprocalReal N = Erdos696.Mertens.primeReciprocalSum N := by
  simp only [iwaniecPrimeReciprocalReal, Nat.floor_natCast]

theorem iwaniecPrimeReciprocalReal_weighted_theta (x : Real) :
    iwaniecPrimeReciprocalReal x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, iwaniecLogKernel n * iwaniecThetaPrimeCoefficient n := by
  unfold iwaniecPrimeReciprocalReal Erdos696.Mertens.primeReciprocalSum
  rw [Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold iwaniecThetaPrimeCoefficient
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hl : Real.log (n : Real) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    unfold iwaniecLogKernel
    field_simp [hn, hl]
  · simp only [if_neg hp, mul_zero]

end

end Erdos1212Kernel
