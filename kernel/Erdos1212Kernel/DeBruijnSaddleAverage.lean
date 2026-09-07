import Erdos1212Kernel.DeBruijnF1Shift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.IntermediateValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The real restriction of the already-proved source phase derivative. -/
def deBruijnSaddleAverage (x : Real) : Real := ∫ t in (0 : Real)..1, Real.exp (t * x)

theorem deBruijnSaddleAverage_ofReal (x : Real) :
    (deBruijnSaddleAverage x : Complex) = deBruijnComplexExpAverage (x : Complex) := by
  unfold deBruijnSaddleAverage deBruijnComplexExpAverage
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  rw [Complex.ofReal_exp, Complex.ofReal_mul]

theorem deBruijnSaddleAverage_continuous : Continuous deBruijnSaddleAverage := by
  have hc : Continuous (fun x : Real => (deBruijnComplexExpAverage (x : Complex)).re) :=
    Complex.continuous_re.comp (deBruijnComplexExpAverage_continuous.comp Complex.continuous_ofReal)
  apply hc.congr
  intro x
  have h := congrArg Complex.re (deBruijnSaddleAverage_ofReal x)
  simpa only [Complex.ofReal_re] using h.symm

theorem deBruijnSaddleAverage_integrand_intervalIntegrable (x a b : Real) :
    IntervalIntegrable (fun t : Real => Real.exp (t * x)) volume a b :=
  (Real.continuous_exp.comp (continuous_id.mul_const x)).intervalIntegrable a b

theorem deBruijnSaddleAverage_zero : deBruijnSaddleAverage 0 = 1 := by
  simp [deBruijnSaddleAverage]

theorem deBruijnSaddleAverage_strictMono : StrictMono deBruijnSaddleAverage := by
  intro x y hxy
  have hx := deBruijnSaddleAverage_integrand_intervalIntegrable x 0 1
  have hy := deBruijnSaddleAverage_integrand_intervalIntegrable y 0 1
  have hi : IntervalIntegrable (fun t : Real => Real.exp (t * y) - Real.exp (t * x)) volume 0 1 := hy.sub hx
  have hp : 0 < ∫ t in (0 : Real)..1, Real.exp (t * y) - Real.exp (t * x) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hi _ (by norm_num)
    intro t ht
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy ht.1))
  rw [intervalIntegral.integral_sub hy hx] at hp
  exact sub_pos.mp hp

theorem deBruijnSaddleAverage_mul (x : Real) : x * deBruijnSaddleAverage x = Real.exp x - 1 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_one]
  rw [deBruijnSaddleAverage_ofReal]
  exact deBruijnComplexExpAverage_mul (x : Complex)

theorem deBruijnSaddleAverage_eq_quot {x : Real} (hx : x ≠ 0) :
    deBruijnSaddleAverage x = (Real.exp x - 1) / x := by
  apply (eq_div_iff hx).mpr
  simpa only [mul_comm] using deBruijnSaddleAverage_mul x

theorem deBruijnSaddleAverage_lower (x : Real) : 1 + x / 2 ≤ deBruijnSaddleAverage x := by
  have ht : IntervalIntegrable (fun t : Real => t * x) volume 0 1 := (continuous_id.mul_const x).intervalIntegrable 0 1
  have hc : IntervalIntegrable (fun _t : Real => (1 : Real)) volume 0 1 := _root_.intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : Real) ≤ 1) (ht.add hc)
    (deBruijnSaddleAverage_integrand_intervalIntegrable x 0 1) (fun t _ht => Real.add_one_le_exp (t * x))
  rw [intervalIntegral.integral_add ht hc, intervalIntegral.integral_mul_const] at h
  rw [integral_id, intervalIntegral.integral_const] at h
  norm_num at h
  change 1 / 2 * x + 1 ≤ deBruijnSaddleAverage x at h
  linarith

theorem deBruijnSaddleAverage_lt_exp {x : Real} (hx : 0 < x) : deBruijnSaddleAverage x < Real.exp x := by
  have hc : IntervalIntegrable (fun _t : Real => Real.exp x) volume 0 1 := _root_.intervalIntegrable_const
  have hi := deBruijnSaddleAverage_integrand_intervalIntegrable x 0 1
  have hp : 0 < ∫ t in (0 : Real)..1, Real.exp x - Real.exp (t * x) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.sub hi) _ (by norm_num)
    intro t ht
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_right ht.2 hx
  rw [intervalIntegral.integral_sub hc hi, intervalIntegral.integral_const] at hp
  simp only [sub_zero, one_smul] at hp
  exact sub_pos.mp hp

end

end Erdos1212Kernel
