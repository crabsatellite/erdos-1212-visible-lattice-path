import Erdos1212Kernel.TaoDyadicEndpointConditions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1800000

def taoZetaEulerKernel (s : Complex) (x : Real) : Complex :=
  (x : Complex) ^ (-s)

def taoZetaEulerKernelDerivative (s : Complex) (x : Real) : Complex :=
  (-s) * (x : Complex) ^ (-s - 1)

theorem taoZetaEulerKernel_hasDerivAt {s : Complex} {x : Real} (hs : s ≠ 0) (hx : 0 < x) :
    HasDerivAt (taoZetaEulerKernel s) (taoZetaEulerKernelDerivative s x) x := by
  exact hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

theorem taoZetaEulerKernelDerivative_norm {s : Complex} {x : Real} (hx : 0 < x) :
    ‖taoZetaEulerKernelDerivative s x‖ = ‖s‖ * x ^ (-s.re - 1) := by
  unfold taoZetaEulerKernelDerivative
  rw [Complex.norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 2 <;> simp

theorem taoZetaEulerKernelDerivative_norm_le {s : Complex} {n x : Real}
    (hs : 0 < s.re) (hn : 0 < n) (hnx : n ≤ x) :
    ‖taoZetaEulerKernelDerivative s x‖ ≤ ‖s‖ * n ^ (-s.re - 1) := by
  rw [taoZetaEulerKernelDerivative_norm (hn.trans_le hnx)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hn hnx (by linarith)) (norm_nonneg _)

theorem taoZetaEulerKernel_unit_difference {s : Complex} {n x : Real}
    (hs : 0 < s.re) (hn : 1 ≤ n) (hx : x ∈ Set.Icc n (n + 1)) :
    ‖taoZetaEulerKernel s n - taoZetaEulerKernel s x‖ ≤
      ‖s‖ * n ^ (-s.re - 1) := by
  have hnpos : 0 < n := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (taoZetaEulerKernel_hasDerivAt hs0 (hnpos.trans_le hy.1)).hasDerivWithinAt)
    (fun y hy => taoZetaEulerKernelDerivative_norm_le hs hnpos hy.1)
    (convex_Icc n (n + 1)) (Set.left_mem_Icc.mpr (by linarith)) hx
  have hdist : ‖x - n‖ ≤ (1 : Real) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hD : 0 ≤ ‖s‖ * n ^ (-s.re - 1) := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left hdist hD)
  simpa only [norm_sub_rev, mul_one] using h'

theorem taoZetaEulerKernel_unit_integral_error {s : Complex} {n : Real}
    (hs : 0 < s.re) (hn : 1 ≤ n) :
    ‖taoZetaEulerKernel s n - ∫ x in n..n + 1, taoZetaEulerKernel s x‖ ≤
      ‖s‖ * n ^ (-s.re - 1) := by
  have hnpos : 0 < n := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hcont : ContinuousOn (taoZetaEulerKernel s) (Set.Icc n (n + 1)) :=
    fun x hx => (taoZetaEulerKernel_hasDerivAt hs0 (hnpos.trans_le hx.1)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (taoZetaEulerKernel s) volume n (n + 1) :=
    hcont.intervalIntegrable_of_Icc (by linarith : n ≤ n + 1)
  have hid : (∫ x in n..n + 1, (taoZetaEulerKernel s n - taoZetaEulerKernel s x)) =
      taoZetaEulerKernel s n - ∫ x in n..n + 1, taoZetaEulerKernel s x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const]
    simp only [show n + 1 - n = 1 by ring, one_smul]
  rw [← hid]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := n) (b := n + 1) (C := ‖s‖ * n ^ (-s.re - 1))
    (fun x hx => by
      have hx' : x ∈ Set.Icc n (n + 1) := by
        rw [Set.uIoc_of_le (by linarith : n ≤ n + 1)] at hx
        exact ⟨hx.1.le, hx.2⟩
      exact taoZetaEulerKernel_unit_difference hs hn hx')
  simpa only [show |n + 1 - n| = 1 by rw [show n + 1 - n = 1 by ring, abs_one], mul_one] using hbound

end

end Erdos1212Kernel
