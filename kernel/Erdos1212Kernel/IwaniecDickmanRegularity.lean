import Erdos1212Kernel.IwaniecDickmanConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

def iwaniecDickmanApproxKernel (n : Nat) (s : Real) : Real := iwaniecDickmanApprox n (s - 1) / s

theorem iwaniecDickmanApproxKernel_continuousOn_of_approx (n : Nat)
    (hc : Continuous (iwaniecDickmanApprox n)) :
    ContinuousOn (iwaniecDickmanApproxKernel n) (Set.Ioi (0 : Real)) := by
  apply (hc.comp (continuous_id.sub continuous_const)).continuousOn.div continuousOn_id
  intro s hs
  exact (show 0 < s from hs).ne'

theorem iwaniecDickmanApproxKernel_intervalIntegrable (n : Nat)
    (hc : Continuous (iwaniecDickmanApprox n)) {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (iwaniecDickmanApproxKernel n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (iwaniecDickmanApproxKernel_continuousOn_of_approx n hc).mono
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hb) hs.1

theorem iwaniecDickmanApproxPrimitive_hasDerivAt (n : Nat)
    (hc : Continuous (iwaniecDickmanApprox n)) {s : Real} (hs : 0 < s) :
    HasDerivAt (fun t => ∫ x in (1 : Real)..t, iwaniecDickmanApproxKernel n x)
      (iwaniecDickmanApproxKernel n s) s := by
  have hk := iwaniecDickmanApproxKernel_continuousOn_of_approx n hc
  exact intervalIntegral.integral_hasDerivAt_right
    (iwaniecDickmanApproxKernel_intervalIntegrable n hc (by norm_num) hs)
    (hk.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hk.continuousAt (Ioi_mem_nhds hs))

theorem iwaniecDickmanApprox_continuous (n : Nat) : Continuous (iwaniecDickmanApprox n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      apply continuous_iff_continuousAt.mpr
      intro s
      have hm : 0 < max (1 : Real) s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hp := (iwaniecDickmanApproxPrimitive_hasDerivAt n ih hm).continuousAt
      have hmax : ContinuousAt (fun t : Real => max 1 t) s := continuousAt_const.max continuousAt_id
      exact continuousAt_const.sub (hp.comp hmax)

theorem iwaniecDickmanApprox_succ_hasDerivAt (n : Nat) {s : Real} (hs : 1 < s) :
    HasDerivAt (iwaniecDickmanApprox (n + 1)) (-iwaniecDickmanApprox n (s - 1) / s) s := by
  have hp := iwaniecDickmanApproxPrimitive_hasDerivAt n (iwaniecDickmanApprox_continuous n) (by linarith : 0 < s)
  have hmodel : HasDerivAt (fun t : Real => 1 - ∫ x in (1 : Real)..t, iwaniecDickmanApproxKernel n x)
      (-iwaniecDickmanApprox n (s - 1) / s) s := by
    simpa only [zero_sub, iwaniecDickmanApproxKernel, neg_div] using (hasDerivAt_const s (1 : Real)).sub hp
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  change (1 : Real) < t at ht
  simp only [iwaniecDickmanApprox, max_eq_right ht.le, iwaniecDickmanApproxKernel]

theorem iwaniecDickman_continuous : Continuous iwaniecDickman := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hceil := Nat.le_ceil s
  have heq := iwaniecDickman_eventuallyEq_approx ⌈s⌉₊ (by linarith)
  exact (iwaniecDickmanApprox_continuous ⌈s⌉₊).continuousAt.congr_of_eventuallyEq heq

theorem iwaniecDickman_hasDerivAt {s : Real} (hs : 1 < s) :
    HasDerivAt iwaniecDickman (-iwaniecDickman (s - 1) / s) s := by
  let n := ⌈s⌉₊
  have hceil : s ≤ (n : Real) := Nat.le_ceil s
  have heq := iwaniecDickman_eventuallyEq_approx (n + 1) (by push_cast; linarith)
  have hraw := (iwaniecDickmanApprox_succ_hasDerivAt n hs).congr_of_eventuallyEq heq
  rw [iwaniecDickman_eq_approx n (s := s - 1) (by linarith)]
  exact hraw

end

end Erdos1212Kernel
