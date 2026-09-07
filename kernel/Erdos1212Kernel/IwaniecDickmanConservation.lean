import Erdos1212Kernel.IwaniecDickmanRegularity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

def iwaniecDickmanPrimitive (s : Real) : Real := ∫ x in (0 : Real)..s, iwaniecDickman x

theorem iwaniecDickmanPrimitive_hasDerivAt (s : Real) :
    HasDerivAt iwaniecDickmanPrimitive (iwaniecDickman s) s := by
  have hc : ContinuousOn iwaniecDickman (Set.univ : Set Real) := iwaniecDickman_continuous.continuousOn
  exact intervalIntegral.integral_hasDerivAt_right (iwaniecDickman_continuous.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter isOpen_univ s (Set.mem_univ s))
    iwaniecDickman_continuous.continuousAt

theorem iwaniecDickmanPrimitive_continuous : Continuous iwaniecDickmanPrimitive :=
  continuous_iff_continuousAt.mpr (fun s => (iwaniecDickmanPrimitive_hasDerivAt s).continuousAt)

theorem iwaniecDickmanPrimitive_window (s : Real) :
    iwaniecDickmanPrimitive s - iwaniecDickmanPrimitive (s - 1) =
      ∫ x in (s - 1)..s, iwaniecDickman x := by
  unfold iwaniecDickmanPrimitive
  exact intervalIntegral.integral_interval_sub_left
    (iwaniecDickman_continuous.intervalIntegrable 0 s) (iwaniecDickman_continuous.intervalIntegrable 0 (s - 1))

def iwaniecDickmanConservation (s : Real) : Real :=
  s * iwaniecDickman s - (iwaniecDickmanPrimitive s - iwaniecDickmanPrimitive (s - 1))

theorem iwaniecDickmanConservation_hasDerivAt {s : Real} (hs : 1 < s) :
    HasDerivAt iwaniecDickmanConservation 0 s := by
  have hprod := (hasDerivAt_id s).mul (iwaniecDickman_hasDerivAt hs)
  have hwindow := (iwaniecDickmanPrimitive_hasDerivAt s).sub
    ((iwaniecDickmanPrimitive_hasDerivAt (s - 1)).comp s ((hasDerivAt_id s).sub_const 1))
  have h := hprod.sub hwindow
  refine h.congr_deriv ?_
  simp only [id_eq, one_mul, mul_one]
  field_simp [show s ≠ 0 by linarith] <;> ring

theorem iwaniecDickmanConservation_continuous : Continuous iwaniecDickmanConservation :=
  (continuous_id.mul iwaniecDickman_continuous).sub
    (iwaniecDickmanPrimitive_continuous.sub
      (iwaniecDickmanPrimitive_continuous.comp (continuous_id.sub continuous_const)))

theorem iwaniecDickman_initial_integral : (∫ x in (0 : Real)..1, iwaniecDickman x) = 1 := by
  have h : (∫ x in (0 : Real)..1, iwaniecDickman x) = ∫ _x in (0 : Real)..1, (1 : Real) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (show (0 : Real) ≤ 1 by norm_num)] at hx
    exact iwaniecDickman_initial hx.2
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

theorem iwaniecDickmanConservation_one : iwaniecDickmanConservation 1 = 0 := by
  unfold iwaniecDickmanConservation
  rw [iwaniecDickmanPrimitive_window, iwaniecDickman_initial (by norm_num : (1 : Real) ≤ 1)]
  norm_num only [sub_self, one_mul]
  rw [iwaniecDickman_initial_integral]
  ring

theorem iwaniecDickmanConservation_zero {s : Real} (hs : 1 ≤ s) : iwaniecDickmanConservation s = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    iwaniecDickmanConservation_continuous.continuousOn
    (f' := fun _t : Real => 0) (fun t ht => iwaniecDickmanConservation_hasDerivAt ht.1)
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, iwaniecDickmanConservation_one, sub_zero] at h
  exact h.symm

theorem iwaniecDickman_window_identity {s : Real} (hs : 1 ≤ s) :
    s * iwaniecDickman s = ∫ x in (s - 1)..s, iwaniecDickman x := by
  have h := iwaniecDickmanConservation_zero hs
  unfold iwaniecDickmanConservation at h
  rw [iwaniecDickmanPrimitive_window] at h
  exact sub_eq_zero.mp h

theorem iwaniecDickman_window_average {s : Real} (hs : 1 ≤ s) :
    iwaniecDickman s = (1 / s) * ∫ x in (s - 1)..s, iwaniecDickman x := by
  have h := iwaniecDickman_window_identity hs
  rw [← h]
  field_simp [show s ≠ 0 by linarith]

end

end Erdos1212Kernel
