import Erdos1212Kernel.IwaniecAuxiliaryUniqueness
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def iwaniecPrimitiveTwo (f : Real → Real) (s : Real) : Real := ∫ x in (2 : Real)..s, f x

theorem iwaniecIntervalIntegrable_of_continuousOn_one
    (f : Real → Real) (hcont : ContinuousOn f (Set.Ioi (1 : Real)))
    {a b : Real} (ha : 1 < a) (hb : 1 < b) : IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hcont.mono
  intro x hx
  exact lt_of_lt_of_le (lt_min ha hb) hx.1

theorem iwaniecPrimitiveTwo_hasDerivAt
    (f : Real → Real) (hcont : ContinuousOn f (Set.Ioi (1 : Real)))
    {s : Real} (hs : 1 < s) : HasDerivAt (iwaniecPrimitiveTwo f) (f s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    (iwaniecIntervalIntegrable_of_continuousOn_one f hcont (by norm_num) hs)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hcont.continuousAt (Ioi_mem_nhds hs))

def iwaniecPrimitiveWindow (f : Real → Real) (s : Real) : Real :=
  iwaniecPrimitiveTwo f s - iwaniecPrimitiveTwo f (s - 1)

theorem iwaniecPrimitiveWindow_eq_integral
    (f : Real → Real) (hcont : ContinuousOn f (Set.Ioi (1 : Real)))
    {s : Real} (hs : 2 < s) :
    iwaniecPrimitiveWindow f s = ∫ x in (s - 1)..s, f x := by
  exact intervalIntegral.integral_interval_sub_left
    (iwaniecIntervalIntegrable_of_continuousOn_one f hcont (by norm_num) (by linarith))
    (iwaniecIntervalIntegrable_of_continuousOn_one f hcont (by norm_num) (by linarith))

theorem iwaniecPrimitiveWindow_hasDerivAt
    (f : Real → Real) (hcont : ContinuousOn f (Set.Ioi (1 : Real)))
    {s : Real} (hs : 2 < s) :
    HasDerivAt (iwaniecPrimitiveWindow f) (f s - f (s - 1)) s := by
  have hright := iwaniecPrimitiveTwo_hasDerivAt f hcont (by linarith : 1 < s)
  have hleft := (iwaniecPrimitiveTwo_hasDerivAt f hcont
    (by linarith : 1 < s - 1)).comp s ((hasDerivAt_id s).sub_const 1)
  simpa only [mul_one] using hright.sub hleft

def iwaniecAuxWWindowKernel (s : Real) : Real := iwaniecAuxW s / s ^ 2

def iwaniecAuxMWindowWeight (s : Real) : Real := 1 - 1 / (2 * s ^ 2)

def iwaniecAuxMWindowKernel (s : Real) : Real := iwaniecAuxMWindowWeight s * iwaniecAuxM s

def iwaniecAuxMCoefficient (s : Real) : Real := ((s - 1) ^ 2 - 1 / 2) / s

theorem iwaniecAuxMCoefficient_hasDerivAt {s : Real} (hs : s ≠ 0) :
    HasDerivAt iwaniecAuxMCoefficient (iwaniecAuxMWindowWeight s) s := by
  have hnum := (((hasDerivAt_id s).sub_const 1).pow 2).sub_const (1 / 2 : Real)
  have hraw := hnum.div (hasDerivAt_id s) hs
  refine hraw.congr_deriv ?_
  unfold iwaniecAuxMWindowWeight
  simp only [Pi.pow_apply, id_eq]
  field_simp [hs]
  ring

theorem iwaniecAuxWWindowKernel_continuousOn :
    ContinuousOn iwaniecAuxWWindowKernel (Set.Ioi (1 : Real)) := by
  apply (iwaniecAuxFunction_continuousOn 1).div (continuousOn_id.pow 2)
  intro s hs
  have hsOne : 1 < s := hs
  exact pow_ne_zero 2 (show s ≠ 0 by linarith)

theorem iwaniecAuxMWindowKernel_continuousOn :
    ContinuousOn iwaniecAuxMWindowKernel (Set.Ioi (1 : Real)) := by
  have hweight : ContinuousOn iwaniecAuxMWindowWeight (Set.Ioi (1 : Real)) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
    intro s hs
    have hsOne : 1 < s := hs
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (show s ≠ 0 by linarith))
  exact hweight.mul (iwaniecAuxFunction_continuousOn (-1))

def iwaniecAuxWConservation (s : Real) : Real :=
  iwaniecAuxW s / s + iwaniecPrimitiveWindow iwaniecAuxWWindowKernel s

def iwaniecAuxMConservation (s : Real) : Real :=
  iwaniecAuxMCoefficient s * iwaniecAuxM s -
    iwaniecPrimitiveWindow iwaniecAuxMWindowKernel s

theorem iwaniecAuxWConservation_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxWConservation 0 s := by
  have hdiv := (iwaniecAuxW_hasDerivAt hs).div (hasDerivAt_id s)
    (by linarith : s ≠ 0)
  have hwindow := iwaniecPrimitiveWindow_hasDerivAt iwaniecAuxWWindowKernel
    iwaniecAuxWWindowKernel_continuousOn (by linarith : 2 < s)
  have hraw := hdiv.add hwindow
  refine hraw.congr_deriv ?_
  unfold iwaniecAuxWWindowKernel
  simp only [id_eq]
  field_simp [show s ≠ 0 by linarith, show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecAuxMConservation_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxMConservation 0 s := by
  have hprod := (iwaniecAuxMCoefficient_hasDerivAt (by linarith : s ≠ 0)).mul
    (iwaniecAuxM_hasDerivAt hs)
  have hwindow := iwaniecPrimitiveWindow_hasDerivAt iwaniecAuxMWindowKernel
    iwaniecAuxMWindowKernel_continuousOn (by linarith : 2 < s)
  have hraw := hprod.sub hwindow
  refine hraw.congr_deriv ?_
  unfold iwaniecAuxMCoefficient iwaniecAuxMWindowKernel iwaniecAuxMWindowWeight
  field_simp [show s ≠ 0 by linarith, show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecAuxWConservation_continuousOn :
    ContinuousOn iwaniecAuxWConservation (Set.Ici (3 : Real)) := by
  intro s hs
  have hsThree : 3 ≤ s := hs
  have hW := (iwaniecAuxFunction_continuousOn 1).continuousAt
    (Ioi_mem_nhds (show (1 : Real) < s by linarith))
  have hwindow := (iwaniecPrimitiveWindow_hasDerivAt iwaniecAuxWWindowKernel
    iwaniecAuxWWindowKernel_continuousOn (show 2 < s by linarith)).continuousAt
  exact ((hW.div continuousAt_id (by linarith : s ≠ 0)).add hwindow).continuousWithinAt

theorem iwaniecAuxMConservation_continuousOn :
    ContinuousOn iwaniecAuxMConservation (Set.Ici (3 : Real)) := by
  intro s hs
  have hsThree : 3 ≤ s := hs
  have hM := (iwaniecAuxFunction_continuousOn (-1)).continuousAt
    (Ioi_mem_nhds (show (1 : Real) < s by linarith))
  have hcoeff := (iwaniecAuxMCoefficient_hasDerivAt (by linarith : s ≠ 0)).continuousAt
  have hwindow := (iwaniecPrimitiveWindow_hasDerivAt iwaniecAuxMWindowKernel
    iwaniecAuxMWindowKernel_continuousOn (show 2 < s by linarith)).continuousAt
  exact ((hcoeff.mul hM).sub hwindow).continuousWithinAt

end

end Erdos1212Kernel
