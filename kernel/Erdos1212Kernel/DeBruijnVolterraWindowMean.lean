import Erdos1212Kernel.DeBruijnVolterraWindowExtrema

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnVolterraPrimitive (f : Real → Real) (x : Real) : Real := ∫ t in (0 : Real)..x, f t

def deBruijnVolterraWindowMean (f : Real → Real) (x : Real) : Real := ∫ t in (x - 1)..x, f t

theorem deBruijnVolterra_intervalIntegrable {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact hf.mono (fun x hx => (le_min ha hb).trans hx.1)

theorem deBruijnVolterraPrimitive_hasDerivAt {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 0 < x) :
    HasDerivAt (deBruijnVolterraPrimitive f) (f x) x := by
  have hc : ContinuousOn f (Set.Ioi (0 : Real)) := hf.mono Set.Ioi_subset_Ici_self
  exact intervalIntegral.integral_hasDerivAt_right (deBruijnVolterra_intervalIntegrable hf le_rfl hx.le)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))

theorem deBruijnVolterraWindowMean_eq_primitive {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    deBruijnVolterraWindowMean f x = deBruijnVolterraPrimitive f x - deBruijnVolterraPrimitive f (x - 1) := by
  exact (intervalIntegral.integral_interval_sub_left
    (deBruijnVolterra_intervalIntegrable hf le_rfl (by linarith : 0 ≤ x))
    (deBruijnVolterra_intervalIntegrable hf le_rfl (by linarith : 0 ≤ x - 1))).symm

theorem deBruijnVolterraWindowMean_hasDerivAt {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 < x) :
    HasDerivAt (deBruijnVolterraWindowMean f) (f x - f (x - 1)) x := by
  have hshift : HasDerivAt (fun y : Real => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have h := (deBruijnVolterraPrimitive_hasDerivAt hf (by linarith : 0 < x)).sub
    ((deBruijnVolterraPrimitive_hasDerivAt hf (by linarith : 0 < x - 1)).comp x hshift)
  simp only [mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact deBruijnVolterraWindowMean_eq_primitive hf hy.le

theorem deBruijnVolterraWindowMean_continuousOn_segment {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {n : Real} (hn : 1 ≤ n) :
    ContinuousOn (deBruijnVolterraWindowMean f) (Set.Icc n (n + 2)) := by
  have hzero : (0 : Real) ∈ Set.uIcc (0 : Real) (n + 2) := Set.left_mem_uIcc
  have hP := intervalIntegral.continuousOn_primitive_interval'
    (deBruijnVolterra_intervalIntegrable hf le_rfl (by linarith : 0 ≤ n + 2)) hzero
  rw [Set.uIcc_of_le (show (0 : Real) ≤ n + 2 by linarith)] at hP
  have hp : ContinuousOn (deBruijnVolterraPrimitive f) (Set.Icc n (n + 2)) :=
    hP.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hnP : ContinuousOn (fun x : Real => deBruijnVolterraPrimitive f (x - 1)) (Set.Icc n (n + 2)) := by
    apply hP.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    change 0 ≤ x - 1 ∧ x - 1 ≤ n + 2
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply (hp.sub hnP).congr
  intro x hx
  exact deBruijnVolterraWindowMean_eq_primitive hf (hn.trans hx.1)

theorem deBruijnVolterraWindowMean_lag (f : Real → Real) (x : Real) :
    (∫ t in (0 : Real)..1, f (x - t)) = deBruijnVolterraWindowMean f x := by
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  rfl

theorem deBruijnVolterraWindowMean_bounds_of_bounds {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x m M : Real} (hx : 1 ≤ x)
    (hb : ∀ y ∈ Set.Icc (x - 1) x, m ≤ f y ∧ f y ≤ M) :
    m ≤ deBruijnVolterraWindowMean f x ∧ deBruijnVolterraWindowMean f x ≤ M := by
  have hi := deBruijnVolterra_intervalIntegrable hf (by linarith : 0 ≤ x - 1) (by linarith : 0 ≤ x)
  have hlo := intervalIntegral.integral_mono_on (by linarith : x - 1 ≤ x)
    (_root_.intervalIntegrable_const (c := m)) hi (fun y hy => (hb y hy).1)
  have hup := intervalIntegral.integral_mono_on (by linarith : x - 1 ≤ x)
    hi (_root_.intervalIntegrable_const (c := M)) (fun y hy => (hb y hy).2)
  simp only [intervalIntegral.integral_const, sub_sub_cancel, one_smul] at hlo hup
  exact ⟨hlo, hup⟩

theorem deBruijnVolterraWindowMean_bounds {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    deBruijnVolterraWindowMin f x ≤ deBruijnVolterraWindowMean f x ∧
      deBruijnVolterraWindowMean f x ≤ deBruijnVolterraWindowMax f x :=
  deBruijnVolterraWindowMean_bounds_of_bounds hf hx (deBruijnVolterraWindow_bounds hf hx)

end

end Erdos1212Kernel
