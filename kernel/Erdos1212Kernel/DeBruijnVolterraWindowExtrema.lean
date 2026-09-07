import Erdos1212Kernel.DeBruijnVolterraRegularity
import Mathlib.MeasureTheory.Function.EssSup

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The paper's effective maximum and minimum, on the literal unit window. -/
def deBruijnVolterraWindowMax (f : Real → Real) (x : Real) : Real := essSup f (volume.restrict (Set.Icc (x - 1) x))

def deBruijnVolterraWindowMin (f : Real → Real) (x : Real) : Real := essInf f (volume.restrict (Set.Icc (x - 1) x))

def deBruijnVolterraOscillation (f : Real → Real) (x : Real) : Real :=
  deBruijnVolterraWindowMax f x - deBruijnVolterraWindowMin f x

theorem deBruijnVolterraWindow_measure_ne_zero (x : Real) :
    volume.restrict (Set.Icc (x - 1) x) ≠ 0 := by
  intro hzero
  have h := Measure.restrict_eq_zero.mp hzero
  rw [Real.volume_Icc] at h
  norm_num at h

theorem deBruijnVolterraWindow_continuousOn {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    ContinuousOn f (Set.Icc (x - 1) x) :=
  hf.mono (fun y hy => by change 0 ≤ y; linarith [hy.1])

theorem deBruijnVolterraWindow_boundedAbove {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Set.Icc (x - 1) x))) f :=
  BddAbove.isBoundedUnder (ae_restrict_mem measurableSet_Icc)
    (isCompact_Icc.bddAbove_image (deBruijnVolterraWindow_continuousOn hf hx))

theorem deBruijnVolterraWindow_boundedBelow {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    IsBoundedUnder (· ≥ ·) (ae (volume.restrict (Set.Icc (x - 1) x))) f :=
  BddBelow.isBoundedUnder (ae_restrict_mem measurableSet_Icc)
    (isCompact_Icc.bddBelow_image (deBruijnVolterraWindow_continuousOn hf hx))

theorem deBruijnVolterraWindow_bounds_ae {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    ∀ᵐ y ∂(volume.restrict (Set.Icc (x - 1) x)),
      deBruijnVolterraWindowMin f x ≤ f y ∧ f y ≤ deBruijnVolterraWindowMax f x :=
  (ae_essInf_le (deBruijnVolterraWindow_boundedBelow hf hx)).and
    (ae_le_essSup (deBruijnVolterraWindow_boundedAbove hf hx))

theorem deBruijnVolterraWindow_bounds {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    ∀ y ∈ Set.Icc (x - 1) x, deBruijnVolterraWindowMin f x ≤ f y ∧ f y ≤ deBruijnVolterraWindowMax f x :=
  deBruijn_continuous_bounds_of_ae_Icc (by linarith) (deBruijnVolterraWindow_continuousOn hf hx)
    (deBruijnVolterraWindow_bounds_ae hf hx)

theorem deBruijnVolterraWindow_future_bounds {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x : Real} (hx : 1 ≤ x) :
    ∀ y : Real, x - 1 ≤ y → deBruijnVolterraWindowMin f x ≤ f y ∧ f y ≤ deBruijnVolterraWindowMax f x := by
  intro y hy
  by_cases hxy : y ≤ x
  · exact deBruijnVolterraWindow_bounds hf hx y ⟨hy, hxy⟩
  · exact deBruijnRhoVolterra_continuous_regular hf heq x hx _ _
      (deBruijnVolterraWindow_bounds_ae hf hx) y (lt_of_not_ge hxy)

theorem deBruijnVolterraWindowMax_antitoneOn {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    AntitoneOn (deBruijnVolterraWindowMax f) (Set.Ici (1 : Real)) := by
  intro a ha b hb hab
  letI : NeZero (volume.restrict (Set.Icc (b - 1) b)) := ⟨deBruijnVolterraWindow_measure_ne_zero b⟩
  apply essSup_le_of_ae_le (deBruijnVolterraWindowMax f a) _
    (deBruijnVolterraWindow_boundedBelow hf hb).isCoboundedUnder_le
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact (deBruijnVolterraWindow_future_bounds hf heq ha y (by linarith [hy.1])).2

theorem deBruijnVolterraWindowMin_monotoneOn {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    MonotoneOn (deBruijnVolterraWindowMin f) (Set.Ici (1 : Real)) := by
  intro a ha b hb hab
  letI : NeZero (volume.restrict (Set.Icc (b - 1) b)) := ⟨deBruijnVolterraWindow_measure_ne_zero b⟩
  apply le_essInf_of_ae_le (deBruijnVolterraWindowMin f a) _
    (deBruijnVolterraWindow_boundedAbove hf hb).isCoboundedUnder_ge
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact (deBruijnVolterraWindow_future_bounds hf heq ha y (by linarith [hy.1])).1

theorem deBruijnVolterraOscillation_nonneg {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    0 ≤ deBruijnVolterraOscillation f x := by
  have hb := deBruijnVolterraWindow_bounds hf hx x ⟨by linarith, le_rfl⟩
  exact sub_nonneg.mpr (hb.1.trans hb.2)

theorem deBruijnVolterraOscillation_antitoneOn {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    AntitoneOn (deBruijnVolterraOscillation f) (Set.Ici (1 : Real)) := by
  intro a ha b hb hab
  exact sub_le_sub (deBruijnVolterraWindowMax_antitoneOn hf heq ha hb hab)
    (deBruijnVolterraWindowMin_monotoneOn hf heq ha hb hab)

end

end Erdos1212Kernel
