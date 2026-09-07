import Erdos1212Kernel.DeBruijnVolterraKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def DeBruijnRhoVolterraEquation (f : Real → Real) : Prop :=
  ∀ x : Real, 1 ≤ x → f x = ∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * f (x - t)

def deBruijnRhoSolutionRatio (F : Real → Real) (x : Real) : Real := F x / deBruijnRho x

theorem deBruijnRhoSolutionRatio_continuousOn {F : Real → Real}
    (hF : ContinuousOn F (Set.Ici (0 : Real))) :
    ContinuousOn (deBruijnRhoSolutionRatio F) (Set.Ici (0 : Real)) := by
  have hc : ContinuousOn (fun x : Real => F x / iwaniecDickman x) (Set.Ici (0 : Real)) :=
    hF.div iwaniecDickman_continuous.continuousOn (fun x hx => (iwaniecDickman_pos hx).ne')
  apply hc.congr
  intro x hx
  rw [deBruijnRhoSolutionRatio, deBruijnRho_eq_dickman hx]

/-- The exact transport (4.3), not a postulated ratio equation. -/
theorem deBruijnRhoSolutionRatio_equation {F : Real → Real}
    (hF : ∀ x : Real, 1 ≤ x → x * F x = ∫ t in (0 : Real)..1, F (x - t)) :
    DeBruijnRhoVolterraEquation (deBruijnRhoSolutionRatio F) := by
  intro x hx
  have hxPos : 0 < x := by linarith
  have hρ : deBruijnRho x ≠ 0 := by
    rw [deBruijnRho_eq_dickman hxPos.le]
    exact (iwaniecDickman_pos hxPos.le).ne'
  have hi : (∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * deBruijnRhoSolutionRatio F (x - t)) =
      ∫ t in (0 : Real)..1, F (x - t) / (x * deBruijnRho x) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
    have hρt : deBruijnRho (x - t) ≠ 0 := by
      rw [deBruijnRho_eq_dickman (by linarith [ht.2] : 0 ≤ x - t)]
      exact (iwaniecDickman_pos (by linarith [ht.2])).ne'
    dsimp only
    rw [deBruijnRhoVolterraKernel_source x ht, deBruijnRhoSolutionRatio]
    field_simp
  rw [hi, intervalIntegral.integral_div, ← hF x hx]
  unfold deBruijnRhoSolutionRatio
  field_simp

theorem deBruijnRhoVolterra_lag_continuousOn {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    ContinuousOn (fun t : Real => f (x - t)) (Set.Icc (0 : Real) 1) := by
  apply hf.comp (continuousOn_const.sub continuousOn_id)
  intro t ht
  change 0 ≤ x - t
  linarith [ht.2]

theorem deBruijnRhoVolterra_product_intervalIntegrable {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) {x : Real} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : Real => deBruijnRhoVolterraKernel x t * f (x - t)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using
    (deBruijnRhoVolterraKernel_continuousOn hx).mul (deBruijnRhoVolterra_lag_continuousOn hf hx)

theorem DeBruijnRhoVolterraEquation.neg {f : Real → Real} (hf : DeBruijnRhoVolterraEquation f) :
    DeBruijnRhoVolterraEquation (fun x : Real => -f x) := by
  intro x hx
  simp only [mul_neg, intervalIntegral.integral_neg, ← hf x hx]

theorem deBruijnRhoVolterra_gap_integral {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f)
    {x : Real} (hx : 1 ≤ x) (M : Real) :
    (∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * (M - f (x - t))) = M - f x := by
  have hiK := deBruijnRhoVolterraKernel_intervalIntegrable hx
  have hiF := deBruijnRhoVolterra_product_intervalIntegrable hf hx
  calc
    _ = ∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * M - deBruijnRhoVolterraKernel x t * f (x - t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * M) -
        ∫ t in (0 : Real)..1, deBruijnRhoVolterraKernel x t * f (x - t) :=
      intervalIntegral.integral_sub (hiK.mul_const M) hiF
    _ = M - f x := by rw [intervalIntegral.integral_mul_const, deBruijnRhoVolterraKernel_integral hx, one_mul, ← heq x hx]

end

end Erdos1212Kernel
