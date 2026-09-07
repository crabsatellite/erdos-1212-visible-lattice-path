import Erdos1212Kernel.DeBruijnSaddleLogWindow

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

/-- The exact elementary exponent main term in source (1.8). -/
def deBruijnRhoLogMain (u : Real) : Real :=
  u * (Real.log u + Real.log (Real.log u) - 1 - 1 / Real.log u + Real.log (Real.log u) / Real.log u)

def deBruijnRhoLogMainDerivative (u : Real) : Real :=
  Real.log u + Real.log (Real.log u) + Real.log (Real.log u) / Real.log u +
    (2 - Real.log (Real.log u)) / (Real.log u) ^ 2

def deBruijnRhoLogErrorScale (u : Real) : Real :=
  u * ((Real.log (Real.log u)) ^ 2 / (Real.log u) ^ 2)

def deBruijnRhoLogErrorDerivative (u : Real) : Real :=
  ((Real.log (Real.log u)) ^ 2 / (Real.log u) ^ 2) * (1 - 2 / Real.log u) +
    2 * Real.log (Real.log u) / (Real.log u) ^ 3

theorem deBruijnRhoLogMain_hasDerivAt {u : Real} (hu : 1 < u) :
    HasDerivAt deBruijnRhoLogMain (deBruijnRhoLogMainDerivative u) u := by
  have hu0 : 0 < u := by linarith
  have hL0 := Real.log_pos hu
  have hL := Real.hasDerivAt_log hu0.ne'
  have hl := hL.log hL0.ne'
  have hinv := (hasDerivAt_const u (1 : Real)).div hL hL0.ne'
  have hquot := hl.div hL hL0.ne'
  have h := (hasDerivAt_id u).mul ((((hL.add hl).sub_const 1).sub hinv).add hquot)
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  unfold deBruijnRhoLogMainDerivative
  field_simp [hu0.ne', hL0.ne']
  <;> ring

theorem deBruijnRhoLogErrorScale_hasDerivAt {u : Real} (hu : 1 < u) :
    HasDerivAt deBruijnRhoLogErrorScale (deBruijnRhoLogErrorDerivative u) u := by
  have hu0 : 0 < u := by linarith
  have hL0 := Real.log_pos hu
  have hL := Real.hasDerivAt_log hu0.ne'
  have hl := hL.log hL0.ne'
  have h := (hasDerivAt_id u).mul ((hl.pow 2).div (hL.pow 2) (pow_ne_zero 2 hL0.ne'))
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  unfold deBruijnRhoLogErrorDerivative
  field_simp [hu0.ne', hL0.ne']
  <;> ring

theorem deBruijnRhoLogMainDerivative_continuousOn :
    ContinuousOn deBruijnRhoLogMainDerivative (Set.Ioi (1 : Real)) := by
  intro u hu
  have hu0 : 0 < u := by linarith [hu.out]
  have hL0 := Real.log_pos hu
  have hL : ContinuousAt Real.log u := Real.continuousAt_log hu0.ne'
  have hl : ContinuousAt (fun x : Real => Real.log (Real.log x)) u := (Real.continuousAt_log hL0.ne').comp hL
  apply ContinuousAt.continuousWithinAt
  unfold deBruijnRhoLogMainDerivative
  exact ((hL.add hl).add (hl.div hL hL0.ne')).add ((continuousAt_const.sub hl).div (hL.pow 2) (pow_ne_zero 2 hL0.ne'))

theorem deBruijnRhoLogErrorDerivative_continuousOn :
    ContinuousOn deBruijnRhoLogErrorDerivative (Set.Ioi (1 : Real)) := by
  intro u hu
  have hu0 : 0 < u := by linarith [hu.out]
  have hL0 := Real.log_pos hu
  have hL : ContinuousAt Real.log u := Real.continuousAt_log hu0.ne'
  have hl : ContinuousAt (fun x : Real => Real.log (Real.log x)) u := (Real.continuousAt_log hL0.ne').comp hL
  apply ContinuousAt.continuousWithinAt
  unfold deBruijnRhoLogErrorDerivative
  exact (((hl.pow 2).div (hL.pow 2) (pow_ne_zero 2 hL0.ne')).mul
    (continuousAt_const.sub (continuousAt_const.div hL hL0.ne'))).add
      ((continuousAt_const.mul hl).div (hL.pow 3) (pow_ne_zero 3 hL0.ne'))

end

end Erdos1212Kernel
