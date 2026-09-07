import Erdos1212Kernel.IwaniecLogReciprocalChange

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecReciprocalLogConstantWeight (L x : Real) : Real :=
  iwaniecReciprocalLogWeight L (fun _t => 1) x

theorem iwaniecReciprocalLogConstantWeight_eq
    (L x : Real) :
    iwaniecReciprocalLogConstantWeight L x =
      (L - Real.log x)⁻¹ := by
  unfold iwaniecReciprocalLogConstantWeight iwaniecReciprocalLogWeight
  simp [one_div]

theorem iwaniecReciprocalLogConstantWeight_pos
    {L x : Real} (hx : x ∈ Set.Ioo (1 : Real) (Real.exp L)) :
    0 < iwaniecReciprocalLogConstantWeight L x := by
  rw [iwaniecReciprocalLogConstantWeight_eq]
  apply inv_pos.mpr
  exact sub_pos.mpr ((Real.log_lt_iff_lt_exp (zero_lt_one.trans hx.1)).2 hx.2)

theorem iwaniecReciprocalLogConstantWeight_continuousOn
    (L : Real) :
    ContinuousOn (iwaniecReciprocalLogConstantWeight L)
      (Set.Ioo (1 : Real) (Real.exp L)) := by
  intro x hx
  rw [show iwaniecReciprocalLogConstantWeight L =
      (fun y : Real => (L - Real.log y)⁻¹) by
    funext y
    exact iwaniecReciprocalLogConstantWeight_eq L y]
  have hxPos : 0 < x := zero_lt_one.trans hx.1
  have hdenPos : 0 < L - Real.log x :=
    sub_pos.mpr ((Real.log_lt_iff_lt_exp hxPos).2 hx.2)
  exact (continuousAt_const.sub (Real.continuousAt_log hxPos.ne')).inv₀
    hdenPos.ne' |>.continuousWithinAt

theorem iwaniecReciprocalLogConstantWeight_monotoneOn
    (L : Real) :
    MonotoneOn (iwaniecReciprocalLogConstantWeight L)
      (Set.Ioo (1 : Real) (Real.exp L)) := by
  intro x hx y hy hxy
  rw [iwaniecReciprocalLogConstantWeight_eq,
    iwaniecReciprocalLogConstantWeight_eq]
  have hxPos : 0 < x := zero_lt_one.trans hx.1
  have hyPos : 0 < y := zero_lt_one.trans hy.1
  have hlog : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxPos hyPos hxy
  have hdenYPos : 0 < L - Real.log y :=
    sub_pos.mpr ((Real.log_lt_iff_lt_exp hyPos).2 hy.2)
  exact inv_anti₀ hdenYPos (sub_le_sub_left hlog L)

theorem iwaniecReciprocalLogConstantWeight_nonnegOn
    (L : Real) :
    ∀ x ∈ Set.Ioo (1 : Real) (Real.exp L),
      0 ≤ iwaniecReciprocalLogConstantWeight L x := by
  intro x hx
  exact (iwaniecReciprocalLogConstantWeight_pos hx).le

/-- Exact evaluation at arbitrary real endpoints inside `(1, exp L)`.  The
parameters are the paper's `alpha = L/log A`, `beta = L/log B`. -/
theorem iwaniecWeightedLogKernelIntegral_constantWeight_eval
    {L B A : Real} (hL : 0 < L) (hB : 1 < B)
    (hBA : B ≤ A) (hA : A < Real.exp L) :
    iwaniecWeightedLogKernelIntegral
        (iwaniecReciprocalLogConstantWeight L) B A =
      L⁻¹ * Real.log
        (((L / Real.log B) - 1) / ((L / Real.log A) - 1)) := by
  have hAOne : 1 < A := hB.trans_le hBA
  have hlogBPos : 0 < Real.log B := Real.log_pos hB
  have hlogAPos : 0 < Real.log A := Real.log_pos hAOne
  have hlogAL : Real.log A < L :=
    (Real.log_lt_iff_lt_exp (zero_lt_one.trans hAOne)).2 hA
  have hlogBL : Real.log B < L :=
    (Real.log_le_log (zero_lt_one.trans hB) hBA).trans_lt hlogAL
  let alpha := L / Real.log A
  let beta := L / Real.log B
  have halpha : 1 < alpha := by
    dsimp [alpha]
    exact (lt_div_iff₀ hlogAPos).2 (by simpa using hlogAL)
  have hab : alpha ≤ beta := by
    dsimp [alpha, beta]
    rw [div_le_div_iff₀ hlogAPos hlogBPos]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (zero_lt_one.trans hB) hBA) hL.le
  have hscaleA : iwaniecExpReciprocalScale L alpha = A := by
    unfold iwaniecExpReciprocalScale
    dsimp [alpha]
    have hlogAne : Real.log A ≠ 0 := hlogAPos.ne'
    have hquot : L / (L / Real.log A) = Real.log A := by
      field_simp [hL.ne', hlogAne]
    rw [hquot]
    rw [Real.exp_log (zero_lt_one.trans hAOne)]
  have hscaleB : iwaniecExpReciprocalScale L beta = B := by
    unfold iwaniecExpReciprocalScale
    dsimp [beta]
    have hlogBne : Real.log B ≠ 0 := hlogBPos.ne'
    have hquot : L / (L / Real.log B) = Real.log B := by
      field_simp [hL.ne', hlogBne]
    rw [hquot]
    rw [Real.exp_log (zero_lt_one.trans hB)]
  have hchange := iwaniecWeightedLogKernelIntegral_reciprocalLog_constant
    hL halpha hab
  unfold iwaniecReciprocalLogConstantWeight
  rw [hscaleB, hscaleA] at hchange
  simpa [alpha, beta] using hchange

end

end Erdos1212Kernel
