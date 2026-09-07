import Erdos1212Kernel.DeBruijnDickmanBoundaryKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn1951_exp_tail_scaled {a : Real} (ha : 0 < a) (R C : Real) :
    a * (∫ x in Set.Ioi R, C * Real.exp (-a * x)) = C * Real.exp (-a * R) := by
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (show -a < 0 by linarith)]
  field_simp [ha.ne'] <;> ring

theorem deBruijn1951BoundaryAverage_lower {a : Real} (ha : 0 < a) :
    Real.exp Real.eulerMascheroniConstant * Real.exp (-a) ≤ deBruijn1951BoundaryAverage a := by
  have hlo := (exp_neg_integrableOn_Ioi (1 : Real) ha).const_mul (Real.exp Real.eulerMascheroniConstant)
  have hi := setIntegral_mono_on hlo (deBruijn1951BoundaryKernel_integrable ha) measurableSet_Ioi
    (show ∀ x ∈ Set.Ioi (1 : Real),
      Real.exp Real.eulerMascheroniConstant * Real.exp (-a * x) ≤ deBruijn1951BoundaryKernel a x from by
      intro x hx
      have h := mul_le_mul_of_nonneg_left (deBruijn1951Phi_bounds (show 1 ≤ x from hx.le)).1
        (Real.exp_pos (-a * x)).le
      simpa only [deBruijn1951BoundaryKernel, mul_comm] using h)
  have h := mul_le_mul_of_nonneg_left hi ha.le
  rw [deBruijn1951_exp_tail_scaled ha] at h
  simpa only [mul_one, deBruijn1951BoundaryAverage] using h

theorem deBruijn1951BoundaryAverage_upper {a R : Real} (ha : 0 < a) (hR : 1 ≤ R) :
    deBruijn1951BoundaryAverage a ≤
      a * (deBruijn1951Phi 1 * (R - 1)) + deBruijn1951Phi R * Real.exp (-a * R) := by
  have hHeadCont : ContinuousOn (deBruijn1951BoundaryKernel a) (Set.Icc (1 : Real) R) := by
    apply (deBruijn1951BoundaryKernel_continuousOn a).mono
    intro x hx
    change (0 : Real) < x
    linarith [hx.1]
  have hHeadInt : IntervalIntegrable (deBruijn1951BoundaryKernel a) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hR] using hHeadCont
  have hTailInt : IntegrableOn (deBruijn1951BoundaryKernel a) (Set.Ioi R) :=
    (deBruijn1951BoundaryKernel_integrable ha).mono_set (Set.Ioi_subset_Ioi hR)
  have hHead : (∫ x in (1 : Real)..R, deBruijn1951BoundaryKernel a x) ≤ deBruijn1951Phi 1 * (R - 1) := by
    have hpoint : ∀ x ∈ Set.Icc (1 : Real) R, deBruijn1951BoundaryKernel a x ≤ deBruijn1951Phi 1 := by
      intro x hx
      have hphi := (deBruijn1951Phi_bounds hx.1).2
      have hexp : Real.exp (-a * x) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (show -a ≤ 0 by linarith) (show 0 ≤ x by linarith [hx.1]))
      unfold deBruijn1951BoundaryKernel
      exact (mul_le_mul_of_nonneg_left hphi (Real.exp_pos _).le).trans
        (mul_le_of_le_one_left (deBruijn1951Phi_pos (by norm_num : (0 : Real) < 1)).le hexp)
    have h := intervalIntegral.integral_mono_on hR hHeadInt
      (g := fun _x : Real => deBruijn1951Phi 1) _root_.intervalIntegrable_const hpoint
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hTail : a * (∫ x in Set.Ioi R, deBruijn1951BoundaryKernel a x) ≤
      deBruijn1951Phi R * Real.exp (-a * R) := by
    have hmajor := (exp_neg_integrableOn_Ioi R ha).const_mul (deBruijn1951Phi R)
    have hi := setIntegral_mono_on hTailInt hmajor measurableSet_Ioi
      (show ∀ x ∈ Set.Ioi R, deBruijn1951BoundaryKernel a x ≤ deBruijn1951Phi R * Real.exp (-a * x) from by
        intro x hx
        have hphi := deBruijn1951Phi_antitoneOn hR (hR.trans hx.le) hx.le
        have h := mul_le_mul_of_nonneg_left hphi (Real.exp_pos (-a * x)).le
        simpa only [deBruijn1951BoundaryKernel, mul_comm] using h)
    have h := mul_le_mul_of_nonneg_left hi ha.le
    rw [deBruijn1951_exp_tail_scaled ha] at h
    exact h
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hHeadInt hTailInt
  unfold deBruijn1951BoundaryAverage
  rw [← hsplit, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_left hHead ha.le) hTail

end

end Erdos1212Kernel
