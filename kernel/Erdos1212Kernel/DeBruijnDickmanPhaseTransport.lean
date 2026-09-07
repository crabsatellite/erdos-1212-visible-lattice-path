import Erdos1212Kernel.IwaniecBuchstabAdjointAsymptotics
import Erdos1212Kernel.DeBruijn1951RealDefinitions

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem deBruijnNegativeExpQuot_abs_le_one {t : Real} (ht : 0 < t) :
    |deBruijnNegativeExpQuot t| ≤ 1 := by
  unfold deBruijnNegativeExpQuot
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ ht]
    have h := Real.add_one_le_exp (-t)
    linarith
  · rw [div_le_iff₀ ht]
    have h := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)
    linarith

theorem deBruijnNegativeExpQuot_measurable : Measurable deBruijnNegativeExpQuot :=
  ((Real.measurable_exp.comp measurable_id.neg).sub_const 1).div measurable_id

theorem deBruijnNegativeExpQuot_intervalIntegrable {x : Real} (hx : 0 < x) :
    IntervalIntegrable deBruijnNegativeExpQuot volume 0 x := by
  have hi : IntervalIntegrable (fun _t : Real => (1 : Real)) volume 0 x := _root_.intervalIntegrable_const
  apply hi.mono_fun' deBruijnNegativeExpQuot_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le hx.le] at ht
  simpa only [Real.norm_eq_abs] using deBruijnNegativeExpQuot_abs_le_one ht.1

/-- Exact integration-by-parts transport to the previously checked 1950
normalization kernel. No identification by matching asymptotics is used. -/
theorem deBruijnPhi_eq_negative_integral {x : Real} (hx : 0 < x) :
    deBruijnPhi x = ∫ t in (0 : Real)..x, deBruijnNegativeExpQuot t := by
  have hc : ContinuousOn deBruijnPhi (Set.Icc (0 : Real) x) := by
    intro t ht
    rcases ht.1.eq_or_lt with heq | hpos
    · subst t
      exact deBruijnPhi_continuousWithinAt_zero.mono (fun _ hu => hu.1)
    · exact (deBruijnPhi_hasDerivAt hpos).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le hc
    (f' := deBruijnNegativeExpQuot) (fun t ht => deBruijnPhi_hasDerivAt ht.1)
    (deBruijnNegativeExpQuot_intervalIntegrable hx)
  have hz : deBruijnPhi 0 = 0 := by simp [deBruijnPhi]
  rw [hz, sub_zero] at h
  exact h.symm

theorem deBruijn1951ExpIntegral_neg {x : Real} (hx : 0 < x) :
    deBruijn1951ExpIntegral (-x) = deBruijnPhi x := by
  calc
    deBruijn1951ExpIntegral (-x) = -(∫ t in (-x)..(0 : Real), (Real.exp t - 1) / t) := by
      exact intervalIntegral.integral_symm (f := fun t : Real => (Real.exp t - 1) / t) (-x) 0
    _ = -(∫ t in (0 : Real)..x, (Real.exp (-t) - 1) / (-t)) := by
      have h := intervalIntegral.integral_comp_neg (fun t : Real => (Real.exp t - 1) / t) (a := 0) (b := x)
      simpa only [neg_zero] using congrArg (fun z : Real => -z) h.symm
    _ = ∫ t in (0 : Real)..x, deBruijnNegativeExpQuot t := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [deBruijnNegativeExpQuot, div_neg, neg_neg]
    _ = deBruijnPhi x := (deBruijnPhi_eq_negative_integral hx).symm

theorem deBruijn1951Phi_eq_inv_primitive {x : Real} (hx : 0 < x) :
    deBruijn1951Phi x = (deBruijnAdjointPrimitive x)⁻¹ := by
  rw [deBruijn1951Phi, deBruijn1951ExpIntegral_neg hx]
  simp only [deBruijnAdjointPrimitive, Real.exp_neg, mul_inv_rev, mul_comm]

/-- The exact normalization limit used immediately after (2.16). -/
theorem tendsto_deBruijn1951Phi : Tendsto deBruijn1951Phi atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h := tendsto_deBruijnAdjointPrimitive.inv₀ (Real.exp_pos (-Real.eulerMascheroniConstant)).ne'
  simp only [Real.exp_neg, inv_inv] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  exact (deBruijn1951Phi_eq_inv_primitive hx).symm

end

end Erdos1212Kernel
