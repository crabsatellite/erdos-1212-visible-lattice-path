import Erdos1212Kernel.IwaniecRootLogDecay

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def iwaniecThetaDecayMajorant (a t : Real) : Real :=
  t * iwaniecRootLogDecay a t * iwaniecMertensThetaKernel t

theorem iwaniec_exp_one_range {x : Real} (hx : Real.exp 1 ≤ x) : 1 < x ∧ 1 ≤ Real.log x := by
  constructor
  · exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : Real) < 1)).trans_le hx
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx

theorem iwaniecThetaDecayMajorant_nonneg (a : Real) {t : Real} (ht : 1 < t) :
    0 ≤ iwaniecThetaDecayMajorant a t := by
  have ht0 : 0 ≤ t := by linarith
  exact mul_nonneg (mul_nonneg ht0 (iwaniecRootLogDecay_pos a t).le) (iwaniecMertensThetaKernel_pos ht).le

theorem iwaniecThetaDecayMajorant_measurable (a : Real) : Measurable (iwaniecThetaDecayMajorant a) := by
  unfold iwaniecThetaDecayMajorant iwaniecRootLogDecay iwaniecMertensThetaKernel
  fun_prop

theorem iwaniecThetaDecayMajorant_pointwise (a : Real) {t : Real} (ht : Real.exp 1 ≤ t) :
    iwaniecThetaDecayMajorant a t ≤ 2 * iwaniecRootLogDensity a t := by
  obtain ⟨ht1, hL⟩ := iwaniec_exp_one_range ht
  have ht0 : 0 < t := by linarith
  have hL0 := Real.log_pos ht1
  have hv0 := Real.sqrt_pos.mpr hL0
  have hv1 : 1 ≤ Real.sqrt (Real.log t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hvL : Real.sqrt (Real.log t) ≤ Real.log t := by
    nlinarith [Real.sq_sqrt hL0.le, sq_nonneg (Real.sqrt (Real.log t) - 1)]
  have hscalar : (1 + Real.log t) / (Real.log t) ^ 2 ≤ 2 / Real.sqrt (Real.log t) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hv0).mpr
    have h1 := mul_le_mul_of_nonneg_right (show 1 + Real.log t ≤ 2 * Real.log t by linarith) hv0.le
    have h2 := mul_le_mul_of_nonneg_left hvL (show 0 ≤ 2 * Real.log t by positivity)
    nlinarith
  calc
    _ = (iwaniecRootLogDecay a t / t) * ((1 + Real.log t) / (Real.log t) ^ 2) := by
      unfold iwaniecThetaDecayMajorant iwaniecMertensThetaKernel
      field_simp [ht0.ne']
    _ ≤ (iwaniecRootLogDecay a t / t) * (2 / Real.sqrt (Real.log t)) :=
      mul_le_mul_of_nonneg_left hscalar (div_nonneg (iwaniecRootLogDecay_pos a t).le ht0.le)
    _ = _ := by unfold iwaniecRootLogDensity; ring

theorem iwaniecThetaDecayMajorant_integrable {a x : Real} (ha : 0 < a) (hx : Real.exp 1 ≤ x) :
    IntegrableOn (iwaniecThetaDecayMajorant a) (Set.Ioi x) := by
  have hi := (iwaniecRootLogDensity_integrable ha (iwaniec_exp_one_range hx).1).const_mul 2
  apply hi.mono' (iwaniecThetaDecayMajorant_measurable a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htExp : Real.exp 1 ≤ t := hx.trans ht.le
  rw [Real.norm_eq_abs, abs_of_nonneg (iwaniecThetaDecayMajorant_nonneg a (iwaniec_exp_one_range htExp).1)]
  exact iwaniecThetaDecayMajorant_pointwise a htExp

/-- The actual theta-to-Mertens kernel has a rate-preserving tail bound:
the coefficient a in the exponential remains exactly a. -/
theorem iwaniecThetaDecayMajorant_integral_bound {a x : Real} (ha : 0 < a) (hx : Real.exp 1 ≤ x) :
    (∫ t in Set.Ioi x, iwaniecThetaDecayMajorant a t) ≤ (4 / a) * iwaniecRootLogDecay a x := by
  have hi := iwaniecThetaDecayMajorant_integrable ha hx
  have hj := (iwaniecRootLogDensity_integrable ha (iwaniec_exp_one_range hx).1).const_mul 2
  have h := MeasureTheory.integral_mono_ae hi hj (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact iwaniecThetaDecayMajorant_pointwise a (hx.trans ht.le))
  rw [MeasureTheory.integral_const_mul, iwaniecRootLogDensity_integral ha (iwaniec_exp_one_range hx).1] at h
  convert h using 1 <;> ring

theorem iwaniecThetaDecayMajorant_finite_bound {a x y : Real} (ha : 0 < a) (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, iwaniecThetaDecayMajorant a t) ≤ (4 / a) * iwaniecRootLogDecay a x := by
  have hi := iwaniecThetaDecayMajorant_integrable ha hx
  rw [intervalIntegral.integral_of_le hxy]
  apply (setIntegral_mono_set hi _ _).trans (iwaniecThetaDecayMajorant_integral_bound ha hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact iwaniecThetaDecayMajorant_nonneg a ((iwaniec_exp_one_range hx).1.trans ht)
  · exact Filter.Eventually.of_forall (fun t ht => ht.1)

theorem iwaniecThetaDecayMajorant_intervalIntegrable {a x y : Real} (ha : 0 < a) (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (iwaniecThetaDecayMajorant a) volume x y := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr
  exact (iwaniecThetaDecayMajorant_integrable ha hx).mono_set Set.Ioc_subset_Ioi_self

end

end Erdos1212Kernel
