import Erdos1212Kernel.DeBruijn1951RealDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnExpQuot (t : Real) : Real := (Real.exp t - 1) / t

theorem deBruijnExpQuot_measurable : Measurable deBruijnExpQuot :=
  (Real.measurable_exp.sub_const 1).div measurable_id

theorem deBruijnExpQuot_nonneg (t : Real) : 0 ≤ deBruijnExpQuot t := by
  unfold deBruijnExpQuot
  rcases le_total 0 t with ht | ht
  · exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)) ht
  · exact div_nonneg_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht)) ht

theorem deBruijnExpQuot_abs_le (t : Real) : |deBruijnExpQuot t| ≤ Real.exp |t| := by
  rw [abs_of_nonneg (deBruijnExpQuot_nonneg t)]
  by_cases ht : 0 < t
  · rw [abs_of_pos ht]
    unfold deBruijnExpQuot
    rw [div_le_iff₀ ht]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
    have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    rw [he] at h
    nlinarith
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    rcases hnonpos.eq_or_lt with rfl | hneg
    · norm_num [deBruijnExpQuot]
    · have hq : deBruijnExpQuot t ≤ 1 := by
        unfold deBruijnExpQuot
        rw [div_le_iff_of_neg hneg]
        linarith [Real.add_one_le_exp t]
      exact hq.trans (Real.one_le_exp_iff.mpr (abs_nonneg t))

theorem abs_le_abs_of_mem_zero_uIoc {x t : Real} (ht : t ∈ Set.uIoc (0 : Real) x) : |t| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · rw [Set.uIoc_of_le hx] at ht
    rw [abs_of_pos ht.1, abs_of_nonneg hx]
    exact ht.2
  · have hx0 : x ≤ 0 := (lt_of_not_ge hx).le
    rw [Set.uIoc_of_ge hx0] at ht
    rw [abs_of_nonpos ht.2, abs_of_nonpos hx0]
    linarith [ht.1]

theorem deBruijnExpQuot_intervalIntegrable_zero (x : Real) :
    IntervalIntegrable deBruijnExpQuot volume 0 x := by
  have hi : IntervalIntegrable (fun _t : Real => Real.exp |x|) volume 0 x := _root_.intervalIntegrable_const
  apply hi.mono_fun' deBruijnExpQuot_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have h := (deBruijnExpQuot_abs_le t).trans (Real.exp_le_exp.mpr (abs_le_abs_of_mem_zero_uIoc ht))
  simpa only [Real.norm_eq_abs] using h

theorem deBruijnExpQuot_intervalIntegrable (a b : Real) : IntervalIntegrable deBruijnExpQuot volume a b :=
  (deBruijnExpQuot_intervalIntegrable_zero a).symm.trans (deBruijnExpQuot_intervalIntegrable_zero b)

theorem deBruijn1951ExpIntegral_continuous : Continuous deBruijn1951ExpIntegral :=
  intervalIntegral.continuous_primitive deBruijnExpQuot_intervalIntegrable 0

theorem deBruijn1951ExpIntegral_sub (a b : Real) :
    deBruijn1951ExpIntegral b - deBruijn1951ExpIntegral a = ∫ t in a..b, deBruijnExpQuot t := by
  exact intervalIntegral.integral_interval_sub_left
    (deBruijnExpQuot_intervalIntegrable_zero b) (deBruijnExpQuot_intervalIntegrable_zero a)

theorem deBruijn1951ExpIntegral_abs_le {z : Real} (hz : |z| ≤ 1) :
    |deBruijn1951ExpIntegral z| ≤ Real.exp 1 * |z| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := z) (C := Real.exp 1) (f := deBruijnExpQuot) (by
      intro t ht
      have hb := (abs_le_abs_of_mem_zero_uIoc ht).trans hz
      simpa only [Real.norm_eq_abs] using (deBruijnExpQuot_abs_le t).trans (Real.exp_le_exp.mpr hb))
  simpa only [Real.norm_eq_abs, sub_zero, deBruijn1951ExpIntegral, deBruijnExpQuot] using h

theorem deBruijn1951ExpIntegral_symmetric_abs_le {z : Real} (hz : 0 ≤ z) (hzOne : z ≤ 1) :
    |deBruijn1951ExpIntegral z - deBruijn1951ExpIntegral (-z)| ≤ 2 * Real.exp 1 * z := by
  rw [deBruijn1951ExpIntegral_sub]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -z) (b := z) (C := Real.exp 1) (f := deBruijnExpQuot) (by
      intro t ht
      rw [Set.uIoc_of_le (show -z ≤ z by linarith)] at ht
      have hb : |t| ≤ 1 := (abs_le.mpr ⟨ht.1.le, ht.2⟩).trans hzOne
      simpa only [Real.norm_eq_abs] using (deBruijnExpQuot_abs_le t).trans (Real.exp_le_exp.mpr hb))
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ z - -z by linarith)] at h
  nlinarith

theorem deBruijnExpQuot_ge_half {t : Real} (ht : 0 ≤ t) : t / 2 ≤ deBruijnExpQuot t := by
  rcases ht.eq_or_lt with rfl | hpos
  · simp [deBruijnExpQuot]
  · unfold deBruijnExpQuot
    rw [le_div_iff₀ hpos]
    nlinarith [Real.quadratic_le_exp_of_nonneg ht]

/-- A quantitative real-axis lower bound for the exact source phase.
It supplies an integrable majorant, not the later saddle-point estimate. -/
theorem deBruijn1951ExpIntegral_quadratic_lower {z : Real} (hz : 0 ≤ z) :
    z ^ 2 / 4 ≤ deBruijn1951ExpIntegral z := by
  have hi := intervalIntegral.integral_mono_on hz
    ((continuous_id.div_const (2 : Real)).intervalIntegrable 0 z)
    (deBruijnExpQuot_intervalIntegrable_zero z) (fun t ht => deBruijnExpQuot_ge_half ht.1)
  rw [intervalIntegral.integral_div] at hi
  simp only [id_eq] at hi
  rw [integral_id] at hi
  change (z ^ 2 - (0 : Real) ^ 2) / 2 / 2 ≤ deBruijn1951ExpIntegral z at hi
  nlinarith

end

end Erdos1212Kernel
