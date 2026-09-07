import Erdos1212Kernel.DeBruijnAdjointDensity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn_exp_upper_lipschitz {p q T : Real} (hp : p ≤ T) (hq : q ≤ T) :
    |Real.exp p - Real.exp q| ≤ Real.exp T * |p - q| := by
  have ordered : ∀ p q : Real, q ≤ p → p ≤ T →
      |Real.exp p - Real.exp q| ≤ Real.exp T * |p - q| := by
    intro p q hqp hpT
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hqp)), abs_of_nonneg (sub_nonneg.mpr hqp)]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (q - p)) (Real.exp_pos p).le
    have he : Real.exp p * Real.exp (q - p) = Real.exp q := by rw [← Real.exp_add]; congr 1 <;> ring
    rw [he] at h
    have hfirst : Real.exp p - Real.exp q ≤ Real.exp p * (p - q) := by nlinarith
    exact hfirst.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hpT) (sub_nonneg.mpr hqp))
  rcases le_total q p with hqp | hpq
  · exact ordered p q hqp hp
  · rw [abs_sub_comm (Real.exp p) (Real.exp q), abs_sub_comm p q]
    exact ordered q p hpq hq

theorem deBruijn1951_exponent_abs_le {u z M : Real} (hM : |u + 1| ≤ M) (hz : |z| ≤ 1) :
    |(u + 1) * z - deBruijn1951ExpIntegral z| ≤ (M + Real.exp 1) * |z| := by
  have hE := deBruijn1951ExpIntegral_abs_le hz
  have hmul := mul_le_mul_of_nonneg_right hM (abs_nonneg z)
  calc
    _ ≤ |(u + 1) * z| + |deBruijn1951ExpIntegral z| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((u + 1) * z) (-deBruijn1951ExpIntegral z)
    _ ≤ M * |z| + Real.exp 1 * |z| := by rw [abs_mul]; exact add_le_add hmul hE
    _ = _ := by ring

def deBruijn1951NearBound (M : Real) : Real := 2 * (M + Real.exp 1) * Real.exp (M + Real.exp 1)

theorem deBruijn1951SymmetricDensity_eq (u z : Real) :
    deBruijn1951SymmetricDensity u z =
      deBruijn1951AdjointDensity u z - deBruijn1951BoundaryKernel (u + 1) z := by
  have h : deBruijn1951SymmetricDensity u z =
      deBruijn1951AdjointDensity u z + deBruijn1951AdjointDensity u (-z) := by
    unfold deBruijn1951SymmetricDensity deBruijn1951AdjointDensity
    ring
  rw [deBruijn1951AdjointDensity_neg] at h
  simpa only [sub_eq_add_neg] using h

/-- Uniform boundedness after the source's symmetric pole cancellation.
The displayed quotient is not assigned an unproved removable value. -/
theorem deBruijn1951SymmetricDensity_abs_le {u z M : Real}
    (hM : |u + 1| ≤ M) (hz : z ∈ Set.Icc (0 : Real) 1) :
    |deBruijn1951SymmetricDensity u z| ≤ deBruijn1951NearBound M := by
  have hM0 : 0 ≤ M := (abs_nonneg (u + 1)).trans hM
  have hT : 0 < M + Real.exp 1 := add_pos_of_nonneg_of_pos hM0 (Real.exp_pos 1)
  rcases hz.1.eq_or_lt with rfl | hzPos
  · simp only [deBruijn1951SymmetricDensity, neg_zero, sub_self, zero_div, abs_zero]
    unfold deBruijn1951NearBound
    positivity
  · have hp := deBruijn1951_exponent_abs_le (u := u) (z := z) hM
      (by simpa only [abs_of_nonneg hz.1] using hz.2)
    have hn := deBruijn1951_exponent_abs_le (u := u) (z := -z) hM
      (by simpa only [abs_neg, abs_of_nonneg hz.1] using hz.2)
    rw [abs_of_nonneg hz.1] at hp
    rw [abs_neg, abs_of_nonneg hz.1] at hn
    have hscale : (M + Real.exp 1) * z ≤ M + Real.exp 1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 hT.le
    have hpUpper : (u + 1) * z - deBruijn1951ExpIntegral z ≤ M + Real.exp 1 :=
      (le_abs_self _).trans (hp.trans hscale)
    have hnUpper : (u + 1) * (-z) - deBruijn1951ExpIntegral (-z) ≤ M + Real.exp 1 :=
      (le_abs_self _).trans (hn.trans hscale)
    have hdiff : |((u + 1) * z - deBruijn1951ExpIntegral z) -
        ((u + 1) * (-z) - deBruijn1951ExpIntegral (-z))| ≤ 2 * (M + Real.exp 1) * z := by
      calc
        _ ≤ |(u + 1) * z - deBruijn1951ExpIntegral z| +
            |(u + 1) * (-z) - deBruijn1951ExpIntegral (-z)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le ((u + 1) * z - deBruijn1951ExpIntegral z)
              (-((u + 1) * (-z) - deBruijn1951ExpIntegral (-z)))
        _ ≤ (M + Real.exp 1) * z + (M + Real.exp 1) * z := add_le_add hp hn
        _ = _ := by ring
    have hExp := deBruijn_exp_upper_lipschitz hpUpper hnUpper
    have hmul := mul_le_mul_of_nonneg_left hdiff (Real.exp_pos (M + Real.exp 1)).le
    unfold deBruijn1951SymmetricDensity deBruijn1951AdjointNumerator
    rw [abs_div, abs_of_pos hzPos, div_le_iff₀ hzPos]
    calc
      _ ≤ Real.exp (M + Real.exp 1) *
          |((u + 1) * z - deBruijn1951ExpIntegral z) - ((u + 1) * (-z) - deBruijn1951ExpIntegral (-z))| := hExp
      _ ≤ Real.exp (M + Real.exp 1) * (2 * (M + Real.exp 1) * z) := hmul
      _ = _ := by unfold deBruijn1951NearBound; ring

theorem deBruijn1951SymmetricDensity_measurable (u : Real) : Measurable (deBruijn1951SymmetricDensity u) :=
  ((deBruijn1951AdjointNumerator_continuous u).measurable.sub
    ((deBruijn1951AdjointNumerator_continuous u).comp continuous_neg).measurable).div measurable_id

theorem deBruijn1951SymmetricDensity_intervalIntegrable (u : Real) :
    IntervalIntegrable (deBruijn1951SymmetricDensity u) volume 0 1 := by
  have hi : IntervalIntegrable (fun _z : Real => deBruijn1951NearBound |u + 1|) volume 0 1 :=
    _root_.intervalIntegrable_const
  apply hi.mono_fun' (deBruijn1951SymmetricDensity_measurable u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  rw [Set.uIoc_of_le (show (0 : Real) ≤ 1 by norm_num)] at hz
  simpa only [Real.norm_eq_abs] using deBruijn1951SymmetricDensity_abs_le (u := u) le_rfl ⟨hz.1.le, hz.2⟩

def deBruijn1951NearIntegral (u : Real) : Real := ∫ z in (0 : Real)..1, deBruijn1951SymmetricDensity u z

theorem deBruijn1951NearIntegral_abs_le {u M : Real} (hM : |u + 1| ≤ M) :
    |deBruijn1951NearIntegral u| ≤ deBruijn1951NearBound M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : Real)) (b := 1)
    (C := deBruijn1951NearBound M) (f := deBruijn1951SymmetricDensity u) (by
      intro z hz
      rw [Set.uIoc_of_le (show (0 : Real) ≤ 1 by norm_num)] at hz
      simpa only [Real.norm_eq_abs] using deBruijn1951SymmetricDensity_abs_le hM ⟨hz.1.le, hz.2⟩)
  simpa only [deBruijn1951NearIntegral, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

end

end Erdos1212Kernel
