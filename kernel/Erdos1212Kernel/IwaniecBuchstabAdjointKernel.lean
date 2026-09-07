import Erdos1212Kernel.IwaniecSieveSeriesLocalFormula
import Erdos1212Kernel.Analytic.BrunTitchmarsh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

/-!
# de Bruijn's adjoint kernel for the Buchstab limit

This is the purely analytic normalization used in de Bruijn 1950, Section 4.
The definition below is an integration-by-parts normal form of

`phi(x) = integral 0..x ((exp (-t) - 1) / t) dt`.

It avoids assigning an artificial value to the removable singularity at zero,
while retaining the exact derivative and limit required by the paper.
-/

def deBruijnLogDensity (t : Real) : Real :=
  Real.log t * Real.exp (-t)

def deBruijnPhi (x : Real) : Real :=
  Real.exp (-x) * Real.log x +
    (∫ t in (0 : Real)..x, deBruijnLogDensity t) - Real.log x

def deBruijnAdjointPrimitive (x : Real) : Real :=
  x * Real.exp (deBruijnPhi x)

theorem tendsto_exp_neg_mul_log_atTop :
    Tendsto (fun x : Real => Real.exp (-x) * Real.log x)
      atTop (nhds 0) := by
  refine squeeze_zero_norm' (a := fun x : Real => x * Real.exp (-x)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hxPos : 0 < x := zero_lt_one.trans_le hx
    have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogLe : Real.log x ≤ x :=
      (Real.log_le_sub_one_of_pos hxPos).trans (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) hlogNonneg)]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hlogLe (Real.exp_nonneg (-x)))
  · simpa [pow_one, mul_comm] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)

theorem tendsto_deBruijnLogDensity_intervalIntegral :
    Tendsto (fun x : Real => ∫ t in (0 : Real)..x, deBruijnLogDensity t)
      atTop (nhds (-Real.eulerMascheroniConstant)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (f := deBruijnLogDensity)
    (0 : Real) (by
      simpa [deBruijnLogDensity] using
        Erdos696.Mertens.integrable_log_mul_exp_neg)
    tendsto_id
  simpa [deBruijnLogDensity, Erdos696.Mertens.gamma_integral] using h

/-- de Bruijn 1950, the limit immediately before the last display in Section 4. -/
theorem tendsto_deBruijnPhi_add_log :
    Tendsto (fun x : Real => deBruijnPhi x + Real.log x)
      atTop (nhds (-Real.eulerMascheroniConstant)) := by
  have h := tendsto_exp_neg_mul_log_atTop.add
    tendsto_deBruijnLogDensity_intervalIntegral
  convert h using 1
  · ext x
    simp [deBruijnPhi]
  · ring

/-- The adjoint primitive tends to the Buchstab normalization constant. -/
theorem tendsto_deBruijnAdjointPrimitive :
    Tendsto deBruijnAdjointPrimitive atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h : Tendsto
      (fun x : Real => Real.exp (deBruijnPhi x + Real.log x)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      tendsto_deBruijnPhi_add_log
  exact Filter.Tendsto.congr' (by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    show Real.exp (deBruijnPhi x + Real.log x) =
      deBruijnAdjointPrimitive x
    rw [deBruijnAdjointPrimitive, Real.exp_add, Real.exp_log hx]
    ring) h

theorem deBruijnPhi_hasDerivAt
    {x : Real} (hx : 0 < x) :
    HasDerivAt deBruijnPhi ((Real.exp (-x) - 1) / x) x := by
  have hdensityContinuous : ContinuousAt deBruijnLogDensity x := by
    unfold deBruijnLogDensity
    exact (Real.continuousAt_log hx.ne').mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_id.neg))
  have hdensityContinuousOn :
      ContinuousOn deBruijnLogDensity (Set.Ioi (0 : Real)) := by
    intro t ht
    unfold deBruijnLogDensity
    exact ((Real.continuousAt_log ht.ne').mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_id.neg))).continuousWithinAt
  have hdensityInterval :
      IntervalIntegrable deBruijnLogDensity volume (0 : Real) x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    have hglobal : IntegrableOn deBruijnLogDensity (Set.Ioi (0 : Real)) := by
      simpa [deBruijnLogDensity] using
        Erdos696.Mertens.integrable_log_mul_exp_neg
    exact hglobal.mono_set Set.Ioc_subset_Ioi_self
  have hintegral : HasDerivAt
      (fun u : Real => ∫ t in (0 : Real)..u, deBruijnLogDensity t)
      (deBruijnLogDensity x) x :=
    intervalIntegral.integral_hasDerivAt_right hdensityInterval
      (hdensityContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      hdensityContinuous
  have hexpNeg : HasDerivAt (fun u : Real => Real.exp (-u))
      (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_id x).neg.exp
  have hlog := Real.hasDerivAt_log hx.ne'
  have hraw := (hexpNeg.mul hlog).add hintegral |>.sub hlog
  unfold deBruijnPhi
  refine hraw.congr_deriv ?_
  unfold deBruijnLogDensity
  field_simp [hx.ne']
  ring

/-- The integrand in de Bruijn's value `h(0)` is an exact derivative. -/
theorem deBruijnAdjointPrimitive_hasDerivAt
    {x : Real} (hx : 0 < x) :
    HasDerivAt deBruijnAdjointPrimitive
      (Real.exp (-x + deBruijnPhi x)) x := by
  have hphi := deBruijnPhi_hasDerivAt hx
  have hraw := (hasDerivAt_id x).mul hphi.exp
  unfold deBruijnAdjointPrimitive
  refine hraw.congr_deriv ?_
  rw [Real.exp_add]
  simp only [id_eq]
  field_simp [hx.ne']
  ring

theorem tendsto_deBruijnLogDensity_intervalIntegral_nhdsGT_zero :
    Tendsto (fun x : Real => ∫ t in (0 : Real)..x, deBruijnLogDensity t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let bound := fun x : Real =>
    ∫ t in Set.Ioc 0 x, |Real.log t * Real.exp (-t)|
  refine squeeze_zero_norm' (a := bound) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := deBruijnLogDensity) hx.le
    simpa [bound, deBruijnLogDensity,
      intervalIntegral.integral_of_le hx.le, Real.norm_eq_abs] using hnorm
  · exact Erdos696.Mertens.integral_log_exp_near_zero_tendsto

theorem tendsto_deBruijnExpNeg_mul_log_nhdsGT_zero :
    Tendsto (fun x : Real => Real.exp (-x) * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
  have hlog := Real.tendsto_log_nhdsGT_zero
  have hneg : Tendsto (fun x : Real => -x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Tendsto (fun x : Real => x) (nhds (0 : Real)) (nhds 0) :=
      tendsto_id
    simpa using (hid.mono_left inf_le_left).neg
  have hexp : Tendsto (fun x : Real => Real.exp (-x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hneg
  have hprod := hlog.atBot_mul_pos zero_lt_one hexp
  exact hprod.congr' (by
    filter_upwards with x
    ring)

theorem tendsto_deBruijnAdjointPrimitive_nhdsGT_zero :
    Tendsto deBruijnAdjointPrimitive
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hsum : Tendsto
      (fun x : Real => deBruijnPhi x + Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
    have h := Tendsto.atBot_add
      tendsto_deBruijnExpNeg_mul_log_nhdsGT_zero
      tendsto_deBruijnLogDensity_intervalIntegral_nhdsGT_zero
    convert h using 1
    ext x
    simp [deBruijnPhi]
  have hexp := Real.tendsto_exp_atBot.comp hsum
  exact Filter.Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx
    show Real.exp (deBruijnPhi x + Real.log x) =
      deBruijnAdjointPrimitive x
    rw [deBruijnAdjointPrimitive, Real.exp_add, Real.exp_log hx]
    ring) hexp

theorem deBruijnAdjointPrimitive_continuousWithinAt_zero :
    ContinuousWithinAt deBruijnAdjointPrimitive (Set.Ici 0) 0 := by
  have hright : ContinuousWithinAt deBruijnAdjointPrimitive (Set.Ioi 0) 0 := by
    unfold ContinuousWithinAt
    simpa [deBruijnAdjointPrimitive] using
      tendsto_deBruijnAdjointPrimitive_nhdsGT_zero
  have hset : Set.Ici (0 : Real) = Set.insert 0 (Set.Ioi 0) := by
    ext x
    change 0 ≤ x ↔ x = 0 ∨ 0 < x
    constructor
    · intro hx
      rcases hx.eq_or_lt with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr hlt
    · rintro (rfl | hx)
      · exact le_rfl
      · exact hx.le
  rw [hset]
  exact continuousWithinAt_insert_self.mpr hright

/-- de Bruijn 1950, Section 4: the value of the adjoint kernel at zero. -/
theorem integral_deBruijnAdjointKernel :
    (∫ x in Set.Ioi (0 : Real),
        Real.exp (-x + deBruijnPhi x)) =
      Real.exp (-Real.eulerMascheroniConstant) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    deBruijnAdjointPrimitive_continuousWithinAt_zero
    (fun x hx => deBruijnAdjointPrimitive_hasDerivAt hx)
    (fun _x _hx => (Real.exp_pos _).le)
    tendsto_deBruijnAdjointPrimitive
  simpa [deBruijnAdjointPrimitive] using h

theorem integrableOn_deBruijnAdjointKernel :
    IntegrableOn (fun x : Real => Real.exp (-x + deBruijnPhi x))
      (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg
    deBruijnAdjointPrimitive_continuousWithinAt_zero
    (fun x hx => deBruijnAdjointPrimitive_hasDerivAt hx)
    (fun _x _hx => (Real.exp_pos _).le)
    tendsto_deBruijnAdjointPrimitive

theorem deBruijnAdjointPrimitive_monotoneOn :
    MonotoneOn deBruijnAdjointPrimitive (Set.Ici 0) := by
  have hcontinuous : ContinuousOn deBruijnAdjointPrimitive (Set.Ici 0) := by
    intro x hx
    have hx' : 0 ≤ x := hx
    rcases hx'.eq_or_lt with heq | hpos
    · subst x
      exact deBruijnAdjointPrimitive_continuousWithinAt_zero
    · exact (deBruijnAdjointPrimitive_hasDerivAt hpos).continuousAt.continuousWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : Real)) hcontinuous
  · intro x hx
    have hpos : 0 < x := by simpa using hx
    exact (deBruijnAdjointPrimitive_hasDerivAt hpos).differentiableAt.differentiableWithinAt
  · intro x hx
    have hpos : 0 < x := by simpa using hx
    rw [(deBruijnAdjointPrimitive_hasDerivAt hpos).deriv]
    exact (Real.exp_pos _).le

theorem deBruijnAdjointPrimitive_le_limit
    {x : Real} (hx : 0 ≤ x) :
    deBruijnAdjointPrimitive x ≤
      Real.exp (-Real.eulerMascheroniConstant) := by
  apply ge_of_tendsto tendsto_deBruijnAdjointPrimitive
  filter_upwards [eventually_ge_atTop x] with y hy
  exact deBruijnAdjointPrimitive_monotoneOn hx (hx.trans hy) hy

end

end Erdos1212Kernel
