import Erdos1212Kernel.IwaniecBuchstabAdjointKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory

set_option maxHeartbeats 1800000

def deBruijnAdjointFunction (u : Real) : Real :=
  ∫ x in Set.Ioi (0 : Real),
    Real.exp (-u * x) * Real.exp (-x + deBruijnPhi x)

def deBruijnAdjointMoment (u : Real) (x : Real) : Real :=
  x * Real.exp (-u * x + deBruijnPhi x)

theorem integrableOn_deBruijnAdjointFunction_integrand
    {u : Real} (hu : 0 ≤ u) :
    IntegrableOn
      (fun x : Real =>
        Real.exp (-u * x) * Real.exp (-x + deBruijnPhi x))
      (Set.Ioi 0) := by
  have hkernel := integrableOn_deBruijnAdjointKernel
  apply hkernel.mono'
  · have hexp : AEStronglyMeasurable (fun x : Real => Real.exp (-u * x))
        (volume.restrict (Set.Ioi 0)) := by
      exact (by fun_prop : Continuous (fun x : Real => Real.exp (-u * x))).aestronglyMeasurable
    exact hexp.mul hkernel.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxNonneg : 0 ≤ x := hx.le
    have hux : 0 ≤ u * x := mul_nonneg hu hxNonneg
    have hexpNonneg : 0 ≤ Real.exp (-u * x) := (Real.exp_pos _).le
    have hexpLe : Real.exp (-u * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hkernelNonneg : 0 ≤ Real.exp (-x + deBruijnPhi x) :=
      (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg hexpNonneg hkernelNonneg)]
    exact mul_le_of_le_one_left hkernelNonneg hexpLe

@[simp]
theorem deBruijnAdjointFunction_zero :
    deBruijnAdjointFunction 0 =
      Real.exp (-Real.eulerMascheroniConstant) := by
  unfold deBruijnAdjointFunction
  simpa using integral_deBruijnAdjointKernel

theorem deBruijnAdjointPrimitive_nonneg
    {x : Real} (hx : 0 ≤ x) :
    0 ≤ deBruijnAdjointPrimitive x := by
  unfold deBruijnAdjointPrimitive
  positivity

theorem integrableOn_deBruijnAdjointMoment
    {u : Real} (hu : 0 < u) :
    IntegrableOn (deBruijnAdjointMoment u) (Set.Ioi 0) := by
  let C := Real.exp (-Real.eulerMascheroniConstant)
  let majorant := fun x : Real => C * Real.exp (-u * x)
  have hmajorant : IntegrableOn majorant (Set.Ioi 0) := by
    have hbase := exp_neg_integrableOn_Ioi (0 : Real) hu
    simpa [majorant] using hbase.const_mul C
  apply hmajorant.mono'
  · have hprimitiveContinuous :
        ContinuousOn deBruijnAdjointPrimitive (Set.Ioi (0 : Real)) := by
      intro x hx
      exact (deBruijnAdjointPrimitive_hasDerivAt hx).continuousAt.continuousWithinAt
    have hprimitiveMeas : AEStronglyMeasurable deBruijnAdjointPrimitive
        (volume.restrict (Set.Ioi 0)) :=
      hprimitiveContinuous.aestronglyMeasurable measurableSet_Ioi
    have hexpMeas : AEStronglyMeasurable (fun x : Real => Real.exp (-u * x))
        (volume.restrict (Set.Ioi 0)) := by
      exact (by fun_prop : Continuous (fun x : Real => Real.exp (-u * x))).aestronglyMeasurable
    have hproduct := hexpMeas.mul hprimitiveMeas
    apply hproduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Real.exp (-u * x) * deBruijnAdjointPrimitive x =
      deBruijnAdjointMoment u x
    unfold deBruijnAdjointMoment deBruijnAdjointPrimitive
    rw [Real.exp_add]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxNonneg : 0 ≤ x := hx.le
    have hprimitiveNonneg := deBruijnAdjointPrimitive_nonneg hxNonneg
    have hprimitiveLe := deBruijnAdjointPrimitive_le_limit hxNonneg
    have hexpNonneg : 0 ≤ Real.exp (-u * x) := (Real.exp_pos _).le
    have heq : deBruijnAdjointMoment u x =
        Real.exp (-u * x) * deBruijnAdjointPrimitive x := by
      unfold deBruijnAdjointMoment deBruijnAdjointPrimitive
      rw [Real.exp_add]
      ring
    rw [heq, Real.norm_of_nonneg (mul_nonneg hexpNonneg hprimitiveNonneg)]
    dsimp [majorant, C]
    nlinarith

theorem deBruijnAdjointFunction_hasDerivAt
    {u : Real} (hu : 0 < u) :
    HasDerivAt deBruijnAdjointFunction
      (-(∫ x in Set.Ioi (0 : Real), deBruijnAdjointMoment (u + 1) x)) u := by
  let F := fun v x : Real =>
    Real.exp (-v * x) * Real.exp (-x + deBruijnPhi x)
  let F' := fun v x : Real =>
    -x * Real.exp (-v * x) * Real.exp (-x + deBruijnPhi x)
  let s := Set.Ioo (u / 2) (3 * u / 2)
  let bound := fun x : Real => deBruijnAdjointMoment (u / 2 + 1) x
  have hF'eq (x : Real) :
      -deBruijnAdjointMoment (u + 1) x = F' u x := by
    have hexp : Real.exp (-(u + 1) * x + deBruijnPhi x) =
        Real.exp (-u * x) * Real.exp (-x + deBruijnPhi x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold F' deBruijnAdjointMoment
    rw [hexp]
    ring
  have hs : s ∈ nhds u := by
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hFmeas : ∀ᶠ v in nhds u,
      AEStronglyMeasurable (F v) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with v
    have hexp : AEStronglyMeasurable (fun x : Real => Real.exp (-v * x))
        (volume.restrict (Set.Ioi 0)) := by
      exact (by fun_prop : Continuous (fun x : Real => Real.exp (-v * x))).aestronglyMeasurable
    exact hexp.mul integrableOn_deBruijnAdjointKernel.aestronglyMeasurable
  have hFint : Integrable (F u) (volume.restrict (Set.Ioi 0)) := by
    simpa [F] using integrableOn_deBruijnAdjointFunction_integrand hu.le
  have hboundInt : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    have hpos : 0 < u / 2 + 1 := by linarith
    simpa [bound] using integrableOn_deBruijnAdjointMoment hpos
  have hF'Int : Integrable (F' u) (volume.restrict (Set.Ioi 0)) := by
    have hmoment := integrableOn_deBruijnAdjointMoment (show 0 < u + 1 by linarith)
    apply hmoment.neg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hF'eq x
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ v ∈ s, ‖F' v x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro v hv
    have hxPos : 0 < x := hx
    have hvLower : u / 2 < v := hv.1
    have hexpLe : Real.exp (-v * x) ≤ Real.exp (-(u / 2) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hkernelNonneg : 0 ≤ Real.exp (-x + deBruijnPhi x) :=
      (Real.exp_pos _).le
    have hleftNonneg : 0 ≤ x * Real.exp (-v * x) := by positivity
    have hnormEq : ‖F' v x‖ =
        x * Real.exp (-v * x) * Real.exp (-x + deBruijnPhi x) := by
      unfold F'
      have hnonpos :
          -x * Real.exp (-v * x) * Real.exp (-x + deBruijnPhi x) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hxPos.le)
            (Real.exp_nonneg _)) (Real.exp_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
      ring
    have hscaled := mul_le_mul_of_nonneg_left hexpLe hxPos.le
    calc
      ‖F' v x‖ =
          x * Real.exp (-v * x) * Real.exp (-x + deBruijnPhi x) := hnormEq
      _ ≤ x * Real.exp (-(u / 2) * x) *
          Real.exp (-x + deBruijnPhi x) :=
        mul_le_mul_of_nonneg_right hscaled hkernelNonneg
      _ = bound x := by
        unfold bound deBruijnAdjointMoment
        have hexp : Real.exp (-(u / 2 + 1) * x + deBruijnPhi x) =
            Real.exp (-(u / 2) * x) *
              Real.exp (-x + deBruijnPhi x) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
  have hdiff : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ v ∈ s, HasDerivAt (F · x) (F' v x) v := by
    filter_upwards with x
    intro v _hv
    unfold F F'
    have hinner : HasDerivAt (fun z : Real => -z * x) (-x) v := by
      convert (hasDerivAt_id v).neg.mul_const x using 1 <;> ring
    have hraw := hinner.exp.mul_const (Real.exp (-x + deBruijnPhi x))
    convert hraw using 1 <;> ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := F) (F' := F')
    (bound := bound) hs hFmeas hFint hF'Int.aestronglyMeasurable
    hbound hboundInt hdiff
  have hderiv := hresult.2
  have hderiv' : HasDerivAt deBruijnAdjointFunction
      (∫ x in Set.Ioi (0 : Real), F' u x) u := by
    simpa only [deBruijnAdjointFunction, F] using hderiv
  refine hderiv'.congr_deriv ?_
  rw [← MeasureTheory.integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact (hF'eq x).symm

theorem deBruijnAdjointMoment_eq_exp_mul_primitive
    (u x : Real) :
    deBruijnAdjointMoment u x =
      Real.exp (-u * x) * deBruijnAdjointPrimitive x := by
  unfold deBruijnAdjointMoment deBruijnAdjointPrimitive
  rw [Real.exp_add]
  ring

theorem tendsto_deBruijnAdjointMoment_nhdsGT_zero
    (u : Real) :
    Filter.Tendsto (deBruijnAdjointMoment u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : Real => Real.exp (-u * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hinner : Filter.Tendsto (fun x : Real => -u * x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hid : Filter.Tendsto (fun x : Real => x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        (show Filter.Tendsto (fun x : Real => x) (nhds (0 : Real)) (nhds 0)
          from tendsto_id).mono_left inf_le_left
      simpa using (tendsto_const_nhds.mul hid).neg
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hinner
  have hprod := hexp.mul tendsto_deBruijnAdjointPrimitive_nhdsGT_zero
  have hprod' : Filter.Tendsto
      (fun x : Real => Real.exp (-u * x) * deBruijnAdjointPrimitive x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hprod
  exact Filter.Tendsto.congr' (by
    filter_upwards with x
    exact (deBruijnAdjointMoment_eq_exp_mul_primitive u x).symm) hprod'

theorem tendsto_deBruijnAdjointMoment_atTop
    {u : Real} (hu : 0 < u) :
    Filter.Tendsto (deBruijnAdjointMoment u) atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : Real => Real.exp (-u * x))
      atTop (nhds 0) := by
    have hscale : Filter.Tendsto (fun x : Real => u * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hu).2 tendsto_id
    simpa [Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hprod := hexp.mul tendsto_deBruijnAdjointPrimitive
  have hprod' : Filter.Tendsto
      (fun x : Real => Real.exp (-u * x) * deBruijnAdjointPrimitive x)
      atTop (nhds 0) := by
    simpa using hprod
  exact Filter.Tendsto.congr' (by
    filter_upwards with x
    exact (deBruijnAdjointMoment_eq_exp_mul_primitive u x).symm) hprod'

theorem deBruijnAdjointMoment_continuousWithinAt_zero
    (u : Real) :
    ContinuousWithinAt (deBruijnAdjointMoment u) (Set.Ici 0) 0 := by
  have hright : ContinuousWithinAt (deBruijnAdjointMoment u) (Set.Ioi 0) 0 := by
    unfold ContinuousWithinAt
    simpa [deBruijnAdjointMoment] using
      tendsto_deBruijnAdjointMoment_nhdsGT_zero u
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

def deBruijnAdjointSpatialDerivative (u x : Real) : Real :=
  Real.exp (-u * x) * Real.exp (-x + deBruijnPhi x) -
    u * deBruijnAdjointMoment u x

theorem deBruijnAdjointMoment_hasDerivAt
    {u x : Real} (hx : 0 < x) :
    HasDerivAt (deBruijnAdjointMoment u)
      (deBruijnAdjointSpatialDerivative u x) x := by
  have hexp : HasDerivAt (fun t : Real => Real.exp (-u * t))
      (-u * Real.exp (-u * x)) x := by
    have hinner : HasDerivAt (fun t : Real => -u * t) (-u) x := by
      convert (hasDerivAt_id x).const_mul (-u) using 1 <;> ring
    convert hinner.exp using 1 <;> ring
  have hprimitive := deBruijnAdjointPrimitive_hasDerivAt hx
  have hraw := hexp.mul hprimitive
  have heq : deBruijnAdjointMoment u =
      fun t : Real => Real.exp (-u * t) * deBruijnAdjointPrimitive t := by
    funext t
    exact deBruijnAdjointMoment_eq_exp_mul_primitive u t
  rw [heq]
  refine hraw.congr_deriv ?_
  unfold deBruijnAdjointSpatialDerivative
  rw [deBruijnAdjointMoment_eq_exp_mul_primitive]
  ring

theorem integrableOn_deBruijnAdjointSpatialDerivative
    {u : Real} (hu : 0 < u) :
    IntegrableOn (deBruijnAdjointSpatialDerivative u) (Set.Ioi 0) := by
  have hfirst := integrableOn_deBruijnAdjointFunction_integrand hu.le
  have hsecond := (integrableOn_deBruijnAdjointMoment hu).const_mul u
  unfold deBruijnAdjointSpatialDerivative
  exact hfirst.sub hsecond

theorem integral_deBruijnAdjointSpatialDerivative
    {u : Real} (hu : 0 < u) :
    (∫ x in Set.Ioi (0 : Real),
        deBruijnAdjointSpatialDerivative u x) = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (deBruijnAdjointMoment_continuousWithinAt_zero u)
    (fun x hx => deBruijnAdjointMoment_hasDerivAt hx)
    (integrableOn_deBruijnAdjointSpatialDerivative hu)
    (tendsto_deBruijnAdjointMoment_atTop hu)
  simpa [deBruijnAdjointMoment] using h

theorem deBruijnAdjointFunction_eq_mul_moment
    {u : Real} (hu : 0 < u) :
    deBruijnAdjointFunction u =
      u * (∫ x in Set.Ioi (0 : Real), deBruijnAdjointMoment u x) := by
  have hzero := integral_deBruijnAdjointSpatialDerivative hu
  have hfirst := integrableOn_deBruijnAdjointFunction_integrand hu.le
  have hsecond := (integrableOn_deBruijnAdjointMoment hu).const_mul u
  unfold deBruijnAdjointSpatialDerivative at hzero
  rw [MeasureTheory.integral_sub hfirst hsecond,
    MeasureTheory.integral_const_mul] at hzero
  unfold deBruijnAdjointFunction
  linarith

/-- de Bruijn 1950, equation (4.3), on the range needed by Iwaniec. -/
theorem deBruijnAdjoint_equation
    {u : Real} (hu : 1 < u) :
    u * deriv deBruijnAdjointFunction (u - 1) +
      deBruijnAdjointFunction u = 0 := by
  have hderiv := deBruijnAdjointFunction_hasDerivAt (show 0 < u - 1 by linarith)
  have hmoment := deBruijnAdjointFunction_eq_mul_moment (show 0 < u by linarith)
  rw [hderiv.deriv]
  simpa only [sub_add_cancel] using (by linarith :
    u * (-(∫ x in Set.Ioi (0 : Real), deBruijnAdjointMoment u x)) +
      deBruijnAdjointFunction u = 0)

end

end Erdos1212Kernel
