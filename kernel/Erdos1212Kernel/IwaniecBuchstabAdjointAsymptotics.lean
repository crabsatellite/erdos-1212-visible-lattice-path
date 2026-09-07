import Erdos1212Kernel.IwaniecBuchstabPrimal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def deBruijnAdjointKernel (x : Real) : Real :=
  Real.exp (-x + deBruijnPhi x)

theorem tendsto_exp_neg_sub_one_mul_log_nhdsGT_zero :
    Tendsto (fun x : Real => (Real.exp (-x) - 1) * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hexp : HasDerivAt (fun x : Real => Real.exp (-x)) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : Real)).neg.exp
  have hratio : Tendsto
      (fun x : Real => (Real.exp (-x) - 1) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
    have hslope := hexp.tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope
  have hxlog : Tendsto (fun x : Real => x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_comm, pow_one] using
      (tendsto_log_mul_rpow_nhdsGT_zero (show (0 : Real) < 1 by norm_num))
  have hproduct := hratio.mul hxlog
  have heq : (fun x : Real =>
      (Real.exp (-x) - 1) / x * (x * Real.log x)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun x : Real => (Real.exp (-x) - 1) * Real.log x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxNe : x ≠ 0 := hx.ne'
    field_simp [hxNe]
  simpa only [mul_zero, neg_zero] using hproduct.congr' heq

theorem tendsto_deBruijnPhi_nhdsGT_zero :
    Tendsto deBruijnPhi (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hsum := tendsto_exp_neg_sub_one_mul_log_nhdsGT_zero.add
    tendsto_deBruijnLogDensity_intervalIntegral_nhdsGT_zero
  have heq : (fun x : Real =>
      (Real.exp (-x) - 1) * Real.log x +
        ∫ t in (0 : Real)..x, deBruijnLogDensity t) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)] deBruijnPhi := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    unfold deBruijnPhi
    ring
  simpa only [zero_add] using hsum.congr' heq

theorem deBruijnPhi_continuousWithinAt_zero :
    ContinuousWithinAt deBruijnPhi (Set.Ici (0 : Real)) 0 := by
  have hright : ContinuousWithinAt deBruijnPhi (Set.Ioi (0 : Real)) 0 := by
    unfold ContinuousWithinAt
    simpa [deBruijnPhi, deBruijnLogDensity] using tendsto_deBruijnPhi_nhdsGT_zero
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

theorem deBruijnPhi_antitoneOn :
    AntitoneOn deBruijnPhi (Set.Ici (0 : Real)) := by
  have hcontinuous : ContinuousOn deBruijnPhi (Set.Ici (0 : Real)) := by
    intro x hx
    change 0 ≤ x at hx
    rcases hx.eq_or_lt with heq | hpos
    · subst x
      exact deBruijnPhi_continuousWithinAt_zero
    · exact (deBruijnPhi_hasDerivAt hpos).continuousAt.continuousWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real)) hcontinuous
  · intro x hx
    have hpos : 0 < x := by simpa using hx
    exact (deBruijnPhi_hasDerivAt hpos).differentiableAt.differentiableWithinAt
  · intro x hx
    have hpos : 0 < x := by simpa using hx
    rw [(deBruijnPhi_hasDerivAt hpos).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by linarith))) hpos.le

theorem deBruijnPhi_nonpos
    {x : Real} (hx : 0 ≤ x) :
    deBruijnPhi x ≤ 0 := by
  have hmono := deBruijnPhi_antitoneOn (show (0 : Real) ∈ Set.Ici 0 by simp) hx hx
  simpa [deBruijnPhi, deBruijnLogDensity] using hmono

theorem tendsto_deBruijnAdjointKernel_nhdsGT_zero :
    Tendsto deBruijnAdjointKernel (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hinner : Tendsto (fun x : Real => -x + deBruijnPhi x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Tendsto (fun x : Real => x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hid.neg.add tendsto_deBruijnPhi_nhdsGT_zero
  simpa [deBruijnAdjointKernel] using
    Real.continuous_exp.continuousAt.tendsto.comp hinner

theorem deBruijnAdjointKernel_continuousOn :
    ContinuousOn deBruijnAdjointKernel (Set.Ioi (0 : Real)) := by
  intro x hx
  unfold deBruijnAdjointKernel
  exact (Real.continuous_exp.continuousAt.comp
    (continuousAt_id.neg.add
      (deBruijnPhi_hasDerivAt hx).continuousAt)).continuousWithinAt

theorem deBruijnAdjointKernel_nonneg
    (x : Real) : 0 ≤ deBruijnAdjointKernel x := by
  unfold deBruijnAdjointKernel
  positivity

theorem deBruijnAdjointKernel_le_one
    {x : Real} (hx : 0 ≤ x) :
    deBruijnAdjointKernel x ≤ 1 := by
  unfold deBruijnAdjointKernel
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith [deBruijnPhi_nonpos hx])

theorem integrableOn_deBruijnAdjointKernel' :
    IntegrableOn deBruijnAdjointKernel (Set.Ioi (0 : Real)) := by
  simpa [deBruijnAdjointKernel] using integrableOn_deBruijnAdjointKernel

theorem tendsto_deBruijnAdjointFunction_atTop_zero :
    Tendsto deBruijnAdjointFunction atTop (nhds 0) := by
  let F := fun u x : Real => Real.exp (-u * x) * deBruijnAdjointKernel x
  have hmeas : ∀ᶠ u : Real in atTop,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with u
    have hcont : ContinuousOn (F u) (Set.Ioi (0 : Real)) := by
      dsimp [F]
      exact (by fun_prop : Continuous (fun x : Real => Real.exp (-u * x))).continuousOn.mul
        deBruijnAdjointKernel_continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ u : Real in atTop,
      ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
        ‖F u x‖ ≤ deBruijnAdjointKernel x := by
    filter_upwards [eventually_ge_atTop (0 : Real)] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hux : 0 ≤ u * x := mul_nonneg hu hx.le
    have hexpLe : Real.exp (-u * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (deBruijnAdjointKernel_nonneg x))]
    exact mul_le_of_le_one_left (deBruijnAdjointKernel_nonneg x) hexpLe
  have hlim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun u : Real => F u x) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hscale : Tendsto (fun u : Real => u * x) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos hx).2 tendsto_id
    have hexp : Tendsto (fun u : Real => Real.exp (-(u * x))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    simpa [F] using hexp.mul_const (deBruijnAdjointKernel x)
  have hresult := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0)) deBruijnAdjointKernel
    hmeas hbound integrableOn_deBruijnAdjointKernel' hlim
  have hresult0 : Tendsto (fun u : Real =>
      ∫ x in Set.Ioi (0 : Real), F u x) atTop (nhds 0) := by
    simpa using hresult
  apply hresult0.congr'
  filter_upwards with u
  unfold deBruijnAdjointFunction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp [F, deBruijnAdjointKernel]

theorem deBruijnAdjointFunction_continuousWithinAt_zero :
    ContinuousWithinAt deBruijnAdjointFunction (Set.Ici (0 : Real)) 0 := by
  let F := fun u x : Real => Real.exp (-u * x) * deBruijnAdjointKernel x
  have hmeas : ∀ᶠ u : Real in nhdsWithin 0 (Set.Ici 0),
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with u
    have hcont : ContinuousOn (F u) (Set.Ioi (0 : Real)) := by
      dsimp [F]
      exact (by fun_prop : Continuous (fun x : Real => Real.exp (-u * x))).continuousOn.mul
        deBruijnAdjointKernel_continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ u : Real in nhdsWithin 0 (Set.Ici 0),
      ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
        ‖F u x‖ ≤ deBruijnAdjointKernel x := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hux : 0 ≤ u * x := mul_nonneg hu hx.le
    have hexpLe : Real.exp (-u * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (deBruijnAdjointKernel_nonneg x))]
    exact mul_le_of_le_one_left (deBruijnAdjointKernel_nonneg x) hexpLe
  have hlim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun u : Real => F u x) (nhdsWithin 0 (Set.Ici 0))
        (nhds (deBruijnAdjointKernel x)) := by
    filter_upwards with x
    have hu : Tendsto (fun u : Real => u)
        (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := tendsto_id.mono_left inf_le_left
    have hinner : Tendsto (fun u : Real => -u * x)
        (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
      simpa using hu.neg.mul_const x
    have hexp : Tendsto (fun u : Real => Real.exp (-u * x))
        (nhdsWithin 0 (Set.Ici 0)) (nhds 1) := by
      simpa using Real.continuous_exp.continuousAt.tendsto.comp hinner
    simpa [F] using hexp.mul_const (deBruijnAdjointKernel x)
  have hresult := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0)) deBruijnAdjointKernel
    hmeas hbound integrableOn_deBruijnAdjointKernel' hlim
  unfold ContinuousWithinAt
  have hresult' : Tendsto deBruijnAdjointFunction
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (∫ x in Set.Ioi (0 : Real), deBruijnAdjointKernel x)) := by
    apply hresult.congr'
    filter_upwards with u
    unfold deBruijnAdjointFunction
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [F, deBruijnAdjointKernel]
  simpa [deBruijnAdjointFunction, deBruijnAdjointKernel] using hresult'

theorem mul_deBruijnAdjointFunction_eq_rescaled_integral
    {u : Real} (hu : 0 < u) :
    u * deBruijnAdjointFunction u =
      ∫ y in Set.Ioi (0 : Real),
        Real.exp (-y) * deBruijnAdjointKernel (y / u) := by
  let g := fun y : Real => Real.exp (-y) * deBruijnAdjointKernel (y / u)
  have hchange := integral_comp_mul_left_Ioi g (0 : Real) hu
  have hleft :
      (∫ x in Set.Ioi (0 : Real), g (u * x)) = deBruijnAdjointFunction u := by
    unfold deBruijnAdjointFunction
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [g, deBruijnAdjointKernel]
    rw [mul_div_cancel_left₀ x hu.ne']
    ring
  rw [hleft] at hchange
  dsimp [g] at hchange ⊢
  norm_num at hchange
  rw [hchange]
  field_simp [hu.ne']

theorem tendsto_mul_deBruijnAdjointFunction_atTop_one :
    Tendsto (fun u : Real => u * deBruijnAdjointFunction u)
      atTop (nhds 1) := by
  let F := fun u y : Real =>
    Real.exp (-y) * deBruijnAdjointKernel (y / u)
  let bound := fun y : Real => Real.exp (-y)
  have hmeas : ∀ᶠ u : Real in atTop,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with u hu
    have hcont : ContinuousOn (F u) (Set.Ioi (0 : Real)) := by
      dsimp [F]
      have hdiv : ContinuousOn (fun y : Real => y / u) (Set.Ioi (0 : Real)) := by
        fun_prop
      have hkernel : ContinuousOn
          (fun y : Real => deBruijnAdjointKernel (y / u)) (Set.Ioi (0 : Real)) := by
        apply deBruijnAdjointKernel_continuousOn.comp hdiv
        intro y hy
        exact div_pos hy hu
      exact (by fun_prop : Continuous (fun y : Real => Real.exp (-y))).continuousOn.mul hkernel
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᶠ u : Real in atTop,
      ∀ᵐ y ∂(volume.restrict (Set.Ioi 0)), ‖F u y‖ ≤ bound y := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hK := deBruijnAdjointKernel_le_one (div_nonneg hy.le hu.le)
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (deBruijnAdjointKernel_nonneg (y / u)))]
    dsimp [F, bound]
    calc
      Real.exp (-y) * deBruijnAdjointKernel (y / u) ≤
          Real.exp (-y) * 1 :=
        mul_le_mul_of_nonneg_left hK (Real.exp_nonneg _)
      _ = Real.exp (-y) := mul_one _
  have hboundInt : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    simpa [bound] using exp_neg_integrableOn_Ioi (0 : Real) (show (0 : Real) < 1 by norm_num)
  have hlim : ∀ᵐ y ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun u : Real => F u y) atTop (nhds (bound y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hinv : Tendsto (fun u : Real => u⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hzero : Tendsto (fun u : Real => y / u) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have hpos : ∀ᶠ u : Real in atTop, y / u ∈ Set.Ioi (0 : Real) := by
      filter_upwards [eventually_gt_atTop (0 : Real)] with u hu
      exact div_pos hy hu
    have hwithin : Tendsto (fun u : Real => y / u) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
    have hkernel := tendsto_deBruijnAdjointKernel_nhdsGT_zero.comp hwithin
    dsimp [F, bound]
    simpa using tendsto_const_nhds.mul hkernel
  have hresult := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0)) bound hmeas hbound hboundInt hlim
  have hintegral : (∫ y in Set.Ioi (0 : Real), bound y) = 1 := by
    simpa [bound] using integral_exp_neg_Ioi_zero
  rw [hintegral] at hresult
  apply hresult.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with u hu
  exact (mul_deBruijnAdjointFunction_eq_rescaled_integral hu).symm

theorem tendsto_succ_mul_deBruijnAdjointFunction_atTop_one :
    Tendsto (fun u : Real => (u + 1) * deBruijnAdjointFunction u)
      atTop (nhds 1) := by
  have hone : Tendsto deBruijnAdjointFunction atTop (nhds 0) :=
    tendsto_deBruijnAdjointFunction_atTop_zero
  have hsum := tendsto_mul_deBruijnAdjointFunction_atTop_one.add hone
  convert hsum using 1
  · ext u
    ring
  · norm_num

end

end Erdos1212Kernel
