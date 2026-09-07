import Erdos1212Kernel.IwaniecBuchstabAdjointAsymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def iwaniecAdjointPairIntegrand (u : Real) : Real :=
  deBruijnAdjointFunction u * iwaniecBuchstabFunction u

def iwaniecAdjointPairPrimitive (s : Real) : Real :=
  ∫ u in (1 : Real)..s, iwaniecAdjointPairIntegrand u

def iwaniecBuchstabInvariant (t : Real) : Real :=
  deBruijnAdjointFunction t * iwaniecBuchstabScaled (t + 1) +
    (iwaniecAdjointPairPrimitive (t + 1) - iwaniecAdjointPairPrimitive t)

theorem deBruijnAdjointFunction_continuousOn_Ici :
    ContinuousOn deBruijnAdjointFunction (Set.Ici (0 : Real)) := by
  intro u hu
  change 0 ≤ u at hu
  rcases hu.eq_or_lt with heq | hpos
  · subst u
    exact deBruijnAdjointFunction_continuousWithinAt_zero
  · exact (deBruijnAdjointFunction_hasDerivAt hpos).continuousAt.continuousWithinAt

theorem iwaniecAdjointPairIntegrand_continuousOn :
    ContinuousOn iwaniecAdjointPairIntegrand (Set.Ici (1 : Real)) := by
  unfold iwaniecAdjointPairIntegrand
  exact (deBruijnAdjointFunction_continuousOn_Ici.mono
    (Set.Ici_subset_Ici.mpr (by norm_num))).mul
    iwaniecBuchstabFunction_continuousOn_Ici

theorem iwaniecAdjointPairIntegrand_intervalIntegrable
    {a b : Real} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable iwaniecAdjointPairIntegrand volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply iwaniecAdjointPairIntegrand_continuousOn.mono
  intro x hx
  exact (le_min ha hb).trans hx.1

theorem iwaniecAdjointPairPrimitive_hasDerivAt
    {s : Real} (hs : 1 < s) :
    HasDerivAt iwaniecAdjointPairPrimitive (iwaniecAdjointPairIntegrand s) s := by
  have hcontIoi : ContinuousOn iwaniecAdjointPairIntegrand (Set.Ioi (1 : Real)) :=
    iwaniecAdjointPairIntegrand_continuousOn.mono Set.Ioi_subset_Ici_self
  unfold iwaniecAdjointPairPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (iwaniecAdjointPairIntegrand_intervalIntegrable (le_refl 1) hs.le)
    (hcontIoi.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hcontIoi.continuousAt (Ioi_mem_nhds hs))

theorem iwaniecAdjointPairPrimitive_sub_eq_window
    {t : Real} (ht : 1 ≤ t) :
    iwaniecAdjointPairPrimitive (t + 1) - iwaniecAdjointPairPrimitive t =
      ∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u := by
  unfold iwaniecAdjointPairPrimitive
  exact intervalIntegral.integral_interval_sub_left
    (iwaniecAdjointPairIntegrand_intervalIntegrable (le_refl 1) (by linarith))
    (iwaniecAdjointPairIntegrand_intervalIntegrable (le_refl 1) ht)

theorem iwaniecBuchstabScaled_eq_mul
    {s : Real} (hs : s ≠ 0) :
    iwaniecBuchstabScaled s = s * iwaniecBuchstabFunction s := by
  unfold iwaniecBuchstabFunction
  field_simp [hs]

theorem iwaniecBuchstabInvariant_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt iwaniecBuchstabInvariant 0 t := by
  have hh := deBruijnAdjointFunction_hasDerivAt (by linarith : 0 < t)
  have hshift : HasDerivAt (fun x : Real => x + 1) 1 t :=
    (hasDerivAt_id t).add_const 1
  have hscaled := (iwaniecBuchstabScaled_hasDerivAt
    (by linarith : 2 < t + 1)).comp t hshift
  have hproduct := hh.mul hscaled
  have hprimRight := (iwaniecAdjointPairPrimitive_hasDerivAt
    (by linarith : 1 < t + 1)).comp t hshift
  have hprimLeft := iwaniecAdjointPairPrimitive_hasDerivAt ht
  have hraw := hproduct.add (hprimRight.sub hprimLeft)
  unfold iwaniecBuchstabInvariant
  refine hraw.congr_deriv ?_
  simp only [Function.comp_apply, mul_one, add_sub_cancel_right]
  have hadjoint : (t + 1) * deriv deBruijnAdjointFunction t +
      deBruijnAdjointFunction (t + 1) = 0 := by
    convert deBruijnAdjoint_equation
      (u := t + 1) (by linarith : 1 < t + 1) using 1 <;> ring
  rw [hh.deriv] at hadjoint
  have hscaledEq := iwaniecBuchstabScaled_eq_mul
    (s := t + 1) (by linarith : t + 1 ≠ 0)
  rw [hscaledEq]
  unfold iwaniecAdjointPairIntegrand
  calc
    -(∫ x in Set.Ioi 0, deBruijnAdjointMoment (t + 1) x) *
          ((t + 1) * iwaniecBuchstabFunction (t + 1)) +
        deBruijnAdjointFunction t * iwaniecBuchstabFunction t +
        (deBruijnAdjointFunction (t + 1) * iwaniecBuchstabFunction (t + 1) -
          deBruijnAdjointFunction t * iwaniecBuchstabFunction t) =
        iwaniecBuchstabFunction (t + 1) *
          ((t + 1) * (-(∫ x in Set.Ioi 0,
            deBruijnAdjointMoment (t + 1) x)) +
            deBruijnAdjointFunction (t + 1)) := by ring
    _ = 0 := by rw [hadjoint, mul_zero]

theorem iwaniecBuchstabInvariant_eq_of_one_lt
    {s t : Real} (hs : 1 < s) (ht : 1 < t) :
    iwaniecBuchstabInvariant s = iwaniecBuchstabInvariant t := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (iwaniecBuchstabInvariant_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (iwaniecBuchstabInvariant_hasDerivAt hx).deriv
  · exact hs
  · exact ht

theorem tendsto_iwaniecAdjointPairIntegrand_atTop_zero :
    Tendsto iwaniecAdjointPairIntegrand atTop (nhds 0) := by
  unfold iwaniecAdjointPairIntegrand
  simpa using tendsto_deBruijnAdjointFunction_atTop_zero.mul
    tendsto_iwaniecBuchstabFunction_atTop

theorem tendsto_iwaniecAdjointPairWindow_atTop_zero :
    Tendsto (fun t : Real =>
      ∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.mp tendsto_iwaniecAdjointPairIntegrand_atTop_zero
      (ε / 2) (half_pos hε) with ⟨A, hA⟩
  refine ⟨max A 1, ?_⟩
  intro t ht
  have htA : A ≤ t := (le_max_left _ _).trans ht
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t + 1) (C := ε / 2)
    (f := iwaniecAdjointPairIntegrand) (by
      intro u hu
      have htu : t ≤ u := by
        rw [Set.uIoc_of_le (by linarith : t ≤ t + 1)] at hu
        exact hu.1.le
      have hdist := hA u (htA.trans htu)
      simpa [dist_eq_norm] using hdist.le)
  calc
    dist (∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u) 0 =
        ‖∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u‖ := by
      simpa using (dist_zero_right
        (∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u))
    _ ≤ (ε / 2) * |(t + 1) - t| := hbound
    _ = ε / 2 := by rw [show (t + 1) - t = 1 by ring]; simp
    _ < ε := half_lt_self hε

theorem tendsto_iwaniecBuchstabInvariant_atTop :
    Tendsto iwaniecBuchstabInvariant atTop
      (nhds (2 / iwaniecSieveNormalizationC)) := by
  have hshiftTop : Tendsto (fun t : Real => t + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hwShift := tendsto_iwaniecBuchstabFunction_atTop.comp hshiftTop
  have hfirst := tendsto_succ_mul_deBruijnAdjointFunction_atTop_one.mul hwShift
  have hraw := hfirst.add tendsto_iwaniecAdjointPairWindow_atTop_zero
  have heq : (fun t : Real =>
      ((t + 1) * deBruijnAdjointFunction t) *
          iwaniecBuchstabFunction (t + 1) +
        ∫ u in t..(t + 1), iwaniecAdjointPairIntegrand u) =ᶠ[atTop]
      iwaniecBuchstabInvariant := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with t ht
    unfold iwaniecBuchstabInvariant
    rw [iwaniecAdjointPairPrimitive_sub_eq_window ht]
    rw [iwaniecBuchstabScaled_eq_mul (by linarith : t + 1 ≠ 0)]
    ring
  simpa only [one_mul, add_zero] using hraw.congr' heq

theorem iwaniecBuchstabInvariant_eq_limit_of_one_lt
    {t : Real} (ht : 1 < t) :
    iwaniecBuchstabInvariant t = 2 / iwaniecSieveNormalizationC := by
  have heq : (fun _s : Real => iwaniecBuchstabInvariant t) =ᶠ[atTop]
      iwaniecBuchstabInvariant := by
    filter_upwards [eventually_gt_atTop (1 : Real)] with s hs
    exact iwaniecBuchstabInvariant_eq_of_one_lt ht hs
  have hsame : Tendsto iwaniecBuchstabInvariant atTop
      (nhds (iwaniecBuchstabInvariant t)) :=
    (tendsto_const_nhds : Tendsto (fun _s : Real => iwaniecBuchstabInvariant t)
      atTop (nhds (iwaniecBuchstabInvariant t))).congr' heq
  exact tendsto_nhds_unique hsame tendsto_iwaniecBuchstabInvariant_atTop

theorem iwaniecAdjointPairPrimitive_continuousWithinAt_one :
    ContinuousWithinAt iwaniecAdjointPairPrimitive (Set.Ici (1 : Real)) 1 := by
  have hlocal : ContinuousOn iwaniecAdjointPairPrimitive (Set.Icc (1 : Real) 2) := by
    simpa [iwaniecAdjointPairPrimitive,
      Set.uIcc_of_le (by norm_num : (1 : Real) ≤ 2)] using
      intervalIntegral.continuousOn_primitive_interval'
        (iwaniecAdjointPairIntegrand_intervalIntegrable
          (le_refl 1) (by norm_num : (1 : Real) ≤ 2))
        (show (1 : Real) ∈ Set.uIcc 1 2 by simp)
  have hsets : Set.Icc (1 : Real) 2 =ᶠ[nhds (1 : Real)] Set.Ici 1 := by
    filter_upwards [Iic_mem_nhds (show (1 : Real) < 2 by norm_num)] with x hx
    apply propext
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, hx⟩
  exact (hlocal 1 (show (1 : Real) ∈ Set.Icc 1 2 by constructor <;> norm_num)).congr_set hsets

theorem iwaniecBuchstabInvariant_continuousWithinAt_one :
    ContinuousWithinAt iwaniecBuchstabInvariant (Set.Ioi (1 : Real)) 1 := by
  have hh : ContinuousAt deBruijnAdjointFunction 1 :=
    (deBruijnAdjointFunction_hasDerivAt (by norm_num)).continuousAt
  have hscaled : ContinuousAt iwaniecBuchstabScaled 2 := by
    have hcont : ContinuousOn iwaniecBuchstabScaled (Set.Ici (1 : Real)) := by
      unfold iwaniecBuchstabScaled
      exact ((continuousOn_const.mul continuousOn_id).sub
        iwaniecWExtended_continuousOn).div_const iwaniecSieveNormalizationC
    exact hcont.continuousAt (Ici_mem_nhds (by norm_num : (1 : Real) < 2))
  have hshift : ContinuousAt (fun t : Real => t + 1) 1 := by fun_prop
  have hscaledShift : ContinuousAt
      (fun t : Real => iwaniecBuchstabScaled (t + 1)) 1 := by
    simpa [Function.comp_def] using hscaled.comp_of_eq hshift (by norm_num)
  have hprimRight : ContinuousAt iwaniecAdjointPairPrimitive 2 :=
    (iwaniecAdjointPairPrimitive_hasDerivAt (by norm_num)).continuousAt
  have hprimShift : ContinuousAt
      (fun t : Real => iwaniecAdjointPairPrimitive (t + 1)) 1 := by
    simpa [Function.comp_def] using hprimRight.comp_of_eq hshift (by norm_num)
  unfold iwaniecBuchstabInvariant
  exact (hh.mul hscaledShift).continuousWithinAt.add
    (hprimShift.continuousWithinAt.sub
      (iwaniecAdjointPairPrimitive_continuousWithinAt_one.mono
        Set.Ioi_subset_Ici_self))

theorem iwaniecBuchstabInvariant_one_eq_limit :
    iwaniecBuchstabInvariant 1 = 2 / iwaniecSieveNormalizationC := by
  have heq : iwaniecBuchstabInvariant =ᶠ[nhdsWithin (1 : Real) (Set.Ioi 1)]
      (fun _t : Real => 2 / iwaniecSieveNormalizationC) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact iwaniecBuchstabInvariant_eq_limit_of_one_lt ht
  have hlimit : Tendsto iwaniecBuchstabInvariant
      (nhdsWithin (1 : Real) (Set.Ioi 1))
      (nhds (2 / iwaniecSieveNormalizationC)) :=
    (tendsto_const_nhds : Tendsto
      (fun _t : Real => 2 / iwaniecSieveNormalizationC)
      (nhdsWithin (1 : Real) (Set.Ioi 1))
      (nhds (2 / iwaniecSieveNormalizationC))).congr' heq.symm
  exact tendsto_nhds_unique iwaniecBuchstabInvariant_continuousWithinAt_one.tendsto hlimit

def deBruijnAdjointInitialDerivative (t : Real) : Real :=
  -deBruijnAdjointFunction (t + 1) / (t + 1)

theorem deBruijnAdjointFunction_hasDerivAt_initial
    {t : Real} (ht : 0 < t) :
    HasDerivAt deBruijnAdjointFunction (deBruijnAdjointInitialDerivative t) t := by
  have hh := deBruijnAdjointFunction_hasDerivAt ht
  refine hh.congr_deriv ?_
  have hadjoint : (t + 1) * deriv deBruijnAdjointFunction t +
      deBruijnAdjointFunction (t + 1) = 0 := by
    convert deBruijnAdjoint_equation
      (u := t + 1) (by linarith : 1 < t + 1) using 1 <;> ring
  rw [hh.deriv] at hadjoint
  unfold deBruijnAdjointInitialDerivative
  field_simp [show t + 1 ≠ 0 by linarith]
  linarith

theorem deBruijnAdjoint_initial_identity :
    deBruijnAdjointFunction 1 +
      (∫ u in (1 : Real)..2, deBruijnAdjointFunction u / u) =
        deBruijnAdjointFunction 0 := by
  have hcont : ContinuousOn deBruijnAdjointFunction (Set.Icc (0 : Real) 1) :=
    deBruijnAdjointFunction_continuousOn_Ici.mono (by
      intro t ht
      exact ht.1)
  have hdCont : ContinuousOn deBruijnAdjointInitialDerivative
      (Set.Icc (0 : Real) 1) := by
    intro t ht
    unfold deBruijnAdjointInitialDerivative
    have hshift : ContinuousAt (fun x : Real => x + 1) t := by fun_prop
    have hh : ContinuousAt deBruijnAdjointFunction (t + 1) :=
      (deBruijnAdjointFunction_hasDerivAt (by linarith [ht.1])).continuousAt
    have hcompH : ContinuousAt
        (fun x : Real => deBruijnAdjointFunction (x + 1)) t :=
      ContinuousAt.comp (f := fun x : Real => x + 1)
        (g := deBruijnAdjointFunction) hh hshift
    exact (hcompH.neg.div hshift
      (show t + 1 ≠ 0 by linarith [ht.1])).continuousWithinAt
  have hdInt : IntervalIntegrable deBruijnAdjointInitialDerivative volume
      (0 : Real) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using hdCont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : Real) ≤ 1 by norm_num) hcont
    (fun t ht => deBruijnAdjointFunction_hasDerivAt_initial ht.1) hdInt
  have hshift :
      (∫ t in (0 : Real)..1, deBruijnAdjointInitialDerivative t) =
        -(∫ u in (1 : Real)..2, deBruijnAdjointFunction u / u) := by
    let q := fun u : Real => deBruijnAdjointFunction u / u
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := q) (a := (0 : Real)) (b := 1) 1
    calc
      (∫ t in (0 : Real)..1, deBruijnAdjointInitialDerivative t) =
          ∫ t in (0 : Real)..1, -q (t + 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        unfold deBruijnAdjointInitialDerivative q
        ring
      _ = -(∫ t in (0 : Real)..1, q (t + 1)) :=
        intervalIntegral.integral_neg
      _ = -(∫ u in (1 : Real)..2, deBruijnAdjointFunction u / u) := by
        rw [hcomp]
        norm_num
        rfl
  rw [hshift] at hftc
  linarith

theorem iwaniecBuchstabScaled_two :
    iwaniecBuchstabScaled 2 = 1 := by
  unfold iwaniecBuchstabScaled
  rw [iwaniecWExtended_two]
  field_simp [iwaniecSieveNormalizationC_pos.ne']
  ring

theorem iwaniecBuchstabInvariant_one_eq_adjoint_zero :
    iwaniecBuchstabInvariant 1 = deBruijnAdjointFunction 0 := by
  unfold iwaniecBuchstabInvariant
  norm_num
  rw [iwaniecBuchstabScaled_two]
  norm_num
  unfold iwaniecAdjointPairPrimitive
  rw [intervalIntegral.integral_congr (f := iwaniecAdjointPairIntegrand)
    (g := fun u : Real => deBruijnAdjointFunction u / u) (by
      intro u hu
      have huIcc : u ∈ Set.Icc (1 : Real) 2 := by
        simpa [Set.uIcc_of_le (by norm_num : (1 : Real) ≤ 2)] using hu
      unfold iwaniecAdjointPairIntegrand
      rw [iwaniecBuchstabFunction_initial huIcc.1 huIcc.2]
      ring)]
  simp only [intervalIntegral.integral_same, sub_zero]
  rw [← deBruijnAdjointFunction_zero]
  exact deBruijnAdjoint_initial_identity

theorem iwaniecBuchstab_limit_value :
    2 / iwaniecSieveNormalizationC =
      Real.exp (-Real.eulerMascheroniConstant) := by
  rw [← deBruijnAdjointFunction_zero]
  rw [← iwaniecBuchstabInvariant_one_eq_adjoint_zero]
  exact iwaniecBuchstabInvariant_one_eq_limit.symm

theorem iwaniecSieveNormalizationC_value :
    iwaniecSieveNormalizationC =
      2 * Real.exp Real.eulerMascheroniConstant := by
  have h := iwaniecBuchstab_limit_value
  have hC : iwaniecSieveNormalizationC ≠ 0 := iwaniecSieveNormalizationC_pos.ne'
  field_simp [hC] at h
  have hexp : Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    iwaniecSieveNormalizationC = iwaniecSieveNormalizationC * 1 := by ring
    _ = iwaniecSieveNormalizationC *
        (Real.exp (-Real.eulerMascheroniConstant) *
          Real.exp Real.eulerMascheroniConstant) := by rw [hexp]
    _ = (iwaniecSieveNormalizationC *
        Real.exp (-Real.eulerMascheroniConstant)) *
          Real.exp Real.eulerMascheroniConstant := by ring
    _ = 2 * Real.exp Real.eulerMascheroniConstant := by rw [← h]

theorem iwaniecOddSieveSeries_three_value :
    iwaniecOddSieveSeries 3 =
      2 * Real.exp Real.eulerMascheroniConstant - 3 := by
  have h := iwaniecSieveNormalizationC_value
  unfold iwaniecSieveNormalizationC at h
  linarith

theorem iwaniecEvenSieveSeries_explicit
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecEvenSieveSeries s =
      s - 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) := by
  have hsPos : 0 < s - 1 := by linarith
  have htwo := iwaniecEvenSieveSeries_local_formula
    (le_refl (2 : Real)) (by norm_num : (2 : Real) ≤ 4)
  have hs := iwaniecEvenSieveSeries_local_formula hlower hupper
  have hC := iwaniecSieveNormalizationC_value
  have hC' : iwaniecOddSieveSeries 3 + 3 =
      2 * Real.exp Real.eulerMascheroniConstant := by
    simpa [iwaniecSieveNormalizationC] using hC
  unfold iwaniecSieveNormalizationC at htwo hs
  rw [iwaniecEvenSieveSeries_two] at htwo
  rw [Real.log_div (by norm_num : (3 : Real) ≠ 0) hsPos.ne'] at hs
  norm_num at htwo
  rw [hC'] at htwo hs
  linarith

end

end Erdos1212Kernel
