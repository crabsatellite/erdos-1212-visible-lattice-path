import Erdos1212Kernel.IwaniecSieveMExtension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def iwaniecMPrimitive (s : Real) : Real :=
  ∫ x in (2 : Real)..s, iwaniecMExtended x

def iwaniecMConservation (s : Real) : Real :=
  (s - 1) * iwaniecMExtended s -
    (iwaniecMPrimitive s - iwaniecMPrimitive (s - 1))

theorem iwaniecMExtended_intervalIntegrable
    {a b : Real} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable iwaniecMExtended volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply iwaniecMExtended_continuousOn.mono
  intro x hx
  have hmin : 2 ≤ min a b := le_min ha hb
  exact hmin.trans hx.1

theorem iwaniecMExtended_continuousAt
    {s : Real} (hs : 2 < s) :
    ContinuousAt iwaniecMExtended s :=
  iwaniecMExtended_continuousOn.continuousAt (Ici_mem_nhds hs)

theorem iwaniecMPrimitive_hasDerivAt
    {s : Real} (hs : 2 < s) :
    HasDerivAt iwaniecMPrimitive (iwaniecMExtended s) s := by
  have hcontIoi : ContinuousOn iwaniecMExtended (Set.Ioi (2 : Real)) :=
    iwaniecMExtended_continuousOn.mono Set.Ioi_subset_Ici_self
  unfold iwaniecMPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (iwaniecMExtended_intervalIntegrable (le_refl 2) hs.le)
    (hcontIoi.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (iwaniecMExtended_continuousAt hs)

theorem iwaniecMPrimitive_sub_shift_eq_window
    {s : Real} (hs : 3 ≤ s) :
    iwaniecMPrimitive s - iwaniecMPrimitive (s - 1) =
      ∫ x in (s - 1)..s, iwaniecMExtended x := by
  unfold iwaniecMPrimitive
  exact intervalIntegral.integral_interval_sub_left
    (iwaniecMExtended_intervalIntegrable (le_refl 2) (by linarith))
    (iwaniecMExtended_intervalIntegrable (le_refl 2) (by linarith))

theorem iwaniecMConservation_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecMConservation 0 s := by
  have hM := iwaniecMExtended_hasDerivAt hs
  have hfactor : HasDerivAt (fun x : Real => x - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hproduct := hfactor.mul hM
  have hprimRight := iwaniecMPrimitive_hasDerivAt (by linarith : 2 < s)
  have hprimLeft := (iwaniecMPrimitive_hasDerivAt
      (by linarith : 2 < s - 1)).comp s hfactor
  have hwindow := hprimRight.sub hprimLeft
  have hraw := hproduct.sub hwindow
  unfold iwaniecMConservation
  convert hraw using 1
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecMConservation_eq_of_three_lt
    {s t : Real} (hs : 3 < s) (ht : 3 < t) :
    iwaniecMConservation s = iwaniecMConservation t := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (iwaniecMConservation_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (iwaniecMConservation_hasDerivAt hx).deriv
  · exact hs
  · exact ht

theorem tendsto_iwaniecMExtended_atTop_zero :
    Tendsto iwaniecMExtended atTop (nhds 0) := by
  have hsum := tendsto_iwaniecEvenSieveSeries_atTop_zero.add
    tendsto_iwaniecOddSieveSeries_atTop_zero
  have heq : (fun s : Real =>
      iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s) =ᶠ[atTop]
      iwaniecMExtended := by
    filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    exact (iwaniecMExtended_of_three_le hs).symm
  simpa only [zero_add] using hsum.congr' heq

def iwaniecMGeometricConstant : Real :=
  (iwaniecBaseA + Real.exp 1 / 3 * iwaniecBaseA) *
    (1 - iwaniecContractionA)⁻¹

theorem iwaniecMGeometricConstant_nonneg :
    0 ≤ iwaniecMGeometricConstant := by
  unfold iwaniecMGeometricConstant
  apply mul_nonneg
  · exact add_nonneg iwaniecBaseA_nonneg
      (mul_nonneg (by positivity) iwaniecBaseA_nonneg)
  · exact inv_nonneg.mpr (sub_nonneg.mpr iwaniecContractionA_lt_one.le)

theorem iwaniecMExtended_le_geometric
    {s : Real} (hs : 3 ≤ s) :
    iwaniecMExtended s ≤
      iwaniecMGeometricConstant * (s * Real.exp (-s)) := by
  have heven := iwaniecEvenSieveSeries_le_geometric (by linarith : 2 ≤ s)
  have hodd := iwaniecOddSieveSeries_le_geometric (by linarith : 1 ≤ s)
  rw [iwaniecMExtended_of_three_le hs]
  calc
    iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s ≤
        ((iwaniecBaseA * s * Real.exp (-s)) *
          (1 - iwaniecContractionA)⁻¹) +
        ((Real.exp 1 / 3 * iwaniecBaseA * s * Real.exp (-s)) *
          (1 - iwaniecContractionA)⁻¹) := add_le_add heven hodd
    _ = iwaniecMGeometricConstant * (s * Real.exp (-s)) := by
      unfold iwaniecMGeometricConstant
      ring

theorem tendsto_sub_one_mul_iwaniecMExtended_atTop_zero :
    Tendsto (fun s : Real => (s - 1) * iwaniecMExtended s)
      atTop (nhds 0) := by
  let majorant := fun s : Real =>
    iwaniecMGeometricConstant * (s ^ 2 * Real.exp (-s))
  have hmajor : Tendsto majorant atTop (nhds 0) := by
    have hconst : Tendsto (fun _s : Real => iwaniecMGeometricConstant)
        atTop (nhds iwaniecMGeometricConstant) := tendsto_const_nhds
    simpa [majorant] using
      hconst.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2)
  apply squeeze_zero' (g := majorant)
  · filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    exact mul_nonneg (by linarith)
      (by
        rw [iwaniecMExtended_of_three_le hs]
        exact add_nonneg (iwaniecEvenSieveSeries_nonneg (by linarith))
          (iwaniecOddSieveSeries_nonneg (by linarith)))
  · filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    have hM := iwaniecMExtended_le_geometric hs
    calc
      (s - 1) * iwaniecMExtended s ≤
          (s - 1) * (iwaniecMGeometricConstant *
            (s * Real.exp (-s))) :=
        mul_le_mul_of_nonneg_left hM (by linarith)
      _ ≤ s * (iwaniecMGeometricConstant *
            (s * Real.exp (-s))) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        exact mul_nonneg iwaniecMGeometricConstant_nonneg
          (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = majorant s := by dsimp [majorant]; ring
  · exact hmajor

theorem tendsto_iwaniecMWindowIntegral_atTop_zero :
    Tendsto (fun s : Real => ∫ x in (s - 1)..s, iwaniecMExtended x)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.mp tendsto_iwaniecMExtended_atTop_zero
      (ε / 2) (half_pos hε) with ⟨A, hA⟩
  refine ⟨max (A + 1) 4, ?_⟩
  intro s hs
  have hsA : A + 1 ≤ s := (le_max_left _ _).trans hs
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s - 1) (b := s) (C := ε / 2) (f := iwaniecMExtended) (by
      intro x hx
      have hle : s - 1 ≤ x := by
        rw [Set.uIoc_of_le (by linarith : s - 1 ≤ s)] at hx
        exact hx.1.le
      have hdist := hA x (by linarith : A ≤ x)
      simpa [dist_eq_norm] using hdist.le)
  calc
    dist (∫ x in (s - 1)..s, iwaniecMExtended x) 0 =
        ‖∫ x in (s - 1)..s, iwaniecMExtended x‖ := by
      simpa using (dist_zero_right (∫ x in (s - 1)..s, iwaniecMExtended x))
    _ ≤ (ε / 2) * |s - (s - 1)| := hbound
    _ = ε / 2 := by rw [show s - (s - 1) = 1 by ring]; simp
    _ < ε := half_lt_self hε

theorem tendsto_iwaniecMConservation_atTop_zero :
    Tendsto iwaniecMConservation atTop (nhds 0) := by
  have hraw := tendsto_sub_one_mul_iwaniecMExtended_atTop_zero.sub
    tendsto_iwaniecMWindowIntegral_atTop_zero
  have heq : (fun s : Real =>
      (s - 1) * iwaniecMExtended s -
        ∫ x in (s - 1)..s, iwaniecMExtended x) =ᶠ[atTop]
      iwaniecMConservation := by
    filter_upwards [eventually_ge_atTop (3 : Real)] with s hs
    unfold iwaniecMConservation
    rw [iwaniecMPrimitive_sub_shift_eq_window hs]
  simpa only [sub_self] using hraw.congr' heq

theorem iwaniecMConservation_eq_zero_of_three_lt
    {s : Real} (hs : 3 < s) :
    iwaniecMConservation s = 0 := by
  have heq : (fun _t : Real => iwaniecMConservation s) =ᶠ[atTop]
      iwaniecMConservation := by
    filter_upwards [eventually_gt_atTop (3 : Real)] with t ht
    exact iwaniecMConservation_eq_of_three_lt hs ht
  have hsame : Tendsto iwaniecMConservation atTop
      (nhds (iwaniecMConservation s)) :=
    (tendsto_const_nhds : Tendsto (fun _t : Real => iwaniecMConservation s)
      atTop (nhds (iwaniecMConservation s))).congr' heq
  exact tendsto_nhds_unique hsame tendsto_iwaniecMConservation_atTop_zero

theorem iwaniecMPrimitive_continuousWithinAt_two :
    ContinuousWithinAt iwaniecMPrimitive (Set.Ici (2 : Real)) 2 := by
  have hlocal : ContinuousOn iwaniecMPrimitive (Set.Icc (2 : Real) 4) := by
    simpa [iwaniecMPrimitive, Set.uIcc_of_le (by norm_num : (2 : Real) ≤ 4)] using
      intervalIntegral.continuousOn_primitive_interval'
        (iwaniecMExtended_intervalIntegrable (le_refl 2) (by norm_num : (2 : Real) ≤ 4))
        (show (2 : Real) ∈ Set.uIcc 2 4 by simp)
  have hsets : Set.Icc (2 : Real) 4 =ᶠ[nhds (2 : Real)] Set.Ici 2 := by
    filter_upwards [Iic_mem_nhds (show (2 : Real) < 4 by norm_num)] with x hx
    apply propext
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, hx⟩
  exact (hlocal 2 (show (2 : Real) ∈ Set.Icc 2 4 by constructor <;> norm_num)).congr_set hsets

theorem iwaniecMConservation_continuousWithinAt_three :
    ContinuousWithinAt iwaniecMConservation (Set.Ioi (3 : Real)) 3 := by
  have hM : ContinuousAt iwaniecMExtended 3 :=
    iwaniecMExtended_continuousAt (by norm_num)
  have hfactor : ContinuousAt (fun s : Real => s - 1) 3 := by fun_prop
  have hproduct : ContinuousAt
      (fun s : Real => (s - 1) * iwaniecMExtended s) 3 := hfactor.mul hM
  have hprimRight : ContinuousAt iwaniecMPrimitive 3 :=
    (iwaniecMPrimitive_hasDerivAt (by norm_num)).continuousAt
  have hshift : ContinuousWithinAt (fun s : Real => s - 1)
      (Set.Ioi (3 : Real)) 3 := hfactor.continuousWithinAt
  have hmaps : Set.MapsTo (fun s : Real => s - 1)
      (Set.Ioi (3 : Real)) (Set.Ici (2 : Real)) := by
    intro s hs
    change 3 < s at hs
    exact (by linarith : 2 ≤ s - 1)
  have hprimLeft : ContinuousWithinAt
      (fun s : Real => iwaniecMPrimitive (s - 1)) (Set.Ioi (3 : Real)) 3 :=
    by
      simpa [Function.comp_def] using
        ContinuousWithinAt.comp_of_eq
          (f := fun s : Real => s - 1) (g := iwaniecMPrimitive)
          iwaniecMPrimitive_continuousWithinAt_two hshift hmaps (by norm_num)
  unfold iwaniecMConservation
  exact hproduct.continuousWithinAt.sub
    (hprimRight.continuousWithinAt.sub hprimLeft)

theorem iwaniecMConservation_three_eq_zero :
    iwaniecMConservation 3 = 0 := by
  have heq : iwaniecMConservation =ᶠ[nhdsWithin (3 : Real) (Set.Ioi 3)]
      (fun _s : Real => (0 : Real)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact iwaniecMConservation_eq_zero_of_three_lt hs
  have hzero : Tendsto iwaniecMConservation
      (nhdsWithin (3 : Real) (Set.Ioi 3)) (nhds 0) :=
    (tendsto_const_nhds : Tendsto (fun _s : Real => (0 : Real))
      (nhdsWithin (3 : Real) (Set.Ioi 3)) (nhds 0)).congr' heq.symm
  exact tendsto_nhds_unique iwaniecMConservation_continuousWithinAt_three.tendsto hzero

theorem integral_log_three_div_sub_one_two_three :
    (∫ x in (2 : Real)..3, Real.log (3 / (x - 1))) =
      1 + Real.log 3 - 2 * Real.log 2 := by
  rw [intervalIntegral.integral_comp_sub_right
    (f := fun u : Real => Real.log (3 / u)) 1]
  norm_num
  have hpoint :
      (∫ u in (1 : Real)..2, Real.log (3 / u)) =
        ∫ u in (1 : Real)..2, (Real.log 3 - Real.log u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    change Real.log (3 / u) = Real.log 3 - Real.log u
    have huIcc : u ∈ Set.Icc (1 : Real) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : Real) ≤ 2)] using hu
    rw [Real.log_div (by norm_num : (3 : Real) ≠ 0)
      (ne_of_gt ((by norm_num : (0 : Real) < 1).trans_le huIcc.1))]
  rw [hpoint]
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 1 2) intervalIntegrable_log']
  simp [integral_log]
  ring

theorem integral_iwaniecMExtended_two_three :
    (∫ x in (2 : Real)..3, iwaniecMExtended x) =
      (iwaniecEvenSieveSeries 4 + iwaniecSieveNormalizationC - 4) +
        iwaniecSieveNormalizationC *
          (1 + Real.log 3 - 2 * Real.log 2) := by
  let base := iwaniecEvenSieveSeries 4 + iwaniecSieveNormalizationC - 4
  let logTerm := fun x : Real => Real.log (3 / (x - 1))
  have hpoint :
      (∫ x in (2 : Real)..3, iwaniecMExtended x) =
        ∫ x in (2 : Real)..3,
          (base + iwaniecSieveNormalizationC * logTerm x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (2 : Real) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : Real) ≤ 3)] using hx
    rw [iwaniecMExtended_of_le_three hxIcc.2]
    rw [iwaniecEvenSieveSeries_local_formula hxIcc.1
      (hxIcc.2.trans (by norm_num : (3 : Real) ≤ 4))]
    dsimp [base, logTerm]
    unfold iwaniecSieveNormalizationC
    ring
  rw [hpoint]
  have hlogCont : ContinuousOn logTerm (Set.Icc (2 : Real) 3) := by
    intro x hx
    dsimp [logTerm]
    have hden : x - 1 ≠ 0 := by linarith [hx.1]
    have hsub : ContinuousAt (fun y : Real => y - 1) x := by fun_prop
    have hdiv : ContinuousAt (fun y : Real => 3 / (y - 1)) x :=
      continuousAt_const.div hsub hden
    exact (hdiv.log (div_ne_zero (by norm_num) hden)).continuousWithinAt
  have hlogInt : IntervalIntegrable logTerm volume (2 : Real) 3 :=
    by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le (by norm_num : (2 : Real) ≤ 3)] using hlogCont
  rw [intervalIntegral.integral_add
    (continuous_const.intervalIntegrable 2 3)
    (hlogInt.const_mul iwaniecSieveNormalizationC)]
  simp only [intervalIntegral.integral_const, sub_self, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  rw [integral_log_three_div_sub_one_two_three]
  dsimp [base, logTerm]
  ring

theorem iwaniecMConservation_three_eq_evenSeries_two_sub_two :
    iwaniecMConservation 3 = iwaniecEvenSieveSeries 2 - 2 := by
  have hfThree := iwaniecEvenSieveSeries_local_formula
    (by norm_num : (2 : Real) ≤ 3) (by norm_num : (3 : Real) ≤ 4)
  have hfTwo := iwaniecEvenSieveSeries_local_formula
    (le_refl (2 : Real)) (by norm_num : (2 : Real) ≤ 4)
  unfold iwaniecMConservation
  rw [iwaniecMPrimitive_sub_shift_eq_window (le_refl (3 : Real))]
  norm_num
  rw [iwaniecMExtended_of_three_le (le_refl (3 : Real))]
  rw [integral_iwaniecMExtended_two_three]
  rw [hfThree, hfTwo]
  unfold iwaniecSieveNormalizationC
  norm_num
  rw [Real.log_div (by norm_num : (3 : Real) ≠ 0)
    (by norm_num : (2 : Real) ≠ 0)]
  ring

theorem iwaniecEvenSieveSeries_two :
    iwaniecEvenSieveSeries 2 = 2 := by
  linarith [iwaniecMConservation_three_eq_zero,
    iwaniecMConservation_three_eq_evenSeries_two_sub_two]

end

end Erdos1212Kernel
