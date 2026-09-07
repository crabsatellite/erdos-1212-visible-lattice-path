import Erdos1212Kernel.IwaniecSieveMConservation

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def iwaniecWExtended (s : Real) : Real :=
  if s ≤ 2 then
    2 * s - iwaniecSieveNormalizationC
  else if s ≤ 3 then
    s - iwaniecSieveNormalizationC + iwaniecEvenSieveSeries s
  else
    iwaniecEvenSieveSeries s - iwaniecOddSieveSeries s

theorem iwaniecWExtended_of_le_two
    {s : Real} (hs : s ≤ 2) :
    iwaniecWExtended s = 2 * s - iwaniecSieveNormalizationC := by
  simp [iwaniecWExtended, hs]

theorem iwaniecWExtended_of_two_lt_of_le_three
    {s : Real} (hlower : 2 < s) (hupper : s ≤ 3) :
    iwaniecWExtended s =
      s - iwaniecSieveNormalizationC + iwaniecEvenSieveSeries s := by
  simp [iwaniecWExtended, not_le.mpr hlower, hupper]

theorem iwaniecWExtended_of_three_lt
    {s : Real} (hs : 3 < s) :
    iwaniecWExtended s =
      iwaniecEvenSieveSeries s - iwaniecOddSieveSeries s := by
  simp [iwaniecWExtended, not_le.mpr (by linarith : 2 < s), not_le.mpr hs]

theorem iwaniecWExtended_two :
    iwaniecWExtended 2 = 4 - iwaniecSieveNormalizationC := by
  rw [iwaniecWExtended_of_le_two (le_refl (2 : Real))]
  ring

theorem iwaniecWExtended_three :
    iwaniecWExtended 3 =
      iwaniecEvenSieveSeries 3 - iwaniecOddSieveSeries 3 := by
  unfold iwaniecWExtended iwaniecSieveNormalizationC
  norm_num
  ring

theorem iwaniecOddSieveSeries_hasDerivWithinAt_three_right :
    HasDerivWithinAt iwaniecOddSieveSeries
      (-iwaniecEvenSeriesKernel 3) (Set.Ici (3 : Real)) 3 := by
  let kernel := iwaniecEvenSeriesKernel
  have hcontOn : ContinuousOn kernel (Set.Ici (3 : Real)) :=
    iwaniecEvenSeriesKernel_continuousOn_Ici
  have hcont : ContinuousWithinAt kernel (Set.Ioi (3 : Real)) 3 :=
    (hcontOn 3 (by simp)).mono Set.Ioi_subset_Ici_self
  have hmeas : StronglyMeasurableAtFilter kernel
      (nhdsWithin (3 : Real) (Set.Ioi 3)) := by
    exact ⟨Set.Ioi 3, self_mem_nhdsWithin,
      (hcontOn.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
  have hprim : HasDerivWithinAt
      (fun u : Real => ∫ x in (3 : Real)..u, kernel x)
      (kernel 3) (Set.Ici (3 : Real)) 3 :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (by rw [intervalIntegrable_iff]; simp : IntervalIntegrable kernel volume 3 3)
      hmeas hcont
  let model := fun u : Real =>
    (∫ x in Set.Ioi (3 : Real), kernel x) - ∫ x in (3 : Real)..u, kernel x
  have hmodel : HasDerivWithinAt model (-kernel 3) (Set.Ici (3 : Real)) 3 := by
    dsimp [model]
    convert (hasDerivAt_const (3 : Real)
      (∫ x in Set.Ioi (3 : Real), kernel x)).hasDerivWithinAt.sub hprim using 1 <;>
      ring
  have heq : iwaniecOddSieveSeries =ᶠ[nhdsWithin (3 : Real) (Set.Ici 3)]
      model := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have huThree : 3 ≤ u := hu
    have hintThree : IntegrableOn kernel (Set.Ioi (3 : Real)) :=
      integrableOn_iwaniecEvenSeriesKernel_Ioi (le_refl 3)
    have hintU : IntegrableOn kernel (Set.Ioi u) :=
      integrableOn_iwaniecEvenSeriesKernel_Ioi huThree
    have hadd := integral_interval_add_Ioi hintThree hintU
    rw [iwaniecOddSieveSeries_eq_integral_Ioi huThree]
    change (∫ x in Set.Ioi u, kernel x) = model u
    dsimp [model]
    linarith
  apply hmodel.congr_of_eventuallyEq heq
  rw [iwaniecOddSieveSeries_eq_integral_Ioi (le_refl (3 : Real))]
  change (∫ x in Set.Ioi (3 : Real), kernel x) = model 3
  dsimp [model]
  simp

theorem iwaniecWExtended_hasDerivAt_of_two_lt_of_lt_three
    {s : Real} (hlower : 2 < s) (hupper : s < 3) :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (s - 1) / (s - 1)) s := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_lt_four hlower
    (by linarith : s < 4)
  have hmodel := ((hasDerivAt_id s).sub_const iwaniecSieveNormalizationC).add hf
  have heq : iwaniecWExtended =ᶠ[nhds s]
      (fun x : Real => x - iwaniecSieveNormalizationC + iwaniecEvenSieveSeries x) := by
    filter_upwards [Ioo_mem_nhds hlower hupper] with x hx
    exact iwaniecWExtended_of_two_lt_of_le_three hx.1 hx.2.le
  have hraw := hmodel.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecWExtended_of_le_two (by linarith : s - 1 ≤ 2)]
  unfold iwaniecOddSeriesKernel iwaniecSieveNormalizationC
  rw [iwaniecOddSieveSeries_eq_three (by linarith : 1 ≤ s - 1)
    (by linarith : s - 1 ≤ 3)]
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecWExtended_hasDerivAt_three :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (3 - 1) / (3 - 1)) 3 := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_lt_four
    (by norm_num : (2 : Real) < 3) (by norm_num : (3 : Real) < 4)
  have hleftModel := ((hasDerivAt_id (3 : Real)).sub_const
    iwaniecSieveNormalizationC).add hf
  have hleft : HasDerivWithinAt iwaniecWExtended
      (iwaniecWExtended (3 - 1) / (3 - 1)) (Set.Iic (3 : Real)) 3 := by
    have heq : iwaniecWExtended =ᶠ[nhdsWithin (3 : Real) (Set.Iic 3)]
        (fun x : Real =>
          x - iwaniecSieveNormalizationC + iwaniecEvenSieveSeries x) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Ioi_mem_nhds (show (2 : Real) < 3 by norm_num)),
        self_mem_nhdsWithin] with x hxLower hxUpper
      exact iwaniecWExtended_of_two_lt_of_le_three hxLower hxUpper
    have htemp := hleftModel.hasDerivWithinAt.congr_of_eventuallyEq heq (by
      rw [iwaniecWExtended_three]
      unfold iwaniecSieveNormalizationC
      simp only [Pi.add_apply, id_eq]
      ring)
    refine htemp.congr_deriv ?_
    norm_num
    rw [iwaniecWExtended_two]
    unfold iwaniecOddSeriesKernel iwaniecSieveNormalizationC
    norm_num
    rw [iwaniecOddSieveSeries_eq_three (by norm_num : (1 : Real) ≤ 2)
      (by norm_num : (2 : Real) ≤ 3)]
    ring
  have hrightModel := hf.hasDerivWithinAt.sub
    iwaniecOddSieveSeries_hasDerivWithinAt_three_right
  have hright : HasDerivWithinAt iwaniecWExtended
      (iwaniecWExtended (3 - 1) / (3 - 1)) (Set.Ici (3 : Real)) 3 := by
    have htemp := hrightModel.congr_of_mem
      (f₁ := iwaniecWExtended) (by
        intro x hx
        change 3 ≤ x at hx
        rcases hx.eq_or_lt with heq | hlt
        · subst x
          exact iwaniecWExtended_three
        · exact iwaniecWExtended_of_three_lt hlt)
      (by simp)
    refine htemp.congr_deriv ?_
    norm_num
    rw [iwaniecWExtended_two]
    unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
    norm_num
    rw [iwaniecOddSieveSeries_eq_three (by norm_num : (1 : Real) ≤ 2)
      (by norm_num : (2 : Real) ≤ 3)]
    rw [iwaniecEvenSieveSeries_two]
    unfold iwaniecSieveNormalizationC
    ring
  simpa using hleft.union hright

theorem iwaniecWExtended_hasDerivAt_of_three_lt_of_lt_four
    {s : Real} (hlower : 3 < s) (hupper : s < 4) :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (s - 1) / (s - 1)) s := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_lt_four
    (by linarith : 2 < s) hupper
  have hF := iwaniecOddSieveSeries_hasDerivAt hlower
  have hmodel := hf.sub hF
  have heq : iwaniecWExtended =ᶠ[nhds s]
      (fun x : Real => iwaniecEvenSieveSeries x - iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds hlower] with x hx
    exact iwaniecWExtended_of_three_lt hx
  have hraw := hmodel.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecWExtended_of_two_lt_of_le_three (by linarith : 2 < s - 1)
    (by linarith : s - 1 ≤ 3)]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  rw [iwaniecOddSieveSeries_eq_three (by linarith : 1 ≤ s - 1)
    (by linarith : s - 1 ≤ 3)]
  unfold iwaniecSieveNormalizationC
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecWExtended_hasDerivAt_four :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (4 - 1) / (4 - 1)) 4 := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_four
  have hF := iwaniecOddSieveSeries_hasDerivAt (by norm_num : (3 : Real) < 4)
  have hmodel := hf.sub hF
  have heq : iwaniecWExtended =ᶠ[nhds (4 : Real)]
      (fun x : Real => iwaniecEvenSieveSeries x - iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds (show (3 : Real) < 4 by norm_num)] with x hx
    exact iwaniecWExtended_of_three_lt hx
  have hraw := hmodel.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  norm_num
  rw [iwaniecWExtended_three]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  norm_num
  ring

theorem iwaniecWExtended_hasDerivAt_of_four_lt
    {s : Real} (hs : 4 < s) :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (s - 1) / (s - 1)) s := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_four_lt hs
  have hF := iwaniecOddSieveSeries_hasDerivAt (by linarith : 3 < s)
  have hmodel := hf.sub hF
  have heq : iwaniecWExtended =ᶠ[nhds s]
      (fun x : Real => iwaniecEvenSieveSeries x - iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds (by linarith : 3 < s)] with x hx
    exact iwaniecWExtended_of_three_lt hx
  have hraw := hmodel.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecWExtended_of_three_lt (by linarith : 3 < s - 1)]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecWExtended_hasDerivAt
    {s : Real} (hs : 2 < s) :
    HasDerivAt iwaniecWExtended
      (iwaniecWExtended (s - 1) / (s - 1)) s := by
  rcases lt_trichotomy s 3 with hlt3 | heq3 | hgt3
  · exact iwaniecWExtended_hasDerivAt_of_two_lt_of_lt_three hs hlt3
  · subst s
    exact iwaniecWExtended_hasDerivAt_three
  · rcases lt_trichotomy s 4 with hlt4 | heq4 | hgt4
    · exact iwaniecWExtended_hasDerivAt_of_three_lt_of_lt_four hgt3 hlt4
    · subst s
      exact iwaniecWExtended_hasDerivAt_four
    · exact iwaniecWExtended_hasDerivAt_of_four_lt hgt4

theorem iwaniecWExtended_continuousOn :
    ContinuousOn iwaniecWExtended (Set.Ici (1 : Real)) := by
  let low := fun s : Real => 2 * s - iwaniecSieveNormalizationC
  let middle := fun s : Real =>
    s - iwaniecSieveNormalizationC + iwaniecEvenSieveSeries s
  let high := fun s : Real =>
    iwaniecEvenSieveSeries s - iwaniecOddSieveSeries s
  let right := fun s : Real => if s ≤ 3 then middle s else high s
  have hright : ContinuousOn right (Set.Ici (2 : Real)) := by
    apply ContinuousOn.if (p := fun s : Real => s ≤ 3)
    · intro s hs
      have hset : {t : Real | t ≤ 3} = Set.Iic 3 := by ext; simp
      have hsFront : s ∈ frontier (Set.Iic (3 : Real)) := by
        simpa [hset] using hs.2
      have hsEq : s = 3 := by simpa using frontier_Iic_subset (3 : Real) hsFront
      subst s
      dsimp [middle, high]
      unfold iwaniecSieveNormalizationC
      ring
    · have hmiddle : ContinuousOn middle (Set.Ici (2 : Real)) := by
        dsimp [middle]
        exact (continuousOn_id.sub continuousOn_const).add
          iwaniecEvenSieveSeries_continuousOn
      exact hmiddle.mono Set.inter_subset_left
    · have hhigh : ContinuousOn high (Set.Ici (3 : Real)) := by
        dsimp [high]
        exact (iwaniecEvenSieveSeries_continuousOn.mono
          (Set.Ici_subset_Ici.mpr (by norm_num))).sub
          (iwaniecOddSieveSeries_continuousOn.mono
            (Set.Ici_subset_Ici.mpr (by norm_num)))
      apply hhigh.mono
      intro s hs
      have hsClosure := hs.2
      have hset : {t : Real | ¬t ≤ 3} = Set.Ioi 3 := by ext; simp
      rw [hset, closure_Ioi] at hsClosure
      exact hsClosure
  have hall : ContinuousOn (fun s : Real => if s ≤ 2 then low s else right s)
      (Set.Ici (1 : Real)) := by
    apply ContinuousOn.if (p := fun s : Real => s ≤ 2)
    · intro s hs
      have hset : {t : Real | t ≤ 2} = Set.Iic 2 := by ext; simp
      have hsFront : s ∈ frontier (Set.Iic (2 : Real)) := by
        simpa [hset] using hs.2
      have hsEq : s = 2 := by simpa using frontier_Iic_subset (2 : Real) hsFront
      subst s
      dsimp [low, right, middle]
      rw [iwaniecEvenSieveSeries_two]
      norm_num
      ring
    · have hlow : ContinuousOn low (Set.Ici (1 : Real)) := by
        dsimp [low]
        exact (continuousOn_const.mul continuousOn_id).sub continuousOn_const
      exact hlow.mono Set.inter_subset_left
    · apply hright.mono
      intro s hs
      have hsClosure := hs.2
      have hset : {t : Real | ¬t ≤ 2} = Set.Ioi 2 := by ext; simp
      rw [hset, closure_Ioi] at hsClosure
      exact hsClosure
  apply hall.congr
  intro s _hs
  by_cases htwo : s ≤ 2
  · simp [iwaniecWExtended, htwo, low]
  · by_cases hthree : s ≤ 3
    · simp [iwaniecWExtended, htwo, hthree, right, middle]
    · simp [iwaniecWExtended, htwo, hthree, right, high]

def iwaniecBuchstabScaled (s : Real) : Real :=
  (2 * s - iwaniecWExtended s) / iwaniecSieveNormalizationC

def iwaniecBuchstabFunction (s : Real) : Real :=
  iwaniecBuchstabScaled s / s

theorem iwaniecBuchstabFunction_initial
    {s : Real} (hlower : 1 ≤ s) (hupper : s ≤ 2) :
    iwaniecBuchstabFunction s = 1 / s := by
  unfold iwaniecBuchstabFunction iwaniecBuchstabScaled
  rw [iwaniecWExtended_of_le_two hupper]
  field_simp [iwaniecSieveNormalizationC_pos.ne', (by linarith : s ≠ 0)]
  ring

theorem iwaniecBuchstabScaled_hasDerivAt
    {s : Real} (hs : 2 < s) :
    HasDerivAt iwaniecBuchstabScaled (iwaniecBuchstabFunction (s - 1)) s := by
  have hW := iwaniecWExtended_hasDerivAt hs
  have hnum := (hasDerivAt_id s).const_mul 2 |>.sub hW
  have hraw := hnum.div_const iwaniecSieveNormalizationC
  unfold iwaniecBuchstabFunction
  unfold iwaniecBuchstabScaled
  refine hraw.congr_deriv ?_
  field_simp [iwaniecSieveNormalizationC_pos.ne',
    show s - 1 ≠ 0 by linarith]

theorem iwaniecBuchstab_mul_hasDerivAt
    {s : Real} (hs : 2 < s) :
    HasDerivAt (fun u : Real => u * iwaniecBuchstabFunction u)
      (iwaniecBuchstabFunction (s - 1)) s := by
  have hscaled := iwaniecBuchstabScaled_hasDerivAt hs
  have heq : (fun u : Real => u * iwaniecBuchstabFunction u) =ᶠ[nhds s]
      iwaniecBuchstabScaled := by
    filter_upwards [Ioi_mem_nhds (by linarith : (0 : Real) < s)] with u hu
    unfold iwaniecBuchstabFunction
    have huPos : 0 < u := hu
    field_simp [huPos.ne']
  exact hscaled.congr_of_eventuallyEq heq

theorem iwaniecBuchstabFunction_continuousOn :
    ContinuousOn iwaniecBuchstabFunction (Set.Ioi (1 : Real)) := by
  have hW : ContinuousOn iwaniecWExtended (Set.Ioi (1 : Real)) :=
    iwaniecWExtended_continuousOn.mono Set.Ioi_subset_Ici_self
  have hscaled : ContinuousOn iwaniecBuchstabScaled (Set.Ioi (1 : Real)) := by
    unfold iwaniecBuchstabScaled
    exact ((continuousOn_const.mul continuousOn_id).sub hW).div_const
      iwaniecSieveNormalizationC
  unfold iwaniecBuchstabFunction
  apply hscaled.div continuousOn_id
  intro s hs
  have hs' : 1 < s := hs
  simpa using (ne_of_gt (zero_lt_one.trans hs'))

theorem iwaniecBuchstabFunction_continuousOn_Ici :
    ContinuousOn iwaniecBuchstabFunction (Set.Ici (1 : Real)) := by
  have hscaled : ContinuousOn iwaniecBuchstabScaled (Set.Ici (1 : Real)) := by
    unfold iwaniecBuchstabScaled
    exact ((continuousOn_const.mul continuousOn_id).sub
      iwaniecWExtended_continuousOn).div_const iwaniecSieveNormalizationC
  unfold iwaniecBuchstabFunction
  apply hscaled.div continuousOn_id
  intro s hs
  have hs' : 1 ≤ s := hs
  exact ne_of_gt (zero_lt_one.trans_le hs')

theorem tendsto_iwaniecWExtended_atTop_zero :
    Tendsto iwaniecWExtended atTop (nhds 0) := by
  have hdiff := tendsto_iwaniecEvenSieveSeries_atTop_zero.sub
    tendsto_iwaniecOddSieveSeries_atTop_zero
  have heq : (fun s : Real =>
      iwaniecEvenSieveSeries s - iwaniecOddSieveSeries s) =ᶠ[atTop]
      iwaniecWExtended := by
    filter_upwards [eventually_gt_atTop (3 : Real)] with s hs
    exact (iwaniecWExtended_of_three_lt hs).symm
  simpa only [sub_self] using hdiff.congr' heq

theorem tendsto_iwaniecBuchstabFunction_atTop :
    Tendsto iwaniecBuchstabFunction atTop
      (nhds (2 / iwaniecSieveNormalizationC)) := by
  have hinv : Tendsto (fun s : Real => s⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have herror : Tendsto
      (fun s : Real =>
        iwaniecWExtended s * s⁻¹ * iwaniecSieveNormalizationC⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_iwaniecWExtended_atTop_zero.mul hinv).mul
      (tendsto_const_nhds : Tendsto
        (fun _s : Real => iwaniecSieveNormalizationC⁻¹) atTop
        (nhds iwaniecSieveNormalizationC⁻¹))
  have hraw := (tendsto_const_nhds : Tendsto
      (fun _s : Real => 2 / iwaniecSieveNormalizationC) atTop
      (nhds (2 / iwaniecSieveNormalizationC))).sub herror
  have heq : (fun s : Real =>
      2 / iwaniecSieveNormalizationC -
        iwaniecWExtended s * s⁻¹ * iwaniecSieveNormalizationC⁻¹) =ᶠ[atTop]
      iwaniecBuchstabFunction := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with s hs
    unfold iwaniecBuchstabFunction
    unfold iwaniecBuchstabScaled
    field_simp [hs.ne', iwaniecSieveNormalizationC_pos.ne']
  simpa only [sub_zero] using hraw.congr' heq

end

end Erdos1212Kernel
