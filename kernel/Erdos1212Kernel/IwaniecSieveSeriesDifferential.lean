import Erdos1212Kernel.IwaniecSieveSeriesRegularity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def iwaniecOddSeriesKernel (t : Real) : Real :=
  iwaniecOddSieveSeries (t - 1) / (t - 1)

def iwaniecEvenSeriesKernel (t : Real) : Real :=
  iwaniecEvenSieveSeries (t - 1) / (t - 1)

theorem iwaniecOddSeriesKernel_continuousOn_Ici :
    ContinuousOn iwaniecOddSeriesKernel (Set.Ici (2 : Real)) := by
  have hsub : ContinuousOn (fun t : Real => t - 1) (Set.Ici (2 : Real)) := by
    fun_prop
  have hshift : ContinuousOn (fun t : Real => iwaniecOddSieveSeries (t - 1))
      (Set.Ici (2 : Real)) := by
    apply iwaniecOddSieveSeries_continuousOn.comp hsub
    intro t ht
    have ht' : 2 ≤ t := ht
    change 1 ≤ t - 1
    linarith
  unfold iwaniecOddSeriesKernel
  apply hshift.div hsub
  intro t ht
  have ht' : 2 ≤ t := ht
  change t - 1 ≠ 0
  linarith

theorem iwaniecEvenSeriesKernel_continuousOn_Ici :
    ContinuousOn iwaniecEvenSeriesKernel (Set.Ici (3 : Real)) := by
  have hsub : ContinuousOn (fun t : Real => t - 1) (Set.Ici (3 : Real)) := by
    fun_prop
  have hshift : ContinuousOn (fun t : Real => iwaniecEvenSieveSeries (t - 1))
      (Set.Ici (3 : Real)) := by
    apply iwaniecEvenSieveSeries_continuousOn.comp hsub
    intro t ht
    have ht' : 3 ≤ t := ht
    change 2 ≤ t - 1
    linarith
  unfold iwaniecEvenSeriesKernel
  apply hshift.div hsub
  intro t ht
  have ht' : 3 ≤ t := ht
  change t - 1 ≠ 0
  linarith

theorem iwaniecOddSeriesKernel_nonneg
    {t : Real} (ht : 2 ≤ t) :
    0 ≤ iwaniecOddSeriesKernel t := by
  unfold iwaniecOddSeriesKernel
  exact div_nonneg (iwaniecOddSieveSeries_nonneg (by linarith)) (by linarith)

theorem iwaniecEvenSeriesKernel_nonneg
    {t : Real} (ht : 3 ≤ t) :
    0 ≤ iwaniecEvenSeriesKernel t := by
  unfold iwaniecEvenSeriesKernel
  exact div_nonneg (iwaniecEvenSieveSeries_nonneg (by linarith)) (by linarith)

theorem integrableOn_iwaniecOddSeriesKernel_Ioi
    {s : Real} (hs : 2 ≤ s) :
    IntegrableOn iwaniecOddSeriesKernel (Set.Ioi s) := by
  let P := Real.exp 1 / 3 * iwaniecBaseA *
    (1 - iwaniecContractionA)⁻¹
  let D := P * Real.exp 1
  let majorant := fun t : Real => D * Real.exp (-t)
  have hmajorant : IntegrableOn majorant (Set.Ioi s) := by
    have hbase := exp_neg_integrableOn_Ioi s (show (0 : Real) < 1 by norm_num)
    simpa [majorant] using hbase.const_mul D
  apply hmajorant.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply iwaniecOddSeriesKernel_continuousOn_Ici.mono
    intro t ht
    exact hs.trans ht.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htS : s < t := ht
    have htTwo : 2 ≤ t := hs.trans htS.le
    have hden : 0 < t - 1 := by linarith
    have hseries := iwaniecOddSieveSeries_le_geometric (by linarith : 1 ≤ t - 1)
    have hPNonneg : 0 ≤ P := by
      dsimp [P]
      have hinv : 0 ≤ (1 - iwaniecContractionA)⁻¹ := by
        exact inv_nonneg.mpr (sub_nonneg.mpr iwaniecContractionA_lt_one.le)
      exact mul_nonneg (mul_nonneg (by positivity) iwaniecBaseA_nonneg) hinv
    have hkernelNonneg := iwaniecOddSeriesKernel_nonneg htTwo
    rw [Real.norm_of_nonneg hkernelNonneg]
    apply (div_le_iff₀ hden).2
    dsimp [majorant, D, P]
    have hexp : Real.exp (-(t - 1)) = Real.exp 1 * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    rw [hexp] at hseries
    nlinarith

theorem integrableOn_iwaniecEvenSeriesKernel_Ioi
    {s : Real} (hs : 3 ≤ s) :
    IntegrableOn iwaniecEvenSeriesKernel (Set.Ioi s) := by
  let P := iwaniecBaseA * (1 - iwaniecContractionA)⁻¹
  let D := P * Real.exp 1
  let majorant := fun t : Real => D * Real.exp (-t)
  have hmajorant : IntegrableOn majorant (Set.Ioi s) := by
    have hbase := exp_neg_integrableOn_Ioi s (show (0 : Real) < 1 by norm_num)
    simpa [majorant] using hbase.const_mul D
  apply hmajorant.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply iwaniecEvenSeriesKernel_continuousOn_Ici.mono
    intro t ht
    exact hs.trans ht.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htS : s < t := ht
    have htThree : 3 ≤ t := hs.trans htS.le
    have hden : 0 < t - 1 := by linarith
    have hseries := iwaniecEvenSieveSeries_le_geometric (by linarith : 2 ≤ t - 1)
    have hPNonneg : 0 ≤ P := by
      dsimp [P]
      have hinv : 0 ≤ (1 - iwaniecContractionA)⁻¹ := by
        exact inv_nonneg.mpr (sub_nonneg.mpr iwaniecContractionA_lt_one.le)
      exact mul_nonneg iwaniecBaseA_nonneg hinv
    have hkernelNonneg := iwaniecEvenSeriesKernel_nonneg htThree
    rw [Real.norm_of_nonneg hkernelNonneg]
    apply (div_le_iff₀ hden).2
    dsimp [majorant, D, P]
    have hexp : Real.exp (-(t - 1)) = Real.exp 1 * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    rw [hexp] at hseries
    nlinarith

/-- A reusable FTC lemma for an improper tail with a locally continuous,
integrable kernel. -/
theorem hasDerivAt_integral_Ioi_of_integrableOn_of_continuousOn
    {kernel : Real → Real} {lower s : Real} (hls : lower < s)
    (hint : IntegrableOn kernel (Set.Ioi lower))
    (hcont : ContinuousOn kernel (Set.Ioi lower)) :
    HasDerivAt (fun a : Real => ∫ x in Set.Ioi a, kernel x) (-kernel s) s := by
  have hinterval : IntervalIntegrable kernel volume lower s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hls.le]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  have hcontAt : ContinuousAt kernel s :=
    isOpen_Ioi.continuousOn_iff.mp hcont hls
  have hmeas : StronglyMeasurableAtFilter kernel (nhds s) :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi s hls
  have hprimitive := intervalIntegral.integral_hasDerivAt_right
    hinterval hmeas hcontAt
  let tailModel := fun a : Real =>
    (∫ x in Set.Ioi lower, kernel x) - ∫ x in lower..a, kernel x
  have hlocal : HasDerivAt tailModel (-kernel s) s := by
    dsimp [tailModel]
    convert (hasDerivAt_const s (∫ x in Set.Ioi lower, kernel x)).sub hprimitive using 1 <;>
      ring
  have heq : (fun a : Real => ∫ x in Set.Ioi a, kernel x) =ᶠ[nhds s] tailModel := by
    filter_upwards [Ioi_mem_nhds hls] with a ha
    have hinta : IntegrableOn kernel (Set.Ioi a) :=
      hint.mono_set (Set.Ioi_subset_Ioi ha.le)
    have hadd := integral_interval_add_Ioi hint hinta
    dsimp [tailModel]
    linarith
  exact hlocal.congr_of_eventuallyEq heq

theorem iwaniecOddSeriesTail_hasDerivAt
    {s : Real} (hs : 2 < s) :
    HasDerivAt (fun a : Real => ∫ t in Set.Ioi a, iwaniecOddSeriesKernel t)
      (-iwaniecOddSeriesKernel s) s := by
  let lower := (s + 2) / 2
  have hlower : 2 ≤ lower := by dsimp [lower]; linarith
  have hls : lower < s := by dsimp [lower]; linarith
  exact hasDerivAt_integral_Ioi_of_integrableOn_of_continuousOn hls
    (integrableOn_iwaniecOddSeriesKernel_Ioi hlower)
    (iwaniecOddSeriesKernel_continuousOn_Ici.mono (by
      intro t ht
      exact hlower.trans ht.le))

theorem iwaniecEvenSeriesTail_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt (fun a : Real => ∫ t in Set.Ioi a, iwaniecEvenSeriesKernel t)
      (-iwaniecEvenSeriesKernel s) s := by
  let lower := (s + 3) / 2
  have hlower : 3 ≤ lower := by dsimp [lower]; linarith
  have hls : lower < s := by dsimp [lower]; linarith
  exact hasDerivAt_integral_Ioi_of_integrableOn_of_continuousOn hls
    (integrableOn_iwaniecEvenSeriesKernel_Ioi hlower)
    (iwaniecEvenSeriesKernel_continuousOn_Ici.mono (by
      intro t ht
      exact hlower.trans ht.le))

theorem iwaniecOddSieveSeries_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecOddSieveSeries (-iwaniecEvenSeriesKernel s) s := by
  have htail := iwaniecEvenSeriesTail_hasDerivAt hs
  have heq : iwaniecOddSieveSeries =ᶠ[nhds s]
      (fun a : Real => ∫ t in Set.Ioi a, iwaniecEvenSeriesKernel t) := by
    filter_upwards [Ioi_mem_nhds hs] with a ha
    exact iwaniecOddSieveSeries_eq_integral_Ioi ha.le
  exact htail.congr_of_eventuallyEq heq

theorem iwaniecGTwo_hasDerivAt_of_two_lt_of_lt_four
    {s : Real} (hlower : 2 < s) (hupper : s < 4) :
    HasDerivAt iwaniecGTwo (1 - 3 / (s - 1)) s := by
  let formula := fun x : Real => 3 * Real.log (3 / (x - 1)) + x - 4
  have hden : s - 1 ≠ 0 := by linarith
  have hsub : HasDerivAt (fun x : Real => x - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hinner : HasDerivAt (fun x : Real => 3 / (x - 1))
      (-3 / (s - 1) ^ 2) s := by
    convert (hasDerivAt_const s (3 : Real)).div hsub hden using 1 <;>
      field_simp <;> ring
  have hinnerNe : (3 : Real) / (s - 1) ≠ 0 :=
    div_ne_zero (by norm_num) hden
  have hraw := ((hinner.log hinnerNe).const_mul 3).add
      (hasDerivAt_id s) |>.sub_const 4
  have hformula : HasDerivAt formula (1 - 3 / (s - 1)) s := by
    dsimp [formula]
    convert hraw using 1
    field_simp [hden]
    ring
  have heq : iwaniecGTwo =ᶠ[nhds s] formula := by
    filter_upwards [Ioo_mem_nhds hlower hupper] with x hx
    exact iwaniecGTwo_eq hx.1.le hx.2.le
  exact hformula.congr_of_eventuallyEq heq

theorem iwaniecGTwo_hasDerivAt_of_four_lt
    {s : Real} (hs : 4 < s) :
    HasDerivAt iwaniecGTwo 0 s := by
  have hzero := hasDerivAt_const s (0 : Real)
  have heq : iwaniecGTwo =ᶠ[nhds s] (fun _x : Real => 0) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact iwaniecGTwo_eq_zero_of_four_le hx.le
  exact hzero.congr_of_eventuallyEq heq

theorem iwaniecGTwo_hasDerivAt_four :
    HasDerivAt iwaniecGTwo 0 4 := by
  let formula := fun x : Real => 3 * Real.log (3 / (x - 1)) + x - 4
  have hden : (4 : Real) - 1 ≠ 0 := by norm_num
  have hsub : HasDerivAt (fun x : Real => x - 1) 1 4 :=
    (hasDerivAt_id 4).sub_const 1
  have hinner : HasDerivAt (fun x : Real => 3 / (x - 1))
      (-3 / ((4 : Real) - 1) ^ 2) 4 := by
    convert (hasDerivAt_const 4 (3 : Real)).div hsub hden using 1 <;>
      field_simp <;> ring
  have hinnerNe : (3 : Real) / ((4 : Real) - 1) ≠ 0 :=
    div_ne_zero (by norm_num) hden
  have hraw := ((hinner.log hinnerNe).const_mul 3).add
      (hasDerivAt_id 4) |>.sub_const 4
  have hformula : HasDerivAt formula 0 4 := by
    dsimp [formula]
    convert hraw using 1 <;> norm_num
  have hleft : HasDerivWithinAt iwaniecGTwo 0 (Set.Iic (4 : Real)) 4 := by
    have heq : iwaniecGTwo =ᶠ[nhdsWithin (4 : Real) (Set.Iic 4)] formula := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Ioi_mem_nhds (show (2 : Real) < 4 by norm_num)),
        self_mem_nhdsWithin] with x hxLower hxUpper
      exact iwaniecGTwo_eq hxLower.le hxUpper
    apply hformula.hasDerivWithinAt.congr_of_eventuallyEq heq
    norm_num [formula, iwaniecGTwo]
  have hright : HasDerivWithinAt iwaniecGTwo 0 (Set.Ici (4 : Real)) 4 := by
    have hzero : HasDerivWithinAt (fun _x : Real => (0 : Real)) 0
        (Set.Ici (4 : Real)) 4 :=
      (hasDerivAt_const (4 : Real) (0 : Real)).hasDerivWithinAt
    apply hzero.congr_of_mem
    · intro x hx
      exact iwaniecGTwo_eq_zero_of_four_le hx
    · simp
  simpa using hleft.union hright

theorem iwaniecEvenSieveSeries_hasDerivAt_of_lt_four
    {s : Real} (hlower : 2 < s) (hupper : s < 4) :
    HasDerivAt iwaniecEvenSieveSeries
      (-iwaniecOddSeriesKernel s + (1 - 3 / (s - 1))) s := by
  have htail := iwaniecOddSeriesTail_hasDerivAt hlower
  have hg := iwaniecGTwo_hasDerivAt_of_two_lt_of_lt_four hlower hupper
  have hsum := htail.add hg
  have heq : iwaniecEvenSieveSeries =ᶠ[nhds s]
      (fun a : Real =>
        (∫ t in Set.Ioi a, iwaniecOddSeriesKernel t) + iwaniecGTwo a) := by
    filter_upwards [Ioi_mem_nhds hlower] with a ha
    simpa [iwaniecOddSeriesKernel] using
      iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo ha.le
  exact hsum.congr_of_eventuallyEq heq

theorem iwaniecEvenSieveSeries_hasDerivAt_of_four_lt
    {s : Real} (hs : 4 < s) :
    HasDerivAt iwaniecEvenSieveSeries (-iwaniecOddSeriesKernel s) s := by
  have htail := iwaniecOddSeriesTail_hasDerivAt (by linarith : 2 < s)
  have hg := iwaniecGTwo_hasDerivAt_of_four_lt hs
  have hsum := htail.add hg
  have heq : iwaniecEvenSieveSeries =ᶠ[nhds s]
      (fun a : Real =>
        (∫ t in Set.Ioi a, iwaniecOddSeriesKernel t) + iwaniecGTwo a) := by
    filter_upwards [Ioi_mem_nhds (by linarith : 2 < s)] with a ha
    simpa [iwaniecOddSeriesKernel] using
      iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo ha.le
  have hraw : HasDerivAt
      (fun a : Real =>
        (∫ t in Set.Ioi a, iwaniecOddSeriesKernel t) + iwaniecGTwo a)
      (-iwaniecOddSeriesKernel s) s := by
    convert hsum using 1 <;> ring
  exact hraw.congr_of_eventuallyEq heq

theorem iwaniecEvenSieveSeries_hasDerivAt_four :
    HasDerivAt iwaniecEvenSieveSeries (-iwaniecOddSeriesKernel 4) 4 := by
  have htail := iwaniecOddSeriesTail_hasDerivAt (by norm_num : (2 : Real) < 4)
  have hg := iwaniecGTwo_hasDerivAt_four
  have hsum := htail.add hg
  have heq : iwaniecEvenSieveSeries =ᶠ[nhds (4 : Real)]
      (fun a : Real =>
        (∫ t in Set.Ioi a, iwaniecOddSeriesKernel t) + iwaniecGTwo a) := by
    filter_upwards [Ioi_mem_nhds (show (2 : Real) < 4 by norm_num)] with a ha
    simpa [iwaniecOddSeriesKernel] using
      iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo ha.le
  have hraw : HasDerivAt
      (fun a : Real =>
        (∫ t in Set.Ioi a, iwaniecOddSeriesKernel t) + iwaniecGTwo a)
      (-iwaniecOddSeriesKernel 4) 4 := by
    convert hsum using 1 <;> ring
  exact hraw.congr_of_eventuallyEq heq

theorem iwaniecOddSieveSeries_deriv_eq
    {s : Real} (hs : 3 < s) :
    deriv iwaniecOddSieveSeries s =
      -iwaniecEvenSieveSeries (s - 1) / (s - 1) := by
  rw [(iwaniecOddSieveSeries_hasDerivAt hs).deriv]
  unfold iwaniecEvenSeriesKernel
  ring

theorem iwaniecEvenSieveSeries_deriv_eq_of_lt_four
    {s : Real} (hlower : 2 < s) (hupper : s < 4) :
    deriv iwaniecEvenSieveSeries s =
      -iwaniecOddSieveSeries (s - 1) / (s - 1) +
        1 - 3 / (s - 1) := by
  rw [(iwaniecEvenSieveSeries_hasDerivAt_of_lt_four hlower hupper).deriv]
  unfold iwaniecOddSeriesKernel
  ring

theorem iwaniecEvenSieveSeries_deriv_eq_of_four_lt
    {s : Real} (hs : 4 < s) :
    deriv iwaniecEvenSieveSeries s =
      -iwaniecOddSieveSeries (s - 1) / (s - 1) := by
  rw [(iwaniecEvenSieveSeries_hasDerivAt_of_four_lt hs).deriv]
  unfold iwaniecOddSeriesKernel
  ring

end

end Erdos1212Kernel
