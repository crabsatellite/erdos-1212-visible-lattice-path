import Erdos1212Kernel.IwaniecAuxiliaryTail

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxLowerTailKernel_initial {t : Real} (ht : t ≤ 4) :
    iwaniecAuxLowerTailKernel t = iwaniecAuxDelayKernel t := by
  unfold iwaniecAuxLowerTailKernel iwaniecAuxDelayKernel
  rw [iwaniecAuxUpper_initial (by linarith), one_mul]

def iwaniecAuxInitialTailPrimitive (s : Real) : Real :=
  -(1 + 1 / (s - 1) - Real.log (s - 1))

theorem iwaniecAuxInitialTailPrimitive_hasDerivAt {s : Real} (hs : 1 < s) :
    HasDerivAt iwaniecAuxInitialTailPrimitive (iwaniecAuxDelayKernel s) s := by
  have hsNe : s - 1 ≠ 0 := by linarith
  have hd := (hasDerivAt_id s).sub_const 1
  have hinv := (hasDerivAt_const s (1 : Real)).div hd hsNe
  have hraw := (((hasDerivAt_const s (1 : Real)).add hinv).sub (hd.log hsNe)).neg
  refine hraw.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, id_eq]
  unfold iwaniecAuxDelayKernel
  field_simp [hsNe] <;> ring

theorem iwaniecAuxLowerTail_initial_integrable
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    IntervalIntegrable iwaniecAuxLowerTailKernel volume s 3 := by
  have hc : ContinuousOn iwaniecAuxDelayKernel (Set.uIcc s 3) := by
    intro t ht
    rw [Set.uIcc_of_le hs.2] at ht
    exact (iwaniecAuxDelayKernel_continuousAt (by linarith [hs.1, ht.1])).continuousWithinAt
  apply (hc.congr _).intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hs.2] at ht
  exact iwaniecAuxLowerTailKernel_initial (by linarith [ht.2])

theorem iwaniecAuxLowerTail_initial_integral
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    (∫ t in s..3, iwaniecAuxLowerTailKernel t) =
      iwaniecAuxLower s - iwaniecAuxLower 3 := by
  have hd : ∀ t ∈ Set.uIcc s (3 : Real),
      HasDerivAt iwaniecAuxInitialTailPrimitive (iwaniecAuxLowerTailKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hs.2] at ht
    rw [iwaniecAuxLowerTailKernel_initial (by linarith [ht.2])]
    exact iwaniecAuxInitialTailPrimitive_hasDerivAt (by linarith [hs.1, ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (iwaniecAuxLowerTail_initial_integrable hs)]
  rw [iwaniecAuxLower_initial hs.2, iwaniecAuxLower_initial (by norm_num : (3 : Real) ≤ 3)]
  unfold iwaniecAuxInitialTailPrimitive
  ring

theorem iwaniecAuxLowerTail_integrable {s : Real} (hs : 2 ≤ s) :
    IntegrableOn iwaniecAuxLowerTailKernel (Set.Ioi s) := by
  by_cases hsHigh : 3 ≤ s
  · exact iwaniecAuxLowerTail_integrable_high hsHigh
  · have hsLow : s ≤ 3 := (lt_of_not_ge hsHigh).le
    have hfinite := (intervalIntegrable_iff_integrableOn_Ioc_of_le hsLow).mp
      (iwaniecAuxLowerTail_initial_integrable ⟨hs, hsLow⟩)
    have hUnion := hfinite.union (iwaniecAuxLowerTail_integrable_high (s := 3) (by norm_num))
    simpa only [Set.Ioc_union_Ioi_eq_Ioi hsLow] using hUnion

/-- The complete source (3.14), including its nontrivial `[2,3]` branch. -/
theorem iwaniecAuxLower_tail {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxLower s = ∫ t in Set.Ioi s, iwaniecAuxLowerTailKernel t := by
  by_cases hsHigh : 3 ≤ s
  · exact iwaniecAuxLower_tail_high hsHigh
  · have hsLow : s ≤ 3 := (lt_of_not_ge hsHigh).le
    have hsum := intervalIntegral.integral_interval_add_Ioi'
      (iwaniecAuxLowerTail_initial_integrable ⟨hs, hsLow⟩)
      (iwaniecAuxLowerTail_integrable_high (s := 3) (by norm_num))
    rw [iwaniecAuxLowerTail_initial_integral ⟨hs, hsLow⟩,
      ← iwaniecAuxLower_tail_high (s := 3) (by norm_num)] at hsum
    simpa only [sub_add_cancel] using hsum

end

end Erdos1212Kernel
