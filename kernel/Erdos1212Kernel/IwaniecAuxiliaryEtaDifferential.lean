import Erdos1212Kernel.IwaniecAuxiliaryWeightRatio

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem iwaniecAuxM_hasDerivAt_initial {s : Real} (hs : 1 < s) (hsThree : s < 3) :
    HasDerivAt iwaniecAuxM (-iwaniecAuxDelayKernel s) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hd := (hasDerivAt_id s).sub_const 1
  have hraw := ((hasDerivAt_const s (2 : Real)).add
    ((hasDerivAt_const s (1 : Real)).div hd hne)).sub (hd.log hne)
  have hformula : HasDerivAt (fun t : Real => 2 + 1 / (t - 1) - Real.log (t - 1))
      (-iwaniecAuxDelayKernel s) s := by
    refine hraw.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.add_apply, id_eq]
    unfold iwaniecAuxDelayKernel
    field_simp [hne] <;> ring
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hsThree] with t ht
  exact iwaniecAuxM_initial ht.le

theorem iwaniecAux_initial_hazard_scalar {u : Real} (hu : u ∈ Set.Icc (1 : Real) 2) :
    (u + 1) / u ^ 2 ≤ (2 / 3 : Real) * (2 + 1 / u - Real.log u) := by
  have huPos : 0 < u := by linarith [hu.1]
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos huPos) (sq_nonneg u)
  have hquad : 0 ≤ -2 * u ^ 2 + 4 * u + 3 := by
    have hprod := mul_nonneg huPos.le (show 0 ≤ 2 - u by linarith [hu.2])
    nlinarith
  have hfactor := mul_nonneg (show 0 ≤ u - 1 by linarith [hu.1]) hquad
  rw [div_le_iff₀ (sq_pos_of_pos huPos)]
  have heq : (2 / 3 : Real) * (2 + 1 / u - Real.log u) * u ^ 2 =
      (2 / 3 : Real) * (2 * u ^ 2 + u - u ^ 2 * Real.log u) := by
    field_simp [huPos.ne'] <;> ring
  rw [heq]
  nlinarith

theorem iwaniecAux_initial_hazard_le {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    iwaniecAuxDelayKernel s / iwaniecAuxM s ≤ 2 / 3 := by
  rw [div_le_iff₀ (iwaniecAuxM_pos hs.1), iwaniecAuxM_initial hs.2]
  have h := iwaniecAux_initial_hazard_scalar (u := s - 1) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa only [iwaniecAuxDelayKernel, sub_add_cancel] using h

theorem iwaniecAuxEta_hasDerivAt_initial {s : Real} (hs : 3 < s) (hsFour : s < 4) :
    HasDerivAt iwaniecAuxEta
      (iwaniecAuxEta s * (iwaniecAuxHazard s -
        iwaniecAuxDelayKernel (s - 1) / iwaniecAuxM (s - 1))) s := by
  have hlag := (iwaniecAuxM_hasDerivAt_initial (s := s - 1) (by linarith) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hraw := hlag.div (iwaniecAuxM_hasDerivAt hs) (iwaniecAuxM_pos (by linarith : 2 ≤ s)).ne'
  refine hraw.congr_deriv ?_
  simp only [mul_one, id_eq, Function.comp_apply]
  simp only [iwaniecAuxHazard, iwaniecAuxEta, iwaniecAuxDelayKernel]
  field_simp [(iwaniecAuxM_pos (s := s) (by linarith)).ne',
    (iwaniecAuxM_pos (s := s - 1) (by linarith)).ne']
  <;> ring

theorem iwaniecAuxEta_deriv_pos_initial {s : Real} (hs : 3 < s) (hsFour : s < 4) :
    0 < deriv iwaniecAuxEta s := by
  rw [(iwaniecAuxEta_hasDerivAt_initial hs hsFour).deriv]
  apply mul_pos (iwaniecAuxEta_pos hs.le)
  have hH := iwaniecAuxHazard_lower hs.le
  have hi := iwaniecAux_initial_hazard_le (s := s - 1) ⟨by linarith, by linarith⟩
  linarith

theorem iwaniecAuxEta_strictMonoOn_initial :
    StrictMonoOn iwaniecAuxEta (Set.Icc (3 : Real) 4) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (3 : Real) 4)
    (iwaniecAuxEta_continuousOn.mono (fun _ hx => hx.1))
  intro s hs
  rw [interior_Icc] at hs
  exact iwaniecAuxEta_deriv_pos_initial hs.1 hs.2

theorem iwaniecAuxEta_hasDerivAt_high {s : Real} (hs : 4 < s) :
    HasDerivAt iwaniecAuxEta
      (iwaniecAuxEta s * (iwaniecAuxHazard s - iwaniecAuxHazard (s - 1))) s := by
  have hlag := (iwaniecAuxM_hasDerivAt (s := s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hraw := hlag.div (iwaniecAuxM_hasDerivAt (by linarith))
    (iwaniecAuxM_pos (by linarith : 2 ≤ s)).ne'
  refine hraw.congr_deriv ?_
  simp only [mul_one, id_eq, Function.comp_apply]
  simp only [iwaniecAuxHazard, iwaniecAuxEta, iwaniecAuxDelayKernel]
  field_simp [(iwaniecAuxM_pos (s := s) (by linarith)).ne',
    (iwaniecAuxM_pos (s := s - 1) (by linarith)).ne']
  <;> ring

end

end Erdos1212Kernel
