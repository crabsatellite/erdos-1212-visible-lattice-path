import Erdos1212Kernel.IwaniecAuxiliaryLogRatio

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxMWindowWeight_hasDerivAt {s : Real} (hs : s ≠ 0) :
    HasDerivAt iwaniecAuxMWindowWeight (1 / s ^ 3) s := by
  have hraw := (hasDerivAt_const s (1 : Real)).sub
    ((hasDerivAt_const s (1 : Real)).div (((hasDerivAt_id s).pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)))
  refine hraw.congr_deriv ?_
  simp only [Pi.pow_apply, id_eq]
  field_simp [hs] <;> ring

def iwaniecAuxWeightRatio (s : Real) : Real :=
  iwaniecAuxMWindowWeight (s - 1) / iwaniecAuxMWindowWeight s

theorem iwaniecAuxWeightRatio_hasDerivAt {s : Real} (hs : 3 ≤ s) :
    HasDerivAt iwaniecAuxWeightRatio
      ((1 / (s - 1) ^ 3 * iwaniecAuxMWindowWeight s -
        iwaniecAuxMWindowWeight (s - 1) * (1 / s ^ 3)) / iwaniecAuxMWindowWeight s ^ 2) s := by
  have hlag := (iwaniecAuxMWindowWeight_hasDerivAt (s := s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hraw := hlag.div (iwaniecAuxMWindowWeight_hasDerivAt (s := s) (by linarith))
    (iwaniecAuxMWindowWeight_pos (by linarith : 2 ≤ s)).ne'
  simpa only [mul_one, id_eq] using hraw

theorem iwaniecAuxWeightRatio_deriv_pos {s : Real} (hs : 3 ≤ s) :
    0 < deriv iwaniecAuxWeightRatio s := by
  rw [(iwaniecAuxWeightRatio_hasDerivAt hs).deriv]
  have hsPos : 0 < s := by linarith
  have huPos : 0 < s - 1 := by linarith
  have heq : 1 / (s - 1) ^ 3 * iwaniecAuxMWindowWeight s -
      iwaniecAuxMWindowWeight (s - 1) * (1 / s ^ 3) =
      (3 * s ^ 2 - 3 * s + 1 / 2) / (s ^ 3 * (s - 1) ^ 3) := by
    unfold iwaniecAuxMWindowWeight
    field_simp [hsPos.ne', huPos.ne'] <;> ring
  rw [heq]
  apply div_pos
  · exact div_pos (by nlinarith [sq_nonneg (s - 1)])
      (mul_pos (pow_pos hsPos 3) (pow_pos huPos 3))
  · exact sq_pos_of_pos (iwaniecAuxMWindowWeight_pos (by linarith))

theorem iwaniecAuxWeightRatio_strictMonoOn :
    StrictMonoOn iwaniecAuxWeightRatio (Set.Ici (3 : Real)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (3 : Real))
    (fun s hs => (iwaniecAuxWeightRatio_hasDerivAt hs).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ici] at hs
  exact iwaniecAuxWeightRatio_deriv_pos hs.le

def iwaniecAuxHazard (s : Real) : Real := iwaniecAuxEta s * iwaniecAuxDelayKernel s

theorem iwaniecAuxDelayKernel_pos {s : Real} (hs : 2 ≤ s) :
    0 < iwaniecAuxDelayKernel s :=
  div_pos (by linarith) (sq_pos_of_pos (by linarith))

theorem iwaniecAuxMCoefficient_mul_delay {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxMCoefficient s * iwaniecAuxDelayKernel s = iwaniecAuxMWindowWeight (s - 1) := by
  unfold iwaniecAuxMCoefficient iwaniecAuxDelayKernel iwaniecAuxMWindowWeight
  field_simp [show s ≠ 0 by linarith, show s - 1 ≠ 0 by linarith] <;> ring

theorem iwaniecAuxHazard_lower {s : Real} (hs : 3 ≤ s) : (7 / 8 : Real) ≤ iwaniecAuxHazard s := by
  have hprod := mul_le_mul_of_nonneg_right (iwaniecAuxMCoefficient_le_eta hs)
    (iwaniecAuxDelayKernel_pos (by linarith : 2 ≤ s)).le
  rw [iwaniecAuxMCoefficient_mul_delay hs] at hprod
  have hw : (7 / 8 : Real) ≤ iwaniecAuxMWindowWeight (s - 1) := by
    have ht : 2 ≤ s - 1 := by linarith
    rcases ht.eq_or_lt with heq | hlt
    · rw [← heq]
      norm_num [iwaniecAuxMWindowWeight]
    · have h := (iwaniecAuxMWindowWeight_lt_of_lt (show (2 : Real) ≤ 2 by norm_num) hlt).le
      norm_num [iwaniecAuxMWindowWeight] at h ⊢
      exact h
  exact hw.trans hprod

theorem iwaniecAuxHazard_continuousOn :
    ContinuousOn iwaniecAuxHazard (Set.Ici (3 : Real)) := by
  apply iwaniecAuxEta_continuousOn.mul
  intro s hs
  exact (iwaniecAuxDelayKernel_continuousAt (by linarith [hs.out])).continuousWithinAt

end

end Erdos1212Kernel
