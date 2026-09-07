import Erdos1212Kernel.IwaniecLowerPowerDerivative

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

def iwaniecCorollaryThreeProfile (rank : Nat) (level s : Real) : Real :=
  iwaniecAuxWeightLowerPower level s * iwaniecAuxG rank (s - 1)

theorem iwaniecAuxG_add_two (rank : Nat) (s : Real) :
    iwaniecAuxG (rank + 2) s = iwaniecAuxG rank s := by
  simp [iwaniecAuxG, Nat.even_add]

theorem iwaniecAuxG_hasDerivAt_same_rank (rank : Nat) {s : Real} (hs : 3 < s) :
    HasDerivAt (iwaniecAuxG rank) (-iwaniecAuxGKernel (rank + 1) s) s := by
  have hh := iwaniecAuxG_succ_hasDerivAt (rank + 1) hs
  have heq : iwaniecAuxG ((rank + 1) + 1) = iwaniecAuxG rank := by
    funext t
    simpa only [Nat.add_assoc] using iwaniecAuxG_add_two rank t
  rwa [heq] at hh

theorem iwaniecCorollaryThreeProfile_pos (rank : Nat) (level : Real) {s : Real} (hs : 3 ≤ s) :
    0 < iwaniecCorollaryThreeProfile rank level s :=
  mul_pos (iwaniecAuxWeightLowerPower_pos level (by linarith))
    (iwaniecAuxG_pos rank (by linarith))

theorem iwaniecCorollaryThreeProfile_hasDerivAt (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : 4 < s) :
    HasDerivAt (iwaniecCorollaryThreeProfile rank level)
      (iwaniecAuxWeightLowerPower level s *
        (iwaniecAuxLowerPowerLogDerivative level s * iwaniecAuxG rank (s - 1) -
          iwaniecAuxGKernel (rank + 1) (s - 1))) s := by
  have hshift := (iwaniecAuxG_hasDerivAt_same_rank rank (show 3 < s - 1 by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hh := (iwaniecAuxWeightLowerPower_hasDerivAt hy (show 1 ≤ s by linarith)).mul hshift
  unfold iwaniecCorollaryThreeProfile
  convert hh using 1
  <;> first | (funext t; rfl) | (simp only [Function.comp_def, id_eq, Pi.mul_apply, mul_one]; ring)

theorem iwaniecCorollaryThreeProfile_deriv_neg (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s)
    (hxi : s ≤ iwaniecPaperXi level) :
    deriv (iwaniecCorollaryThreeProfile rank level) s < 0 := by
  have hs4 : 4 < s := by linarith [iwaniecAuxSZero_large]
  have hC : 0 < iwaniecAuxCorollaryConstant := by linarith [iwaniecAuxCorollaryConstant_gt_three_hundred]
  have hG : 0 < iwaniecAuxG rank (s - 1) := iwaniecAuxG_pos rank (by linarith)
  have hD := mul_lt_mul_of_pos_right (iwaniecAuxLowerPower_shifted_loss_lt hy hs hxi) hG
  have hHazard := iwaniecAuxG_log_lt_kernel (rank + 1) (s := s - 1) (by linarith)
  rw [show (rank + 1) + 1 = rank + 2 by omega, iwaniecAuxG_add_two] at hHazard
  have hprod : iwaniecAuxCorollaryConstant *
      (iwaniecAuxLowerPowerLogDerivative level s * iwaniecAuxG rank (s - 1)) <
      iwaniecAuxCorollaryConstant * iwaniecAuxGKernel (rank + 1) (s - 1) := by
    have hh := hD.trans (by simpa only [mul_comm] using hHazard)
    simpa only [mul_assoc] using hh
  have hnegative : iwaniecAuxLowerPowerLogDerivative level s * iwaniecAuxG rank (s - 1) <
      iwaniecAuxGKernel (rank + 1) (s - 1) := by
    nlinarith only [hprod, hC]
  rw [(iwaniecCorollaryThreeProfile_hasDerivAt rank hy hs4).deriv]
  exact mul_neg_of_pos_of_neg (iwaniecAuxWeightLowerPower_pos level (by linarith))
    (sub_neg.mpr hnegative)

theorem iwaniecCorollaryThreeProfile_antitoneOn (rank : Nat) {level : Real} (hy : 1 < level) :
    AntitoneOn (iwaniecCorollaryThreeProfile rank level)
      (Set.Icc iwaniecAuxSZero (iwaniecPaperXi level)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro s hs
    exact (iwaniecCorollaryThreeProfile_hasDerivAt rank hy
      (by linarith [hs.1, iwaniecAuxSZero_large])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' := interior_subset hs
    exact (iwaniecCorollaryThreeProfile_hasDerivAt rank hy
      (by linarith [hs'.1, iwaniecAuxSZero_large])).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (iwaniecCorollaryThreeProfile_deriv_neg rank hy hs.1 hs.2.le).le

end

end Erdos1212Kernel
