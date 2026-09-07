import Erdos1212Kernel.IwaniecAuxiliaryCorollary

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecAuxGKernel (rank : Nat) (s : Real) : Real :=
  iwaniecAuxG rank (s - 1) * s / (s - 1) ^ 2

theorem iwaniecAuxGKernel_pos (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    0 < iwaniecAuxGKernel rank s :=
  div_pos (mul_pos (iwaniecAuxG_pos rank (by linarith)) (by linarith))
    (sq_pos_of_pos (by linarith))

theorem iwaniecAuxG_succ_hasDerivAt (rank : Nat) {s : Real} (hs : 3 < s) :
    HasDerivAt (iwaniecAuxG (rank + 1)) (-iwaniecAuxGKernel rank s) s := by
  by_cases hr : Even rank
  · have hf : iwaniecAuxG (rank + 1) = iwaniecAuxUpper := by
      funext t
      simp only [iwaniecAuxG, Nat.even_add_one, hr, not_true_eq_false, if_false]
    have hd : -iwaniecAuxGKernel rank s = -s / (s - 1) ^ 2 * iwaniecAuxLower (s - 1) := by
      unfold iwaniecAuxGKernel
      rw [iwaniecAuxG, if_pos hr]
      ring
    rw [hf, hd]
    exact iwaniecAuxUpper_hasDerivAt hs
  · have hf : iwaniecAuxG (rank + 1) = iwaniecAuxLower := by
      funext t
      simp only [iwaniecAuxG, Nat.even_add_one, hr, not_false_eq_true, if_true]
    have hd : -iwaniecAuxGKernel rank s = -s / (s - 1) ^ 2 * iwaniecAuxUpper (s - 1) := by
      unfold iwaniecAuxGKernel
      rw [iwaniecAuxG, if_neg hr]
      ring
    rw [hf, hd]
    exact iwaniecAuxLower_hasDerivAt hs

theorem iwaniecAuxGKernel_continuousOn (rank : Nat) :
    ContinuousOn (iwaniecAuxGKernel rank) (Set.Ioi (3 : Real)) := by
  have hshift : ContinuousOn (fun s : Real => iwaniecAuxG rank (s - 1)) (Set.Ioi (3 : Real)) := by
    apply (iwaniecAuxG_continuousOn rank).comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change (1 : Real) < s - 1
    linarith [hs.out]
  apply (hshift.mul continuousOn_id).div ((continuousOn_id.sub continuousOn_const).pow 2)
  intro s hs
  exact pow_ne_zero 2 (by linarith [hs.out] : s - 1 ≠ 0)

/-- The source corollary transported to its exact derivative kernel. -/
theorem iwaniecAuxG_log_lt_kernel (rank : Nat) {s : Real} (hs : 3 < s) :
    iwaniecAuxG (rank + 1) s * Real.log s < iwaniecAuxCorollaryConstant * iwaniecAuxGKernel rank s := by
  have hstart : (5 + (-1 : Real) ^ rank) / 2 < s := by
    rw [neg_one_pow_eq_ite]
    split_ifs <;> linarith
  have h := iwaniecAuxLemmaTenCorollary rank hstart
  rw [div_lt_iff₀ (mul_pos (iwaniecAuxG_pos rank (by linarith : 2 ≤ s - 1)) (by linarith))] at h
  unfold iwaniecAuxGKernel
  rw [← mul_div_assoc, lt_div_iff₀ (sq_pos_of_pos (show 0 < s - 1 by linarith))]
  nlinarith

end

end Erdos1212Kernel
