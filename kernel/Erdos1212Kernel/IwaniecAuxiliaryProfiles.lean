import Erdos1212Kernel.IwaniecAuxiliaryRatio

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The auxiliary lower function on printed page 12, distinct from the
normalized lower function in Lemma 5. -/
def iwaniecAuxLower (s : Real) : Real := (iwaniecAuxM s + iwaniecAuxW s) / 2

/-- The auxiliary upper function. Its literal initial data also gives
the paper's extension by 1 on `[1,2]`. -/
def iwaniecAuxUpper (s : Real) : Real := (iwaniecAuxM s - iwaniecAuxW s) / 2

def iwaniecAuxG (rank : Nat) (s : Real) : Real :=
  if Even rank then iwaniecAuxLower s else iwaniecAuxUpper s

theorem iwaniecAuxLower_initial {s : Real} (hs : s ≤ 3) :
    iwaniecAuxLower s = 1 + 1 / (s - 1) - Real.log (s - 1) := by
  unfold iwaniecAuxLower
  rw [iwaniecAuxM_initial hs, iwaniecAuxW_initial hs]
  ring

theorem iwaniecAuxUpper_initial {s : Real} (hs : s ≤ 3) :
    iwaniecAuxUpper s = 1 := by
  unfold iwaniecAuxUpper
  rw [iwaniecAuxM_initial hs, iwaniecAuxW_initial hs]
  ring

theorem iwaniecAuxLower_bounds {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxM s / 3 ≤ iwaniecAuxLower s ∧
      iwaniecAuxLower s ≤ 2 * iwaniecAuxM s / 3 := by
  have h := abs_le.mp (iwaniecAuxW_abs_le_third_M hs)
  unfold iwaniecAuxLower
  constructor <;> linarith [h.1, h.2]

theorem iwaniecAuxUpper_bounds {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxM s / 3 ≤ iwaniecAuxUpper s ∧
      iwaniecAuxUpper s ≤ 2 * iwaniecAuxM s / 3 := by
  have h := abs_le.mp (iwaniecAuxW_abs_le_third_M hs)
  unfold iwaniecAuxUpper
  constructor <;> linarith [h.1, h.2]

theorem iwaniecAuxG_bounds (rank : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecAuxM s / 3 ≤ iwaniecAuxG rank s ∧
      iwaniecAuxG rank s ≤ 2 * iwaniecAuxM s / 3 := by
  unfold iwaniecAuxG
  split
  · exact iwaniecAuxLower_bounds hs
  · exact iwaniecAuxUpper_bounds hs

theorem iwaniecAuxLower_pos {s : Real} (hs : 2 ≤ s) : 0 < iwaniecAuxLower s :=
  (div_pos (iwaniecAuxM_pos hs) (by norm_num : (0 : Real) < 3)).trans_le
    (iwaniecAuxLower_bounds hs).1

theorem iwaniecAuxUpper_pos {s : Real} (hs : 1 ≤ s) : 0 < iwaniecAuxUpper s := by
  by_cases hsTwo : 2 ≤ s
  · exact (div_pos (iwaniecAuxM_pos hsTwo) (by norm_num : (0 : Real) < 3)).trans_le
      (iwaniecAuxUpper_bounds hsTwo).1
  · rw [iwaniecAuxUpper_initial (by linarith)]
    norm_num

theorem iwaniecAuxG_pos (rank : Nat) {s : Real} (hs : 2 ≤ s) : 0 < iwaniecAuxG rank s :=
  (div_pos (iwaniecAuxM_pos hs) (by norm_num : (0 : Real) < 3)).trans_le
    (iwaniecAuxG_bounds rank hs).1

theorem iwaniecAuxLower_continuousOn :
    ContinuousOn iwaniecAuxLower (Set.Ioi (1 : Real)) :=
  ((iwaniecAuxFunction_continuousOn (-1)).add
    (iwaniecAuxFunction_continuousOn 1)).div_const 2

theorem iwaniecAuxUpper_continuousOn :
    ContinuousOn iwaniecAuxUpper (Set.Ioi (1 : Real)) :=
  ((iwaniecAuxFunction_continuousOn (-1)).sub
    (iwaniecAuxFunction_continuousOn 1)).div_const 2

theorem iwaniecAuxG_continuousOn (rank : Nat) :
    ContinuousOn (iwaniecAuxG rank) (Set.Ioi (1 : Real)) := by
  unfold iwaniecAuxG
  split
  · exact iwaniecAuxLower_continuousOn
  · exact iwaniecAuxUpper_continuousOn

theorem iwaniecAuxLower_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxLower
      (-s / (s - 1) ^ 2 * iwaniecAuxUpper (s - 1)) s := by
  have h := ((iwaniecAuxM_hasDerivAt hs).add (iwaniecAuxW_hasDerivAt hs)).div_const 2
  convert h using 1 <;> simp only [iwaniecAuxLower, iwaniecAuxUpper] <;> ring

theorem iwaniecAuxUpper_hasDerivAt {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecAuxUpper
      (-s / (s - 1) ^ 2 * iwaniecAuxLower (s - 1)) s := by
  have h := ((iwaniecAuxM_hasDerivAt hs).sub (iwaniecAuxW_hasDerivAt hs)).div_const 2
  convert h using 1 <;> simp only [iwaniecAuxLower, iwaniecAuxUpper] <;> ring

theorem iwaniecAuxLower_deriv_neg {s : Real} (hs : 3 < s) :
    deriv iwaniecAuxLower s < 0 := by
  rw [(iwaniecAuxLower_hasDerivAt hs).deriv]
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos (by linarith)))
    (iwaniecAuxUpper_pos (by linarith))

theorem iwaniecAuxUpper_deriv_neg {s : Real} (hs : 3 < s) :
    deriv iwaniecAuxUpper s < 0 := by
  rw [(iwaniecAuxUpper_hasDerivAt hs).deriv]
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos (by linarith)))
    (iwaniecAuxLower_pos (by linarith))

end

end Erdos1212Kernel
