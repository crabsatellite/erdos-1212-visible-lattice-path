import Erdos1212Kernel.IwaniecCorollaryThreeProfile
import Erdos1212Kernel.IwaniecLogReciprocalChange

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- The literal weight displayed in the proof of Corollary 3. -/
def iwaniecCorollaryThreePrimeWeight (rank : Nat) (level x : Real) : Real :=
  (1 + Real.log (Real.log level / Real.log x) ^ 5 / Real.log x ^ 2) ^
      (5 * (Real.log level / Real.log x - 1)) *
    iwaniecAuxG rank (Real.log level / Real.log x - 1) / Real.log (level / x) ^ 2

def iwaniecCorollaryThreeScaledProfile (rank : Nat) (level s : Real) : Real :=
  iwaniecCorollaryThreeProfile rank level s * (s / (s - 1)) ^ 2

theorem iwaniecCorollaryThreePrimeWeight_literal_normalization (rank : Nat)
    {level x : Real} (hy : 1 < level) (hx : 1 < x) :
    iwaniecCorollaryThreePrimeWeight rank level x =
      iwaniecCorollaryThreeProfile rank level (Real.log level / Real.log x) /
        (Real.log level - Real.log x) ^ 2 := by
  have hL : Real.log level ≠ 0 := (Real.log_pos hy).ne'
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hbase : 1 + Real.log (Real.log level / Real.log x) ^ 5 / Real.log x ^ 2 =
      iwaniecAuxWeightBase level (Real.log level / Real.log x) := by
    unfold iwaniecAuxWeightBase
    field_simp [hL, hl]
    <;> ring
  unfold iwaniecCorollaryThreePrimeWeight iwaniecCorollaryThreeProfile iwaniecAuxWeightLowerPower
  rw [hbase, Real.log_div (by linarith : level ≠ 0) (by linarith : x ≠ 0)]

theorem iwaniecCorollaryThreePrimeWeight_scaled_normalization (rank : Nat)
    {level x : Real} (hy : 1 < level) (hx : 1 < x) (hxy : x < level) :
    iwaniecCorollaryThreePrimeWeight rank level x =
      iwaniecCorollaryThreeScaledProfile rank level (Real.log level / Real.log x) /
        Real.log level ^ 2 := by
  rw [iwaniecCorollaryThreePrimeWeight_literal_normalization rank hy hx]
  unfold iwaniecCorollaryThreeScaledProfile
  have hL : Real.log level ≠ 0 := (Real.log_pos hy).ne'
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hdiff : Real.log level - Real.log x ≠ 0 :=
    (sub_pos.mpr (Real.log_lt_log (by linarith) hxy)).ne'
  field_simp [hL, hl, hdiff]
  <;> ring

theorem iwaniecCorollaryThreePrimeWeight_at_scale (rank : Nat)
    {level t : Real} (hy : 1 < level) (ht : 1 < t) :
    iwaniecCorollaryThreePrimeWeight rank level (iwaniecExpReciprocalScale (Real.log level) t) =
      iwaniecCorollaryThreeScaledProfile rank level t / Real.log level ^ 2 := by
  have hL := Real.log_pos hy
  have hx : 1 < iwaniecExpReciprocalScale (Real.log level) t :=
    Real.one_lt_exp_iff.mpr (div_pos hL (by linarith))
  have hxy : iwaniecExpReciprocalScale (Real.log level) t < level := by
    calc
      _ < Real.exp (Real.log level) := Real.exp_lt_exp.mpr (div_lt_self hL ht)
      _ = _ := Real.exp_log (by linarith)
  rw [iwaniecCorollaryThreePrimeWeight_scaled_normalization rank hy hx hxy]
  have heq : Real.log level / Real.log (iwaniecExpReciprocalScale (Real.log level) t) = t := by
    unfold iwaniecExpReciprocalScale
    rw [Real.log_exp]
    field_simp [hL.ne', (show t ≠ 0 by linarith)]
  rw [heq]

theorem iwaniec_squared_reciprocal_ratio_antitone :
    AntitoneOn (fun t : Real => (t / (t - 1)) ^ 2) (Set.Ici (2 : Real)) := by
  intro x hx y hy hxy
  have hx1 : 0 < x - 1 := by linarith [hx.out]
  have hy1 : 0 < y - 1 := by linarith [hy.out]
  have hratio : y / (y - 1) ≤ x / (x - 1) := by
    apply (div_le_div_iff₀ hy1 hx1).mpr
    nlinarith only [hxy]
  exact pow_le_pow_left₀ (div_nonneg (by linarith [hy.out]) hy1.le) hratio 2

theorem iwaniecCorollaryThreeScaledProfile_antitoneOn (rank : Nat)
    {level : Real} (hy : 1 < level) :
    AntitoneOn (iwaniecCorollaryThreeScaledProfile rank level)
      (Set.Icc iwaniecAuxSZero (iwaniecPaperXi level)) := by
  intro x hx y hyy hxy
  have hx3 : 3 ≤ x := by linarith [hx.1, iwaniecAuxSZero_large]
  have hy3 : 3 ≤ y := hx3.trans hxy
  have hprofile := iwaniecCorollaryThreeProfile_antitoneOn rank hy hx hyy hxy
  have hratio := iwaniec_squared_reciprocal_ratio_antitone
    (show (2 : Real) ≤ x by linarith only [hx3]) (show (2 : Real) ≤ y by linarith only [hy3]) hxy
  exact mul_le_mul hprofile hratio (sq_nonneg _) (iwaniecCorollaryThreeProfile_pos rank level hx3).le

end

end Erdos1212Kernel
