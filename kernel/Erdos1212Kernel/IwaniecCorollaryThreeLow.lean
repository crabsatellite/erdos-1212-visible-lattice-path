import Erdos1212Kernel.IwaniecAuxPrimeSquaredIntegral
import Erdos1212Kernel.IwaniecLemma13Real

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 650000

theorem exists_iwaniecCorollaryThree_low_constant :
    ∃ C : Real, 0 < C ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecAuxSZero →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecPrimeReciprocalWeightedRealInterval (iwaniecAuxPrimeSquaredWeight rank level)
        (iwaniecExpReciprocalScale (Real.log level) iwaniecAuxSZero)
        (iwaniecExpReciprocalScale (Real.log level) s) ≤
      (iwaniecAuxG (rank + 1) s - iwaniecAuxG (rank + 1) iwaniecAuxSZero) / Real.log level ^ 2 +
        32 * C * iwaniecPaperXi level ^ 2 * (iwaniecAuxG (rank + 1) s / Real.log level ^ 2) *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)) := by
  obtain ⟨C, hC, hsource⟩ := exists_iwaniecLemma13_real_constant
  refine ⟨C, hC, ?_⟩
  intro rank level s hy hs hs0 hξ
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let B := iwaniecExpReciprocalScale L iwaniecAuxSZero
  let A := iwaniecExpReciprocalScale L s
  let b := iwaniecAuxPrimeSquaredWeight rank level
  let J := ∫ x in B..A, b x / (x * Real.log x)
  let E₀ := Real.exp (-Real.sqrt (L / iwaniecAuxSZero))
  let E := Real.exp (-Real.sqrt (L / ξ))
  have hL : 0 < L := Real.log_pos hy
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hs0pos : 0 < iwaniecAuxSZero := by linarith [iwaniecAuxSZero_large]
  have hspos : 0 < s := by linarith
  have hξpos : 0 < ξ := hs0pos.trans_le hξ
  have hB : 2 ≤ B := (iwaniecCorollaryThree_left_cutoff_two hy hξ).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hs0pos hξ))
  have hBA : B ≤ A := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hspos hs0)
  have hmono := iwaniecAuxPrimeSquaredWeight_monotoneOn rank hy hs hs0
  have hnonneg : ∀ x ∈ Set.Icc B A, 0 ≤ b x :=
    fun x hx => (iwaniecAuxPrimeSquaredWeight_pos_on rank hy hs hs0 hx).le
  have herr := hsource b B A hB hBA hmono hnonneg
  have herr' : |iwaniecPrimeReciprocalWeightedRealInterval b B A - J| ≤ C * b A * E₀ := by
    simpa only [J, b, B, A, E₀, iwaniecExpReciprocalScale, Real.log_exp] using herr
  have hmain : J = (iwaniecAuxG (rank + 1) s - iwaniecAuxG (rank + 1) iwaniecAuxSZero) / L ^ 2 :=
    iwaniecAuxPrimeSquared_integral_finite rank hy hs hs0
  have hG : 0 < iwaniecAuxG (rank + 1) s := iwaniecAuxG_pos (rank + 1) hs2
  have hsquare : s ^ 2 ≤ ξ ^ 2 := by nlinarith only [hspos, hs0, hξ]
  have hbA : b A ≤ 32 * ξ ^ 2 * iwaniecAuxG (rank + 1) s / L ^ 2 := by
    have hh := iwaniecAuxPrimeSquaredWeight_endpoint_bound rank hy hs
    exact hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hG.le) (sq_nonneg L))
  have hE : E₀ ≤ E := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hL.le hs0pos hξ))
  have hbudget : C * b A * E₀ ≤ 32 * C * ξ ^ 2 * (iwaniecAuxG (rank + 1) s / L ^ 2) * E := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hbA hC.le) hE
      (show 0 ≤ E₀ from (Real.exp_pos _).le)
      (show 0 ≤ C * (32 * ξ ^ 2 * iwaniecAuxG (rank + 1) s / L ^ 2) by positivity)
    convert hh using 1 <;> ring
  have habs := (le_abs_self (iwaniecPrimeReciprocalWeightedRealInterval b B A - J)).trans herr'
  have hsum : iwaniecPrimeReciprocalWeightedRealInterval b B A ≤ J + C * b A * E₀ := by
    linarith only [habs]
  exact hsum.trans (by rw [hmain]; exact add_le_add le_rfl hbudget)

end

end Erdos1212Kernel
