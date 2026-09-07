import Erdos1212Kernel.IwaniecCorollaryThreeMonotonicity
import Erdos1212Kernel.IwaniecCorollaryThreeIntegral
import Erdos1212Kernel.IwaniecCorollaryThreeEndpoint
import Erdos1212Kernel.IwaniecLemma13Real

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 650000

def iwaniecCorollaryThreePrimeSum (rank : Nat) (level s : Real) : Real :=
  iwaniecPrimeReciprocalWeightedRealInterval (iwaniecCorollaryThreePrimeWeight rank level)
    (iwaniecExpReciprocalScale (Real.log level) (iwaniecPaperXi level))
    (iwaniecExpReciprocalScale (Real.log level) s)

/-- The source's first case of Corollary 3, with its literal weight,
finite prime interval, and effective factor, including both endpoints. -/
theorem exists_iwaniecCorollaryThree_high_constant :
    ∃ C : Real, 0 < C ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ s → s ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreePrimeSum rank level s ≤
        (iwaniecAuxTau rank level s / Real.log level ^ 2) *
          (1 + 20 * C * iwaniecPaperXi level ^ 2 *
            Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level))) := by
  obtain ⟨C, hC, hsource⟩ := exists_iwaniecLemma13_real_constant
  refine ⟨C, hC, ?_⟩
  intro rank level s hy hs hxi
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let B := iwaniecExpReciprocalScale L ξ
  let A := iwaniecExpReciprocalScale L s
  let b := iwaniecCorollaryThreePrimeWeight rank level
  let J := ∫ x in B..A, b x / (x * Real.log x)
  let T := iwaniecAuxTau rank level s / L ^ 2
  let E := Real.exp (-Real.sqrt (L / ξ))
  have hL : 0 < L := Real.log_pos hy
  have hs3 : 3 ≤ s := by linarith [iwaniecAuxSZero_large]
  have hs0 : 0 < s := by linarith
  have hξ0 : 0 < ξ := hs0.trans_le hxi
  have hB : 2 ≤ B := iwaniecCorollaryThree_left_cutoff_two hy (hs.trans hxi)
  have hBA : B ≤ A := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hs0 hxi)
  have hmono := iwaniecCorollaryThreePrimeWeight_monotoneOn rank hy hs hxi
  have hnonneg : ∀ x ∈ Set.Icc B A, 0 ≤ b x :=
    fun x hx => (iwaniecCorollaryThreePrimeWeight_pos_on rank hy hs hxi hx).le
  have herr := hsource b B A hB hBA hmono hnonneg
  have herr' : |iwaniecCorollaryThreePrimeSum rank level s - J| ≤ C * b A * E := by
    simpa only [iwaniecCorollaryThreePrimeSum, J, A, B, L, ξ, b, E,
      iwaniecExpReciprocalScale, Real.log_exp] using herr
  have hint : J < T := by
    have hh := mul_lt_mul_of_pos_left (iwaniecAuxLemmaEleven_closed rank hy hs hxi)
      (inv_pos.mpr (sq_pos_of_pos hL))
    dsimp [J, B, A, b]
    rw [iwaniecCorollaryThree_integral rank hy (show 1 < s by linarith) hxi]
    simpa only [T, L, div_eq_mul_inv, mul_comm] using hh
  have hTau : 0 ≤ iwaniecAuxTau rank level s := (iwaniecAuxTau_pos rank level (by linarith)).le
  have hsquare : s ^ 2 ≤ ξ ^ 2 := by nlinarith only [hs0, hxi]
  have hbA : b A ≤ 20 * ξ ^ 2 * T := by
    dsimp [b, A]
    rw [iwaniecCorollaryThreePrimeWeight_at_scale rank hy (show 1 < s by linarith)]
    calc
      _ ≤ (20 * s ^ 2 * iwaniecAuxTau rank level s) / L ^ 2 :=
        div_le_div_of_nonneg_right (iwaniecCorollaryThreeScaledProfile_endpoint_bound rank level hs3)
          (sq_nonneg L)
      _ ≤ (20 * ξ ^ 2 * iwaniecAuxTau rank level s) / L ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hTau)
          (sq_nonneg L)
      _ = _ := by dsimp [T]; ring
  have hbudget : C * b A * E ≤ T * (20 * C * ξ ^ 2 * E) := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbA hC.le)
      (show 0 ≤ E from (Real.exp_pos (-Real.sqrt (L / ξ))).le)
    convert hh using 1 <;> ring
  have habs := (le_abs_self (iwaniecCorollaryThreePrimeSum rank level s - J)).trans herr'
  change iwaniecCorollaryThreePrimeSum rank level s ≤ T * (1 + 20 * C * ξ ^ 2 * E)
  calc
    _ ≤ J + C * b A * E := by linarith only [habs]
    _ ≤ T + T * (20 * C * ξ ^ 2 * E) := add_le_add hint.le hbudget
    _ = _ := by ring

end

end Erdos1212Kernel
