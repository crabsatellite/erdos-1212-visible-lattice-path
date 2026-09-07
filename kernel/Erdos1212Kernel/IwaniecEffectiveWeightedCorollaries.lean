import Erdos1212Kernel.IwaniecLemma13Real
import Erdos1212Kernel.IwaniecPrimeWeightedCorollaryOne
import Erdos1212Kernel.IwaniecPrimeWeightedCorollaryTwo

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 600000

theorem iwaniecWeightedLogKernelIntegral_eq_div_integral (b : Real → Real) (B A : Real) :
    iwaniecWeightedLogKernelIntegral b B A = ∫ x in B..A, b x / (x * Real.log x) := by
  unfold iwaniecWeightedLogKernelIntegral
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold iwaniecLogKernel
  ring

theorem exists_iwaniecPrimeWeightedCorollaryTwo_effective :
    ∃ C : Real, 0 < C ∧ ∀ L B A : Real, 0 < L → 2 ≤ B → B ≤ A → A < Real.exp L →
      |iwaniecPrimeReciprocalWeightedRealInterval (iwaniecReciprocalLogConstantWeight L) B A -
        iwaniecCorollaryTwoMain L B A| ≤
          C * (L - Real.log A)⁻¹ * Real.exp (-Real.sqrt (Real.log B)) := by
  obtain ⟨C, hC, hsource⟩ := exists_iwaniecLemma13_real_constant
  refine ⟨C, hC, ?_⟩
  intro L B A hL hB hBA hA
  have hsubset : Icc B A ⊆ Ioo (1 : Real) (Real.exp L) := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans_lt hA⟩
  have hh := hsource (iwaniecReciprocalLogConstantWeight L) B A hB hBA
    ((iwaniecReciprocalLogConstantWeight_monotoneOn L).mono hsubset)
    (fun x hx => iwaniecReciprocalLogConstantWeight_nonnegOn L x (hsubset hx))
  rw [← iwaniecWeightedLogKernelIntegral_eq_div_integral,
    iwaniecWeightedLogKernelIntegral_constantWeight_eval hL (by linarith) hBA hA,
    iwaniecReciprocalLogConstantWeight_eq] at hh
  exact hh

theorem exists_iwaniecPrimeWeightedCorollaryOne_effective :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat) (L B A : Real), 0 < L → 2 ≤ B → B ≤ A →
      A ≤ Real.exp (L / (iwaniecParityProfileStart r + 1)) →
      |iwaniecPrimeReciprocalWeightedRealInterval (iwaniecParityReciprocalLogWeight r L) B A -
        iwaniecCorollaryOneMain r L B A| ≤
          C * iwaniecParityReciprocalLogWeight r L A * Real.exp (-Real.sqrt (Real.log B)) := by
  obtain ⟨C, hC, hsource⟩ := exists_iwaniecLemma13_real_constant
  refine ⟨C, hC, ?_⟩
  intro r L B A hL hB hBA hcutoff
  have hstart : 0 < iwaniecParityProfileStart r :=
    zero_lt_one.trans_le (one_le_iwaniecParityProfileStart r)
  have hsubset : Icc B A ⊆ iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r) := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans hcutoff⟩
  have hAexp : A < Real.exp L :=
    (iwaniecReciprocalLogProfileDomain_subset hL hstart (hsubset ⟨hBA, le_rfl⟩)).2
  have hh := hsource (iwaniecParityReciprocalLogWeight r L) B A hB hBA
    ((iwaniecParityReciprocalLogWeight_monotoneOn r hL).mono hsubset)
    (fun x hx => iwaniecParityReciprocalLogWeight_nonneg r hL (hsubset hx))
  rw [← iwaniecWeightedLogKernelIntegral_eq_div_integral] at hh
  have hmain := iwaniecWeightedLogKernelIntegral_profile_eval
    (iwaniecParitySieveProfile r) hL (show 1 < B by linarith) hBA hAexp
  change iwaniecWeightedLogKernelIntegral (iwaniecParityReciprocalLogWeight r L) B A =
    iwaniecCorollaryOneMain r L B A at hmain
  rwa [hmain] at hh

end

end Erdos1212Kernel
