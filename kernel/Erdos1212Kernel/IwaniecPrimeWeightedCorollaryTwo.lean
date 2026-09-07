import Erdos1212Kernel.IwaniecReciprocalLogConstantWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def iwaniecCorollaryTwoMain (L B A : Real) : Real :=
  L⁻¹ * Real.log
    (((L / Real.log B) - 1) / ((L / Real.log A) - 1))

def iwaniecCorollaryTwoEndpoint (L A : Real) : Real :=
  L⁻¹ * Real.log
    (((L / Real.log A) - 1) /
      ((L / Real.log (A + 1)) - 1))

/-- Qualitative, fully explicit version of Iwaniec 1971, Corollary 2.  The
effective exponential rate is replaced by arbitrary `epsilon, delta`, while
the target main term and final endpoint interval are evaluated exactly. -/
theorem eventually_iwaniecPrimeWeightedCorollaryTwo
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ L : Real, ∀ B A : Nat,
      B₀ ≤ B → B ≤ A → 0 < L →
      ((A + 1 : Nat) : Real) < Real.exp L →
      iwaniecCorollaryTwoMain L B A -
          2 * epsilon * (L - Real.log A)⁻¹ ≤
        iwaniecPrimeReciprocalWeightedInterval
          (fun n => iwaniecReciprocalLogConstantWeight L n) B A ∧
      iwaniecPrimeReciprocalWeightedInterval
          (fun n => iwaniecReciprocalLogConstantWeight L n) B A ≤
        iwaniecCorollaryTwoMain L B A +
          delta * iwaniecCorollaryTwoMain L B A +
          (1 + delta) * iwaniecCorollaryTwoEndpoint L A +
          2 * epsilon * (L - Real.log A)⁻¹ := by
  obtain ⟨B₁, hB₁⟩ :=
    eventually_iwaniecWeightedPrimeIntegral_target_bounds hepsilon hdelta
  refine ⟨max 3 B₁, ?_⟩
  intro L B A hB hBA hL hAexp
  have hBThree : 3 ≤ B := (Nat.le_max_left 3 B₁).trans hB
  have hBBase : B₁ ≤ B := (Nat.le_max_right 3 B₁).trans hB
  have hsubset :
      Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real) ⊆
        Set.Ioo (1 : Real) (Real.exp L) := by
    intro x hx
    have hpred : (2 : Real) ≤ ((B - 1 : Nat) : Real) := by
      norm_cast
      omega
    exact ⟨lt_of_lt_of_le one_lt_two (hpred.trans hx.1),
      hx.2.trans_lt hAexp⟩
  have hbounds := hB₁ B A (iwaniecReciprocalLogConstantWeight L)
    hBBase hBA
    ((iwaniecReciprocalLogConstantWeight_continuousOn L).mono hsubset)
    ((iwaniecReciprocalLogConstantWeight_monotoneOn L).mono hsubset)
    (fun x hx => iwaniecReciprocalLogConstantWeight_nonnegOn L x
      (hsubset hx))
  have hBOne : (1 : Real) < B := by exact_mod_cast (show 1 < B by omega)
  have hAOne : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
  have hAASucc : (A : Real) < ((A + 1 : Nat) : Real) := by
    exact_mod_cast (show A < A + 1 by omega)
  have hARealExp : (A : Real) < Real.exp L := hAASucc.trans hAexp
  have hmain := iwaniecWeightedLogKernelIntegral_constantWeight_eval
    hL hBOne (by exact_mod_cast hBA) hARealExp
  have hendpoint := iwaniecWeightedLogKernelIntegral_constantWeight_eval
    hL hAOne hAASucc.le hAexp
  rw [hmain, hendpoint,
    iwaniecReciprocalLogConstantWeight_eq] at hbounds
  simpa [iwaniecCorollaryTwoMain, iwaniecCorollaryTwoEndpoint] using hbounds

end

end Erdos1212Kernel
