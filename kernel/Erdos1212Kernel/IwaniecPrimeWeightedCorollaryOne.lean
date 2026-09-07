import Erdos1212Kernel.IwaniecParityReciprocalLogWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecCorollaryOneMain (r : Nat) (L B A : Real) : Real :=
  L⁻¹ * (∫ t in (L / Real.log A)..(L / Real.log B),
    iwaniecParitySieveProfile r (t - 1) / (t - 1))

/-- The full parity-sensitive nonconstant profile has now been consumed by
the weighted prime-integral estimate.  This retains qualitative errors and
the last unit interval; it does not assert Lemma 13's effective error rate. -/
theorem eventually_iwaniecPrimeWeightedCorollaryOne
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ r : Nat, ∀ L : Real, ∀ B A : Nat,
      B₀ ≤ B → B ≤ A → 0 < L →
      ((A + 1 : Nat) : Real) ≤ Real.exp (L / (iwaniecParityProfileStart r + 1)) →
      iwaniecCorollaryOneMain r L B A -
          2 * epsilon * iwaniecParityReciprocalLogWeight r L A ≤
        iwaniecPrimeReciprocalWeightedInterval
          (fun n => iwaniecParityReciprocalLogWeight r L n) B A ∧
      iwaniecPrimeReciprocalWeightedInterval
          (fun n => iwaniecParityReciprocalLogWeight r L n) B A ≤
        iwaniecCorollaryOneMain r L B A +
          delta * iwaniecCorollaryOneMain r L B A +
          (1 + delta) * iwaniecCorollaryOneMain r L A (A + 1 : Nat) +
          2 * epsilon * iwaniecParityReciprocalLogWeight r L A := by
  obtain ⟨B₁, hB₁⟩ :=
    eventually_iwaniecWeightedPrimeIntegral_target_bounds hepsilon hdelta
  refine ⟨max 3 B₁, ?_⟩
  intro r L B A hB hBA hL hcutoff
  have hBThree : 3 ≤ B := (Nat.le_max_left 3 B₁).trans hB
  have hBBase : B₁ ≤ B := (Nat.le_max_right 3 B₁).trans hB
  have hstart : 0 < iwaniecParityProfileStart r :=
    zero_lt_one.trans_le (one_le_iwaniecParityProfileStart r)
  have hsubset :
      Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real) ⊆
        iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r) := by
    intro x hx
    have hpred : (2 : Real) ≤ ((B - 1 : Nat) : Real) := by
      exact_mod_cast (show 2 ≤ B - 1 by omega)
    exact ⟨lt_of_lt_of_le one_lt_two (hpred.trans hx.1), hx.2.trans hcutoff⟩
  have hbounds := hB₁ B A (iwaniecParityReciprocalLogWeight r L)
    hBBase hBA
    ((iwaniecParityReciprocalLogWeight_continuousOn r hL).mono hsubset)
    ((iwaniecParityReciprocalLogWeight_monotoneOn r hL).mono hsubset)
    (fun x hx => iwaniecParityReciprocalLogWeight_nonneg r hL (hsubset hx))
  have hBOne : (1 : Real) < B := by exact_mod_cast (show 1 < B by omega)
  have hAOne : (1 : Real) < A := by exact_mod_cast (show 1 < A by omega)
  have hASucc : (A : Real) < ((A + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_succ_self A
  have hnextDomain : ((A + 1 : Nat) : Real) ∈
      iwaniecReciprocalLogProfileDomain L (iwaniecParityProfileStart r) :=
    ⟨hAOne.trans hASucc, hcutoff⟩
  have hnextExp : ((A + 1 : Nat) : Real) < Real.exp L :=
    (iwaniecReciprocalLogProfileDomain_subset hL hstart hnextDomain).2
  have hmain := iwaniecWeightedLogKernelIntegral_profile_eval
    (iwaniecParitySieveProfile r) hL hBOne (by exact_mod_cast hBA)
    (hASucc.trans hnextExp)
  have hendpoint := iwaniecWeightedLogKernelIntegral_profile_eval
    (iwaniecParitySieveProfile r) hL hAOne hASucc.le hnextExp
  change iwaniecWeightedLogKernelIntegral (iwaniecParityReciprocalLogWeight r L)
    B A = iwaniecCorollaryOneMain r L B A at hmain
  change iwaniecWeightedLogKernelIntegral (iwaniecParityReciprocalLogWeight r L)
    A (A + 1 : Nat) = iwaniecCorollaryOneMain r L A (A + 1 : Nat) at hendpoint
  rwa [hmain, hendpoint] at hbounds

end

end Erdos1212Kernel
