import Erdos1212Kernel.IwaniecPaperAUniformCount
import Erdos1212Kernel.IwaniecPaperSupportReferenceTransport
import Erdos1212Kernel.IwaniecShiftedIntervalLowerSieve

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Quantitative error support on exactly the first card(Q) reference
primes, consuming the proved equality with the actual A-carrier. -/
theorem exists_iwaniecCubicShiftedErrorMass_log_sq_bound :
    ∃ D : Real, 0 < D ∧ ∀ (r y : Nat) (Q : Finset Nat), 0 < r →
      iwaniecStrictReferenceCutoff Q.card ^ 2 ≤ y →
      iwaniecCubicShiftedErrorMass r y Q ≤ D * (y : Real) / Real.log (y : Real) ^ 2 := by
  obtain ⟨D, hD, hcount⟩ := exists_iwaniecPaperA_uniform_count_bound
  refine ⟨D, hD, ?_⟩
  intro r y Q hr hy
  let z := iwaniecStrictReferenceCutoff Q.card
  have hz2 : 2 ≤ z := two_le_iwaniecStrictReferenceCutoff Q.card
  have hzy : z ≤ y := by
    have hzp : z ≤ z ^ 2 := by nlinarith only [hz2]
    exact hzp.trans hy
  have hy1 : (1 : Real) < y := by exact_mod_cast (show 1 < y by omega)
  have hz0 : (0 : Real) < z := by exact_mod_cast (show 0 < z by omega)
  have hz1 : (1 : Real) < z := by exact_mod_cast (show 1 < z by omega)
  have hpow : (z : Real) ^ 2 ≤ (y : Real) := by exact_mod_cast hy
  have hlog := Real.log_le_log (pow_pos hz0 2) hpow
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs2 : 2 ≤ Real.log (y : Real) / Real.log (z : Real) := by
    apply (le_div_iff₀ (Real.log_pos hz1)).mpr
    linarith only [hlog]
  rw [iwaniecCubicShiftedErrorMass_eq_paperA hr Q hzy]
  exact hcount (2 * r - 1) (by omega) (y : Real) (Real.log (y : Real) / Real.log (z : Real)) hy1 hs2

/-- The support gain is consumed by the actual arbitrary-prime-state
interval inequality. Its main term remains the canonical reference tree. -/
theorem exists_iwaniecPrimeState_reference_error_bound :
    ∃ D : Real, 0 < D ∧ ∀ (r y lower length : Nat) (Q : Finset Nat), 0 < r →
      (∀ q ∈ Q, Nat.Prime q) → iwaniecStrictReferenceCutoff Q.card ^ 2 ≤ y →
      (length : Real) * ((iwaniecActualPrimeStateEuler Q / iwaniecReferencePrimePoolEuler Q.card) *
        iwaniecCubicWeightedMainExpansion r y (iwaniecReferencePrimePool Q.card)) -
        D * (y : Real) / Real.log (y : Real) ^ 2 ≤ (primeStateAvoidingIndices Q lower length).card := by
  obtain ⟨D, hD, herr⟩ := exists_iwaniecCubicShiftedErrorMass_log_sq_bound
  refine ⟨D, hD, ?_⟩
  intro r y lower length Q hr hprime hy
  have hbase := iwaniecCubic_reference_main_sub_errorMass_le_actualState (y := y) hr Q lower length hprime
  have herror := herr r y Q hr hy
  linarith only [hbase, herror]

end

end Erdos1212Kernel
