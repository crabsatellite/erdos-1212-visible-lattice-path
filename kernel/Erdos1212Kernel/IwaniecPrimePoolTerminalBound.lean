import Erdos1212Kernel.IwaniecTerminalElementaryBound
import Erdos1212Kernel.VaughanIwaniecStoppedMassReduction

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

theorem sum_abs_reciprocal_descendingFactors
    (factors : Finset Nat) :
    ((iwaniecDescendingFactors factors).map fun p =>
        |iwaniecReciprocalFactorWeight p|).sum =
      ∑ p ∈ factors, (p : Real)⁻¹ := by
  let weight := fun p : Nat => |iwaniecReciprocalFactorWeight p|
  have hperm := Finset.sort_perm_toList factors
    (fun left right : Nat => right ≤ left)
  calc
    ((iwaniecDescendingFactors factors).map weight).sum =
        (factors.toList.map weight).sum :=
      List.Perm.sum_eq (hperm.map weight)
    _ = ∑ p ∈ factors, weight p := Finset.sum_map_toList factors weight
    _ = ∑ p ∈ factors, (p : Real)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [weight, iwaniecReciprocalFactorWeight]
      rw [abs_of_nonneg]
      positivity

theorem reciprocalPrime_eulerFactor_abs_le_one
    {p : Nat} (hp : Nat.Prime p) :
    |1 - iwaniecReciprocalFactorWeight p| ≤ 1 := by
  have hinvNonneg : (0 : Real) ≤ (p : Real)⁻¹ := by positivity
  have hinvLe : (p : Real)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  unfold iwaniecReciprocalFactorWeight
  rw [abs_of_nonneg (sub_nonneg.mpr hinvLe)]
  linarith

/-- The terminal `2r` tail is completely controlled by a factorial moment of
the prime reciprocal sum. -/
theorem factorial_mul_iwaniecPrimePoolTerminalMass_le
    (r y cutoff : Nat) (hr : 0 < r) :
    ((2 * r).factorial : Real) *
        iwaniecPrimePoolTerminalMass r y cutoff ≤
      Erdos696.Mertens.primeReciprocalSum cutoff ^ (2 * r) := by
  let factors := iwaniecDescendingFactors (vaughanPrimePool cutoff)
  have hfactor : ∀ p ∈ factors,
      |1 - iwaniecReciprocalFactorWeight p| ≤ 1 := by
    intro p hp
    have hpPool : p ∈ vaughanPrimePool cutoff := by
      simpa [factors, iwaniecDescendingFactors] using hp
    exact reciprocalPrime_eulerFactor_abs_le_one
      (vaughanPrimePool_prime cutoff p hpPool)
  have hterminal := iwaniecCubicTerminalMass_le_elementary
    r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight
    [] factors (by simp; omega) hfactor
  have hfactorialNonneg : (0 : Real) ≤ (2 * r).factorial := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hterminal hfactorialNonneg
  have helementary := factorial_mul_iwaniecElementaryMass_le_sum_pow
    iwaniecReciprocalFactorWeight (2 * r) factors
  unfold iwaniecPrimePoolTerminalMass
  change ((2 * r).factorial : Real) *
      iwaniecCubicTerminalMass r (iwaniecCubicEvenRestriction y)
        iwaniecReciprocalFactorWeight [] factors ≤ _
  calc
    ((2 * r).factorial : Real) *
        iwaniecCubicTerminalMass r (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [] factors ≤
      ((2 * r).factorial : Real) *
        iwaniecElementaryMass iwaniecReciprocalFactorWeight (2 * r) factors :=
      hscaled
    _ ≤ (factors.map fun p => |iwaniecReciprocalFactorWeight p|).sum ^
        (2 * r) := helementary
    _ = (∑ p ∈ vaughanPrimePool cutoff, (p : Real)⁻¹) ^
        (2 * r) := by
      rw [sum_abs_reciprocal_descendingFactors]
    _ = Erdos696.Mertens.primeReciprocalSum cutoff ^ (2 * r) := by
      rw [vaughanPrimePool_reciprocalSum_eq_mertens]

end

end Erdos1212Kernel
