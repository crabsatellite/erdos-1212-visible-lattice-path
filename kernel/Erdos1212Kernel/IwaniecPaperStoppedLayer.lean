import Erdos1212Kernel.IwaniecThresholdRealTransport
import Erdos1212Kernel.IwaniecPaperD2Suffix
import Erdos1212Kernel.IwaniecPaperMainLayers

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- A literal stopped layer on the complete strict prime pool. -/
def iwaniecPaperStoppedLayer (offset : Nat) (level z : Real) (k : Nat) : Real :=
  iwaniecCubicRealThresholdLayer offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) k

def iwaniecPaperStoppedPartial (offset : Nat) (level z : Real) (depth : Nat) : Real :=
  iwaniecCubicRealThresholdPartial offset level (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) depth

@[simp] theorem iwaniecPaperStoppedLayer_zero (offset : Nat) (level z : Real) :
    iwaniecPaperStoppedLayer offset level z 0 = 0 := by simp [iwaniecPaperStoppedLayer]

theorem iwaniecPaperStoppedLayer_nonneg (offset : Nat) (level z : Real) (k : Nat) :
    0 ≤ iwaniecPaperStoppedLayer offset level z k := iwaniecCubicRealThresholdLayer_nonneg _ _ _ _

theorem iwaniecPaperStoppedLayer_eq_zero_of_card (offset : Nat) (level z : Real) (k : Nat)
    (hk : (iwaniecStrictPrimePool z).card < k) : iwaniecPaperStoppedLayer offset level z k = 0 := by
  apply iwaniecCubicRealThresholdLayer_eq_zero_of_length
  simpa [iwaniecDescendingFactors] using hk

theorem iwaniecPaperStoppedLayer_add_two (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer (offset + 2) level z k = iwaniecPaperStoppedLayer offset level z k :=
  iwaniecCubicRealThresholdLayer_add_two _ _ _ _

theorem iwaniecPaperStoppedLayer_parity (offset : Nat) (level z : Real) (k : Nat)
    (hk : ¬Even (offset + k)) : iwaniecPaperStoppedLayer offset level z k = 0 :=
  iwaniecCubicRealThresholdLayer_parity _ _ _ _ hk

/-- Exact first-prime identity. The successful child has the literal
real quotient level/p, and the failed last prime has exactly R(p)/p. -/
theorem iwaniecPaperStoppedLayer_first_prime (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer offset level z (k + 1) =
      ∑ p ∈ iwaniecStrictPrimePool z,
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecPaperStoppedLayer (offset + 1) (level / p) p k
        else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0 := by
  classical
  change iwaniecCubicRealThresholdLayer offset level
    (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (k + 1) = _
  rw [iwaniecCubicRealThresholdLayer_eq_sum_firstFactor]
  calc
    _ = ∑ i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length,
        if Even offset ∨ ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) ^ 3 < level then
          ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real)⁻¹ *
            iwaniecPaperStoppedLayer (offset + 1)
              (level / (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i])
              ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) k
        else if k = 0 then ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real)⁻¹ *
          iwaniecPaperR ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iwaniecPaperR_suffix z i, abs_of_pos (iwaniecPaperR_pos _), iwaniecStrictPrimeSuffix z i] <;> rfl
    _ = _ := iwaniecSum_descendingFactors_real (iwaniecStrictPrimePool z)
      (fun p : Nat => if Even offset ∨ (p : Real) ^ 3 < level then
        (p : Real)⁻¹ * iwaniecPaperStoppedLayer (offset + 1) (level / p) (p : Real) k
      else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0)

/-- Consume the real-level transport in the original finite main term. -/
theorem iwaniecCubicWeightedMainExpansion_stopped_partial {r y : Nat} (hr : 0 < r) (z : Real) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) = iwaniecPaperR z -
      iwaniecPaperStoppedPartial 0 y z (2 * r) -
      iwaniecSurvivalLayer (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r) := by
  have hpositive : ∀ p ∈ iwaniecDescendingFactors (iwaniecStrictPrimePool z), 0 < p := by
    intro p hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by simpa [iwaniecDescendingFactors] using hp
    exact (mem_iwaniecStrictPrimePool.mp hpPool).1.pos
  rw [iwaniecCubicWeightedMainExpansion_full_layers hr z,
    iwaniecThresholdPartialMass_root_eq_realLevel y _ (2 * r) hpositive] <;> rfl

theorem iwaniecCubicWeightedMainExpansion_stopped_partial_no_tail {r y : Nat} (hr : 0 < r) (z : Real)
    (hcard : (iwaniecStrictPrimePool z).card < 2 * r) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) =
      iwaniecPaperR z - iwaniecPaperStoppedPartial 0 y z (2 * r) := by
  rw [iwaniecCubicWeightedMainExpansion_stopped_partial hr z,
    iwaniecSurvivalLayer_eq_zero_of_length _ _ _ _ _ (by simpa [iwaniecDescendingFactors] using hcard), sub_zero]

end

end Erdos1212Kernel
