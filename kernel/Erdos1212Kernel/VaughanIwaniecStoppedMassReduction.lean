import Erdos1212Kernel.IwaniecWeightedStoppedMass
import Erdos1212Kernel.IwaniecPrimePoolEuler
import Erdos1212Kernel.IwaniecCubicStoppedMassSplit
import Erdos1212Kernel.IwaniecUntruncatedThresholdMass

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

def iwaniecPrimePoolStoppedMass (r y cutoff : Nat) : Real :=
  iwaniecWeightedStoppedMass r (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight []
    (iwaniecDescendingFactors (vaughanPrimePool cutoff))

def iwaniecPrimePoolTerminalMass (r y cutoff : Nat) : Real :=
  iwaniecCubicTerminalMass r (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight []
    (iwaniecDescendingFactors (vaughanPrimePool cutoff))

def iwaniecPrimePoolThresholdMass (r y cutoff : Nat) : Real :=
  iwaniecCubicThresholdMass r (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight []
    (iwaniecDescendingFactors (vaughanPrimePool cutoff))

def iwaniecPrimePoolUntruncatedRank (cutoff : Nat) : Nat :=
  (vaughanPrimePool cutoff).card + 1

def iwaniecPrimePoolCubicFailureMass (y cutoff : Nat) : Real :=
  iwaniecUntruncatedThresholdMass (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight []
    (iwaniecDescendingFactors (vaughanPrimePool cutoff))

theorem iwaniecPrimePoolUntruncatedRank_pos (cutoff : Nat) :
    0 < iwaniecPrimePoolUntruncatedRank cutoff := by
  unfold iwaniecPrimePoolUntruncatedRank
  omega

theorem iwaniecPrimePoolTerminalMass_untruncated_eq_zero
    (y cutoff : Nat) :
    iwaniecPrimePoolTerminalMass
      (iwaniecPrimePoolUntruncatedRank cutoff) y cutoff = 0 := by
  unfold iwaniecPrimePoolTerminalMass
  apply iwaniecCubicTerminalMass_eq_zero_of_totalDepth
  simp [iwaniecPrimePoolUntruncatedRank, iwaniecDescendingFactors]
  omega

theorem iwaniecPrimePoolThresholdMass_untruncated_eq_cubicFailure
    (y cutoff : Nat) :
    iwaniecPrimePoolThresholdMass
        (iwaniecPrimePoolUntruncatedRank cutoff) y cutoff =
      iwaniecPrimePoolCubicFailureMass y cutoff := by
  unfold iwaniecPrimePoolThresholdMass
    iwaniecPrimePoolCubicFailureMass
  apply iwaniecCubicThresholdMass_eq_untruncated_of_totalDepth
  simp [iwaniecPrimePoolUntruncatedRank, iwaniecDescendingFactors]
  omega

theorem iwaniecPrimePoolStoppedMass_eq_terminal_add_threshold
    (r y cutoff : Nat) :
    iwaniecPrimePoolStoppedMass r y cutoff =
      iwaniecPrimePoolTerminalMass r y cutoff +
        iwaniecPrimePoolThresholdMass r y cutoff := by
  exact iwaniecWeightedStoppedMass_eq_terminal_add_threshold _ _ _ _ _

/-- Final actual-state reduction with every signed quantity removed.  The sole
new analytic object is the nonnegative stopped mass. -/
theorem vaughanIwaniec_stoppedMass_reduction
    {Q : Finset Nat} {cutoff lower length r y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff)
    (hr : 0 < r) (hy : 1 < y) (hcutoffY : cutoff < y) :
    (length : Real) *
          (Erdos696.Mertens.mertensProd cutoff -
            iwaniecPrimePoolStoppedMass r y cutoff) -
        y - (Q.card * (length / cutoff + 1) : Nat) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have htree := vaughanIwaniec_primePool_mainTree_reduction
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    (r := r) (y := y) hprime hcutoff hr hy hcutoffY
  have htreeLower := euler_sub_stoppedMass_le_iwaniecWeightedTree
    r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
    (iwaniecDescendingFactors (vaughanPrimePool cutoff))
  rw [vaughanPrimePool_euler_eq_mertensProd] at htreeLower
  have hlengthNonneg : (0 : Real) ≤ length := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htreeLower hlengthNonneg
  unfold iwaniecPrimePoolStoppedMass
  linarith

theorem iwaniecPrimePoolStoppedMass_nonneg
    (r y cutoff : Nat) :
    0 ≤ iwaniecPrimePoolStoppedMass r y cutoff := by
  unfold iwaniecPrimePoolStoppedMass
  exact iwaniecWeightedStoppedMass_nonneg _ _ _ _ _

/-- Fully split final reduction: terminal depth tail and cubic-threshold tail
are now independent positive analytic targets. -/
theorem vaughanIwaniec_terminal_threshold_reduction
    {Q : Finset Nat} {cutoff lower length r y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff)
    (hr : 0 < r) (hy : 1 < y) (hcutoffY : cutoff < y) :
    (length : Real) *
          (Erdos696.Mertens.mertensProd cutoff -
            iwaniecPrimePoolTerminalMass r y cutoff -
            iwaniecPrimePoolThresholdMass r y cutoff) -
        y - (Q.card * (length / cutoff + 1) : Nat) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have h := vaughanIwaniec_stoppedMass_reduction
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    (r := r) (y := y) hprime hcutoff hr hy hcutoffY
  rw [iwaniecPrimePoolStoppedMass_eq_terminal_add_threshold] at h
  linarith

/-- With the finite pool's untruncated rank, the sole remaining analytic loss
is the cubic-threshold mass. -/
theorem vaughanIwaniec_thresholdOnly_reduction
    {Q : Finset Nat} {cutoff lower length y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff)
    (hy : 1 < y) (hcutoffY : cutoff < y) :
    (length : Real) *
          (Erdos696.Mertens.mertensProd cutoff -
            iwaniecPrimePoolThresholdMass
              (iwaniecPrimePoolUntruncatedRank cutoff) y cutoff) -
        y - (Q.card * (length / cutoff + 1) : Nat) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have h := vaughanIwaniec_terminal_threshold_reduction
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    (r := iwaniecPrimePoolUntruncatedRank cutoff) (y := y)
    hprime hcutoff (iwaniecPrimePoolUntruncatedRank_pos cutoff)
    hy hcutoffY
  rw [iwaniecPrimePoolTerminalMass_untruncated_eq_zero] at h
  simpa using h

/-- Canonical final sieve reduction: only the first cubic-failure mass
remains. -/
theorem vaughanIwaniec_cubicFailureOnly_reduction
    {Q : Finset Nat} {cutoff lower length y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff)
    (hy : 1 < y) (hcutoffY : cutoff < y) :
    (length : Real) *
          (Erdos696.Mertens.mertensProd cutoff -
            iwaniecPrimePoolCubicFailureMass y cutoff) -
        y - (Q.card * (length / cutoff + 1) : Nat) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have h := vaughanIwaniec_thresholdOnly_reduction
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    (y := y) hprime hcutoff hy hcutoffY
  rw [iwaniecPrimePoolThresholdMass_untruncated_eq_cubicFailure] at h
  exact h

end

end Erdos1212Kernel
