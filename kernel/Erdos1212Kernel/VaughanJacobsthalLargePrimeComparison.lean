import Erdos1212Kernel.StateJacobsthalCompositeSurvivor
import Erdos1212Kernel.FixedCompositeProgressionSurvivor

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

def primeStateAvoidingIndices
    (Q : Finset Nat) (lower length : Nat) : Finset Nat :=
  (Finset.range length).filter fun index =>
    ∀ q ∈ Q, ¬ q ∣ lower + 1 + index

def primeStateSmallPart (Q : Finset Nat) (cutoff : Nat) : Finset Nat :=
  Q.filter fun q => q ≤ cutoff

def primeStateLargePart (Q : Finset Nat) (cutoff : Nat) : Finset Nat :=
  Q.filter fun q => cutoff < q

def primeStateLargeKilledIndices
    (Q : Finset Nat) (cutoff lower length : Nat) : Finset Nat :=
  (primeStateLargePart Q cutoff).biUnion fun q =>
    fixedProgressionKilledIndicesRange 1 0 lower length q

theorem fixedProgressionCandidate_one_zero
    (lower index : Nat) :
    fixedProgressionCandidate 1 0 lower index = lower + 1 + index := by
  simp [fixedProgressionCandidate, fixedProgressionBase]

theorem primeStateAvoidingSmall_subset_full_union_largeKilled
    (Q : Finset Nat) (cutoff lower length : Nat) :
    primeStateAvoidingIndices (primeStateSmallPart Q cutoff) lower length ⊆
      primeStateAvoidingIndices Q lower length ∪
        primeStateLargeKilledIndices Q cutoff lower length := by
  classical
  intro index hindex
  have hindexData := Finset.mem_filter.mp hindex
  by_cases hfull : ∀ q ∈ Q, ¬ q ∣ lower + 1 + index
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨hindexData.1, hfull⟩)
  · apply Finset.mem_union_right
    rw [primeStateLargeKilledIndices, Finset.mem_biUnion]
    push Not at hfull
    obtain ⟨q, hq, hqDvd⟩ := hfull
    have hqLarge : cutoff < q := by
      by_contra hnotLarge
      have hqSmall : q ∈ primeStateSmallPart Q cutoff :=
        Finset.mem_filter.mpr ⟨hq, by omega⟩
      exact hindexData.2 q hqSmall hqDvd
    refine ⟨q, Finset.mem_filter.mpr ⟨hq, hqLarge⟩, ?_⟩
    apply Finset.mem_filter.mpr
    rw [fixedProgressionCandidate_one_zero]
    exact ⟨hindexData.1, hqDvd⟩

theorem primeStateLargeKilledIndices_card_le_sum
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (primeStateLargeKilledIndices Q cutoff lower length).card ≤
      ∑ q ∈ primeStateLargePart Q cutoff, (length / q + 1) := by
  unfold primeStateLargeKilledIndices
  calc
    ((primeStateLargePart Q cutoff).biUnion fun q =>
        fixedProgressionKilledIndicesRange 1 0 lower length q).card ≤
      ∑ q ∈ primeStateLargePart Q cutoff,
        (fixedProgressionKilledIndicesRange 1 0 lower length q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ q ∈ primeStateLargePart Q cutoff, (length / q + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      exact fixedProgressionKilledIndicesRange_card_le
        (hprime q hqData.1) (hprime q hqData.1).not_dvd_one

theorem nat_div_anti_right
    {numerator left right : Nat} (hleft : 0 < left) (hle : left ≤ right) :
    numerator / right ≤ numerator / left := by
  apply (Nat.le_div_iff_mul_le hleft).2
  calc
    numerator / right * left ≤ numerator / right * right :=
      Nat.mul_le_mul_left _ hle
    _ ≤ numerator := Nat.div_mul_le_self numerator right

theorem primeStateLargeKilledIndices_card_le
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff) :
    (primeStateLargeKilledIndices Q cutoff lower length).card ≤
      Q.card * (length / cutoff + 1) := by
  have hsum := primeStateLargeKilledIndices_card_le_sum
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length) hprime
  calc
    (primeStateLargeKilledIndices Q cutoff lower length).card ≤
        ∑ q ∈ primeStateLargePart Q cutoff, (length / q + 1) := hsum
    _ ≤ ∑ _q ∈ primeStateLargePart Q cutoff,
        (length / cutoff + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqLarge := (Finset.mem_filter.mp hq).2
      exact Nat.add_le_add_right
        (nat_div_anti_right hcutoff (by omega)) 1
    _ = (primeStateLargePart Q cutoff).card *
        (length / cutoff + 1) := by simp
    _ ≤ Q.card * (length / cutoff + 1) := by
      exact Nat.mul_le_mul_right _
        (Finset.card_le_card (Finset.filter_subset _ _))

/-- Vaughan's exact large-prime comparison, before the Rosser lower sieve.
The loss is charged only to actual state primes above `cutoff`. -/
theorem primeStateAvoiding_full_card_lower
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff) :
    (primeStateAvoidingIndices (primeStateSmallPart Q cutoff)
        lower length).card - Q.card * (length / cutoff + 1) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hsubset := primeStateAvoidingSmall_subset_full_union_largeKilled
    Q cutoff lower length
  have hcardSubset := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le
    (primeStateAvoidingIndices Q lower length)
    (primeStateLargeKilledIndices Q cutoff lower length)
  have hbad := primeStateLargeKilledIndices_card_le
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    hprime hcutoff
  omega

end

end Erdos1212Kernel
