import Erdos1212Kernel.VaughanSmallPoolLower
import Erdos1212Kernel.VaughanJacobsthalLargePrimeComparison

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 700000

def primeStateRealLargePart (Q : Finset Nat) (X : Real) : Finset Nat :=
  Q.filter fun q => X ≤ (q : Real)

def primeStateRealLargeKilledIndices
    (Q : Finset Nat) (X : Real) (lower length : Nat) : Finset Nat :=
  (primeStateRealLargePart Q X).biUnion fun q =>
    fixedProgressionKilledIndicesRange 1 0 lower length q

theorem primeStateAvoiding_strictPool_subset_full_union_realLargeKilled
    (Q : Finset Nat) (X : Real) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower length ⊆
      primeStateAvoidingIndices Q lower length ∪
        primeStateRealLargeKilledIndices Q X lower length := by
  classical
  intro index hindex
  have hindexData := Finset.mem_filter.mp hindex
  by_cases hfull : ∀ q ∈ Q, ¬q ∣ lower + 1 + index
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hindexData.1, hfull⟩)
  · apply Finset.mem_union_right
    rw [primeStateRealLargeKilledIndices, Finset.mem_biUnion]
    push Not at hfull
    obtain ⟨q, hq, hqDvd⟩ := hfull
    have hqLarge : X ≤ (q : Real) := by
      by_contra hnotLarge
      have hqPool : q ∈ iwaniecStrictPrimePool X :=
        mem_iwaniecStrictPrimePool.mpr ⟨hprime q hq, lt_of_not_ge hnotLarge⟩
      exact hindexData.2 q hqPool hqDvd
    refine ⟨q, Finset.mem_filter.mpr ⟨hq, hqLarge⟩, ?_⟩
    apply Finset.mem_filter.mpr
    rw [fixedProgressionCandidate_one_zero]
    exact ⟨hindexData.1, hqDvd⟩

theorem primeStateRealLargeKilledIndices_card_le_sum
    {Q : Finset Nat} {X : Real} {lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (primeStateRealLargeKilledIndices Q X lower length).card ≤
      ∑ q ∈ primeStateRealLargePart Q X, (length / q + 1) := by
  unfold primeStateRealLargeKilledIndices
  calc
    _ ≤ ∑ q ∈ primeStateRealLargePart Q X,
        (fixedProgressionKilledIndicesRange 1 0 lower length q).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      exact fixedProgressionKilledIndicesRange_card_le
        (hprime q hqData.1) (hprime q hqData.1).not_dvd_one

/-- The exact real-cutoff loss in Vaughan (11). Every remaining prime
is at least X because the comparison pool contains precisely p<X. -/
theorem primeStateRealLargeKilledIndices_card_bound
    {Q : Finset Nat} {X : Real} {lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hX : 0 < X) :
    ((primeStateRealLargeKilledIndices Q X lower length).card : Real) ≤
      (Q.card : Real) * ((length : Real) / X + 1) := by
  have hsumNat := primeStateRealLargeKilledIndices_card_le_sum
    (Q := Q) (X := X) (lower := lower) (length := length) hprime
  have hsum : ((primeStateRealLargeKilledIndices Q X lower length).card : Real) ≤
      ∑ q ∈ primeStateRealLargePart Q X, ((length / q + 1 : Nat) : Real) := by
    exact_mod_cast hsumNat
  calc
    _ ≤ ∑ q ∈ primeStateRealLargePart Q X, ((length / q + 1 : Nat) : Real) := hsum
    _ ≤ ∑ _q ∈ primeStateRealLargePart Q X, ((length : Real) / X + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      have hqPrime := hprime q hqData.1
      have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
      have hmulNat := Nat.div_mul_le_self length q
      have hmul : ((length / q : Nat) : Real) * (q : Real) ≤ (length : Real) := by
        exact_mod_cast hmulNat
      have hdiv : ((length / q : Nat) : Real) ≤ (length : Real) / (q : Real) :=
        (le_div_iff₀ hqPos).mpr hmul
      have hanti := div_le_div_of_nonneg_left (Nat.cast_nonneg length) hX hqData.2
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith only [hdiv, hanti]
    _ = ((primeStateRealLargePart Q X).card : Real) * ((length : Real) / X + 1) := by simp <;> ring
    _ ≤ _ := by
      have hcard : (primeStateRealLargePart Q X).card ≤ Q.card :=
        Finset.card_le_card (Finset.filter_subset (fun q : Nat => X ≤ (q : Real)) Q)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Vaughan equation (11), with the literal strict real cutoff and its
closed complementary endpoint p>=X. -/
theorem primeStateAvoiding_full_realCutoff_lower
    {Q : Finset Nat} {X : Real} {lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hX : 0 < X) :
    ((primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower length).card : Real) -
        (Q.card : Real) * ((length : Real) / X + 1) ≤
      ((primeStateAvoidingIndices Q lower length).card : Real) := by
  have hsubset := primeStateAvoiding_strictPool_subset_full_union_realLargeKilled
    Q X lower length hprime
  have hcardSubset := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le
    (primeStateAvoidingIndices Q lower length)
    (primeStateRealLargeKilledIndices Q X lower length)
  have hbad := primeStateRealLargeKilledIndices_card_bound
    (Q := Q) (X := X) (lower := lower) (length := length) hprime hX
  have hnat : (primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower length).card ≤
      (primeStateAvoidingIndices Q lower length).card +
        (primeStateRealLargeKilledIndices Q X lower length).card :=
    hcardSubset.trans hunion
  have hreal : ((primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower length).card : Real) ≤
      (primeStateAvoidingIndices Q lower length).card +
        (primeStateRealLargeKilledIndices Q X lower length).card := by exact_mod_cast hnat
  linarith only [hreal, hbad]

end

end Erdos1212Kernel
