import Erdos1212Kernel.RosserRestrictedPairing

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega BigOperators
open Finset Nat UniqueFactorizationMonoid

set_option maxHeartbeats 1400000

def restrictedLowerMoebiusInt
    (r : Nat) (allowed : Finset Nat → Bool) (n : Nat) : Int :=
  if ArithmeticFunction.cardFactors n < 2 * r ∧ allowed n.primeFactors then
    ArithmeticFunction.moebius n
  else 0

def restrictedLowerMoebius
    (r : Nat) (allowed : Finset Nat → Bool) (n : Nat) : Real :=
  restrictedLowerMoebiusInt r allowed n

theorem restrictedLowerMoebiusInt_subset_prod
    {n r : Nat} {allowed : Finset Nat → Bool}
    (t : Finset Nat)
    (ht : t ∈ (normalizedFactors n).toFinset.powerset) :
    restrictedLowerMoebiusInt r allowed t.val.prod =
      if t.card < 2 * r ∧ allowed t then (-1 : Int) ^ t.card else 0 := by
  obtain ⟨hsquare, homega, hmu⟩ := normalizedFactorSubset_prod_data t ht
  have hpf := normalizedFactorSubset_prod_primeFactors t ht
  unfold restrictedLowerMoebiusInt
  rw [homega, hmu, hpf]

theorem restrictedLowerMoebiusInt_divisor_sum_eq
    {n r : Nat} {allowed : Finset Nat → Bool} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, restrictedLowerMoebiusInt r allowed d) =
      rosserRestrictedAlternatingSum
        (normalizedFactors n).toFinset r allowed := by
  let factors := (normalizedFactors n).toFinset
  have hfilter :
      (∑ d ∈ n.divisors, restrictedLowerMoebiusInt r allowed d) =
        ∑ d ∈ n.divisors with Squarefree d,
          restrictedLowerMoebiusInt r allowed d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnotSquare : ¬ Squarefree d := fun hs =>
      hnot (Finset.mem_filter.mpr ⟨hd, hs⟩)
    simp [restrictedLowerMoebiusInt,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSquare]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hn]
  change (∑ t ∈ factors.powerset,
    restrictedLowerMoebiusInt r allowed t.val.prod) = _
  calc
    _ = ∑ t ∈ factors.powerset,
        (if t.card < 2 * r ∧ allowed t then (-1 : Int) ^ t.card else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact restrictedLowerMoebiusInt_subset_prod t (by simpa [factors] using ht)
    _ = ∑ t ∈ rosserAllowedSubsets factors r allowed,
        (-1 : Int) ^ t.card := by
      unfold rosserAllowedSubsets rosserTruncatedSubsets
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hcard : t.card < 2 * r <;>
        by_cases ha : allowed t <;> simp [hcard, ha]
    _ = _ := rfl

theorem restrictedLowerMoebius_isLower_of_pairing
    (r : Nat) (allowed : Finset Nat → Bool)
    (hpair : ∀ n : Nat,
      (rosserRemovedOdd (normalizedFactors n).toFinset r allowed).card ≤
        (rosserRemovedEven (normalizedFactors n).toFinset r allowed).card) :
    BoundingSieve.IsLowerMoebius (restrictedLowerMoebius r allowed) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [restrictedLowerMoebius, restrictedLowerMoebiusInt]
  · have hsum := restrictedLowerMoebiusInt_divisor_sum_eq
      (n := n) (r := r) (allowed := allowed) hn0
    have hrestrict := rosserRestrictedAlternatingSum_le_truncated_of_card
      (normalizedFactors n).toFinset r allowed (hpair n)
    rw [rosserTruncated_alternatingSum_eq_oddTruncated] at hrestrict
    have halt := oddTruncatedAlternatingChoose_le_indicator
      (normalizedFactors n).toFinset.card r
    have hfactorZero : (normalizedFactors n).toFinset.card = 0 ↔ n = 1 := by
      rw [Finset.card_eq_zero, Multiset.toFinset_eq_empty,
        normalizedFactors_eq_zero_iff hn0, Nat.isUnit_iff]
    have halt' : oddTruncatedAlternatingChoose
        (normalizedFactors n).toFinset.card r ≤
          if n = 1 then 1 else 0 := by
      simpa only [hfactorZero] using halt
    unfold restrictedLowerMoebius
    exact_mod_cast hsum ▸ hrestrict.trans halt'

end

end Erdos1212Kernel
