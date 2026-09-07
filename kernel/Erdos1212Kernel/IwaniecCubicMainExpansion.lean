import Erdos1212Kernel.IwaniecWeightedLowerTree
import Erdos1212Kernel.VaughanIntervalLowerSieve

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators
open Finset Nat UniqueFactorizationMonoid

set_option maxHeartbeats 1600000

def iwaniecReciprocalFactorWeight (factor : Nat) : Real :=
  (factor : Real)⁻¹

theorem iwaniecWeightedContinuationTerm_reciprocal_eq
    (r y : Nat) (selected extension : List Nat)
    (hnonzero : ∀ factor ∈ extension, factor ≠ 0) :
    iwaniecWeightedContinuationTerm r (iwaniecCubicEvenRestriction y)
        iwaniecReciprocalFactorWeight selected extension =
      (iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y)
          selected extension : Int) * (extension.prod : Real)⁻¹ := by
  induction extension generalizing selected with
  | nil =>
      simp [iwaniecWeightedContinuationTerm,
        iwaniecLowerContinuationTerm]
  | cons factor extension ih =>
      have hfactor := hnonzero factor (by simp)
      have htail : ∀ next ∈ extension, next ≠ 0 := by
        intro next hnext
        exact hnonzero next (by simp [hnext])
      rw [iwaniecWeightedContinuationTerm,
        iwaniecLowerContinuationTerm]
      by_cases hselect :
          selected.length + 1 < 2 * r ∧
            (Even selected.length ∨
              iwaniecCubicEvenRestriction y selected factor)
      · rw [if_pos hselect, if_pos hselect, ih _ htail]
        simp only [Int.cast_neg, Int.cast_mul, List.prod_cons,
          Nat.cast_mul, iwaniecReciprocalFactorWeight]
        rw [mul_inv_rev]
        ring
      · rw [if_neg hselect, if_neg hselect]
        simp

def iwaniecCubicWeightedMainExpansion
    (r y : Nat) (factors : Finset Nat) : Real :=
  iwaniecWeightedExpansionSum r (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight [] (iwaniecDescendingFactors factors)

theorem sum_iwaniecOrderedFactorSublists_eq_weightedExpansion
    (r y : Nat) (factors : Finset Nat) :
    (∑ ordered ∈ iwaniecOrderedFactorSublists factors,
        iwaniecWeightedContinuationTerm r
          (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [] ordered) =
      iwaniecCubicWeightedMainExpansion r y factors := by
  rfl

theorem product_normalizedFactors_toFinset
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (normalizedFactors (∏ q ∈ Q, q)).toFinset = Q := by
  rw [Nat.factors_eq]
  exact Nat.primeFactors_prod hprime

theorem vaughanIntervalSieve_iwaniecCubic_mainSum_eq_expansion
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).mainSum
        (iwaniecCubicLowerMoebius r y) =
      iwaniecCubicWeightedMainExpansion r y Q := by
  let product := ∏ q ∈ Q, q
  let factors := (normalizedFactors product).toFinset
  have hsquare := primeFinsetProduct_squarefree Q hprime
  have hproduct : product ≠ 0 := hsquare.ne_zero
  have hfactors : factors = Q := by
    simpa [factors, product] using
      product_normalizedFactors_toFinset Q hprime
  have hfilter :
      (∑ d ∈ product.divisors,
          iwaniecCubicLowerMoebius r y d * vaughanIntervalNu d) =
        ∑ d ∈ product.divisors with Squarefree d,
          iwaniecCubicLowerMoebius r y d * vaughanIntervalNu d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hdDvd := (Nat.mem_divisors.mp hd).1
    exact (hnot (Finset.mem_filter.mpr
      ⟨hd, Squarefree.squarefree_of_dvd hdDvd hsquare⟩)).elim
  unfold BoundingSieve.mainSum
  change (∑ d ∈ product.divisors,
      iwaniecCubicLowerMoebius r y d * vaughanIntervalNu d) = _
  rw [hfilter, Nat.sum_divisors_filter_squarefree hproduct]
  change (∑ subset ∈ factors.powerset,
      iwaniecCubicLowerMoebius r y subset.val.prod *
        vaughanIntervalNu subset.val.prod) = _
  calc
    _ = ∑ subset ∈ factors.powerset,
        iwaniecWeightedContinuationTerm r
          (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight []
          (iwaniecDescendingFactors subset) := by
      apply Finset.sum_congr rfl
      intro subset hsubset
      have hsubsetQ : subset ⊆ Q := by
        have := Finset.mem_powerset.mp hsubset
        simpa [hfactors] using this
      have hsubsetPrime : ∀ p ∈ subset, Nat.Prime p := by
        intro p hp
        exact hprime p (hsubsetQ hp)
      have hsubsetSquare := primeFinsetProduct_squarefree subset hsubsetPrime
      have hsubsetProduct : subset.val.prod ≠ 0 := by
        rw [Finset.prod_val]
        exact hsubsetSquare.ne_zero
      have hcoefficient := iwaniecCubicLowerMoebiusInt_subset_prod
        (n := product) (r := r) (y := y) subset
        (by simpa [factors, product] using hsubset)
      have hweighted := iwaniecWeightedContinuationTerm_reciprocal_eq
        r y [] (iwaniecDescendingFactors subset) (by
          intro p hp
          have hpMem : p ∈ subset := by
            simpa [iwaniecDescendingFactors] using hp
          exact (hsubsetPrime p hpMem).ne_zero)
      unfold iwaniecCubicLowerMoebius
      rw [hcoefficient,
        vaughanIntervalNu_apply_of_ne_zero hsubsetProduct]
      rw [hweighted]
      rw [iwaniecDescendingFactors_prod]
      rw [Finset.prod_val]
      congr 3
    _ = ∑ ordered ∈ iwaniecOrderedFactorSublists factors,
        iwaniecWeightedContinuationTerm r
          (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [] ordered :=
      sum_powerset_iwaniecDescendingFactors factors _
    _ = _ := by
      rw [hfactors]
      exact sum_iwaniecOrderedFactorSublists_eq_weightedExpansion r y Q

theorem vaughanIntervalSieve_iwaniecCubic_mainSum_eq_tree
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).mainSum
        (iwaniecCubicLowerMoebius r y) =
      iwaniecWeightedLowerTreeSum r (iwaniecCubicEvenRestriction y)
        iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors Q) := by
  rw [vaughanIntervalSieve_iwaniecCubic_mainSum_eq_expansion]
  exact iwaniecWeightedExpansionSum_eq_tree _ _ _ _ _

end

end Erdos1212Kernel
