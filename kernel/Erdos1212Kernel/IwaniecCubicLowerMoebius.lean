import Erdos1212Kernel.IwaniecOrderedFactors

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega BigOperators
open Finset Nat UniqueFactorizationMonoid

set_option maxHeartbeats 1400000

/-- Polynomial form of Iwaniec's literal cutoff
`p_(2i) < (y / (p_1 ... p_(2i-1)))^(1/3)`.  All quantities are positive
natural numbers in the later prime-factor consumer, so cross multiplication
gives exactly the strict cubic prefix condition below. -/
def iwaniecCubicEvenRestriction
    (y : Nat) (selected : List Nat) (factor : Nat) : Bool :=
  decide (factor ^ 3 * selected.prod < y)

/-- Iwaniec's lower Rosser coefficient, with squarefree support and the exact
decreasing prime-factor order from equation `(2.6)`. -/
def iwaniecCubicLowerMoebiusInt (r y n : Nat) : Int :=
  if Squarefree n then
    iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
      (iwaniecDescendingFactors n.primeFactors)
  else
    0

def iwaniecCubicLowerMoebius (r y n : Nat) : Real :=
  iwaniecCubicLowerMoebiusInt r y n

theorem abs_iwaniecLowerContinuationTerm_le_one
    {α : Type*} (r : Nat) (evenRestriction : List α → α → Bool)
    (selected extension : List α) :
    |iwaniecLowerContinuationTerm r evenRestriction selected extension| ≤ 1 := by
  induction extension generalizing selected with
  | nil => simp [iwaniecLowerContinuationTerm]
  | cons factor extension ih =>
      rw [iwaniecLowerContinuationTerm]
      split_ifs
      · simpa using ih (selected ++ [factor])
      · simp

theorem abs_iwaniecCubicLowerMoebiusInt_le_one (r y n : Nat) :
    |iwaniecCubicLowerMoebiusInt r y n| ≤ 1 := by
  unfold iwaniecCubicLowerMoebiusInt
  split_ifs
  · exact abs_iwaniecLowerContinuationTerm_le_one _ _ _ _
  · simp

theorem abs_iwaniecCubicLowerMoebius_le_one (r y n : Nat) :
    |iwaniecCubicLowerMoebius r y n| ≤ 1 := by
  unfold iwaniecCubicLowerMoebius
  exact_mod_cast abs_iwaniecCubicLowerMoebiusInt_le_one r y n

theorem iwaniecCubicLowerMoebiusInt_subset_prod
    {n r y : Nat} (subset : Finset Nat)
    (hsubset : subset ∈ (normalizedFactors n).toFinset.powerset) :
    iwaniecCubicLowerMoebiusInt r y subset.val.prod =
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors subset) := by
  obtain ⟨hsquare, _homega, _hmu⟩ :=
    normalizedFactorSubset_prod_data subset hsubset
  have hpf := normalizedFactorSubset_prod_primeFactors subset hsubset
  unfold iwaniecCubicLowerMoebiusInt
  rw [if_pos hsquare, hpf]

theorem sum_iwaniecOrderedFactorSublists_eq_expansion
    (r y : Nat) (factors : Finset Nat) :
    (∑ ordered ∈ iwaniecOrderedFactorSublists factors,
        iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
          ordered) =
      iwaniecLowerExpansionSum r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors factors) := by
  rfl

theorem iwaniecCubicLowerMoebiusInt_divisor_sum_eq
    {n r y : Nat} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, iwaniecCubicLowerMoebiusInt r y d) =
      iwaniecLowerExpansionSum r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors (normalizedFactors n).toFinset) := by
  let factors := (normalizedFactors n).toFinset
  have hfilter :
      (∑ d ∈ n.divisors, iwaniecCubicLowerMoebiusInt r y d) =
        ∑ d ∈ n.divisors with Squarefree d,
          iwaniecCubicLowerMoebiusInt r y d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnotSquare : ¬Squarefree d := fun hsquare =>
      hnot (Finset.mem_filter.mpr ⟨hd, hsquare⟩)
    simp [iwaniecCubicLowerMoebiusInt, hnotSquare]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hn]
  change (∑ subset ∈ factors.powerset,
      iwaniecCubicLowerMoebiusInt r y subset.val.prod) = _
  calc
    _ = ∑ subset ∈ factors.powerset,
        iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
          (iwaniecDescendingFactors subset) := by
      apply Finset.sum_congr rfl
      intro subset hsubset
      exact iwaniecCubicLowerMoebiusInt_subset_prod subset
        (by simpa [factors] using hsubset)
    _ = ∑ ordered ∈ iwaniecOrderedFactorSublists factors,
        iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
          ordered :=
      sum_powerset_iwaniecDescendingFactors factors _
    _ = _ := by
      simpa [factors] using
        sum_iwaniecOrderedFactorSublists_eq_expansion r y factors

theorem iwaniecCubicLowerMoebiusInt_isLower
    (r y : Nat) (hr : 0 < r) (n : Nat) :
    (∑ d ∈ n.divisors, iwaniecCubicLowerMoebiusInt r y d) ≤
      if n = 1 then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [iwaniecCubicLowerMoebiusInt]
  · rw [iwaniecCubicLowerMoebiusInt_divisor_sum_eq hn0]
    by_cases hn1 : n = 1
    · subst n
      simp [iwaniecLowerExpansionSum, iwaniecDescendingFactors,
        iwaniecLowerContinuationTerm]
    · rw [if_neg hn1]
      apply iwaniecLowerExpansionSum_root_nonpos r hr
      have hfactorZero :
          (normalizedFactors n).toFinset.card = 0 ↔ n = 1 := by
        rw [Finset.card_eq_zero, Multiset.toFinset_eq_empty,
          normalizedFactors_eq_zero_iff hn0, Nat.isUnit_iff]
      have hcard : (normalizedFactors n).toFinset.card ≠ 0 := fun hzero =>
        hn1 (hfactorZero.mp hzero)
      intro hlist
      have hlength := congrArg List.length hlist
      have : (normalizedFactors n).toFinset.card = 0 := by
        simpa [iwaniecDescendingFactors] using hlength
      exact hcard this

theorem iwaniecCubicLowerMoebius_isLower
    (r y : Nat) (hr : 0 < r) :
    BoundingSieve.IsLowerMoebius (iwaniecCubicLowerMoebius r y) := by
  intro n
  have h := iwaniecCubicLowerMoebiusInt_isLower r y hr n
  unfold iwaniecCubicLowerMoebius
  exact_mod_cast h

end

end Erdos1212Kernel
