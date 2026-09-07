import Erdos1212Kernel.RosserTruncatedLowerMoebius

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

variable {α : Type*} [DecidableEq α]

def rosserTruncatedSubsets (factors : Finset α) (r : Nat) : Finset (Finset α) :=
  factors.powerset.filter fun subset => subset.card < 2 * r

def rosserAllowedSubsets
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    Finset (Finset α) :=
  (rosserTruncatedSubsets factors r).filter fun subset => allowed subset

def rosserRemovedSubsets
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    Finset (Finset α) :=
  (rosserTruncatedSubsets factors r).filter fun subset => !allowed subset

def rosserRemovedEven
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    Finset (Finset α) :=
  (rosserRemovedSubsets factors r allowed).filter fun subset => Even subset.card

def rosserRemovedOdd
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    Finset (Finset α) :=
  (rosserRemovedSubsets factors r allowed).filter fun subset => Odd subset.card

def rosserRestrictedAlternatingSum
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) : Int :=
  ∑ subset ∈ rosserAllowedSubsets factors r allowed,
    (-1 : Int) ^ subset.card

omit [DecidableEq α] in
theorem rosserTruncated_alternatingSum_eq_oddTruncated
    (factors : Finset α) (r : Nat) :
    (∑ subset ∈ rosserTruncatedSubsets factors r,
        (-1 : Int) ^ subset.card) =
      oddTruncatedAlternatingChoose factors.card r := by
  unfold rosserTruncatedSubsets
  rw [Finset.sum_filter]
  calc
    (∑ subset ∈ factors.powerset,
        if subset.card < 2 * r then (-1 : Int) ^ subset.card else 0) =
      ∑ k ∈ Finset.range (factors.card + 1),
        factors.card.choose k •
          (if k < 2 * r then (-1 : Int) ^ k else 0) := by
      exact Finset.sum_powerset_apply_card
        (fun k => if k < 2 * r then (-1 : Int) ^ k else 0)
    _ = oddTruncatedAlternatingChoose factors.card r :=
      sum_choose_mul_truncated_eq_oddTruncated factors.card r

theorem rosserRemoved_even_union_odd
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    rosserRemovedEven factors r allowed ∪ rosserRemovedOdd factors r allowed =
      rosserRemovedSubsets factors r allowed := by
  ext subset
  constructor
  · intro h
    rcases Finset.mem_union.mp h with heven | hodd
    · exact (Finset.mem_filter.mp heven).1
    · exact (Finset.mem_filter.mp hodd).1
  · intro h
    rcases Nat.even_or_odd subset.card with heven | hodd
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, heven⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hodd⟩)

omit [DecidableEq α] in
theorem rosserRemoved_even_disjoint_odd
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    Disjoint (rosserRemovedEven factors r allowed)
      (rosserRemovedOdd factors r allowed) := by
  rw [Finset.disjoint_left]
  intro subset heven hodd
  have he := (Finset.mem_filter.mp heven).2
  have ho := (Finset.mem_filter.mp hodd).2
  exact (Nat.not_even_iff_odd.mpr ho) he

theorem rosserRemoved_alternatingSum_eq_card_sub
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    (∑ subset ∈ rosserRemovedSubsets factors r allowed,
        (-1 : Int) ^ subset.card) =
      (rosserRemovedEven factors r allowed).card -
        (rosserRemovedOdd factors r allowed).card := by
  rw [← rosserRemoved_even_union_odd factors r allowed,
    Finset.sum_union (rosserRemoved_even_disjoint_odd factors r allowed)]
  have heven :
      (∑ subset ∈ rosserRemovedEven factors r allowed,
          (-1 : Int) ^ subset.card) =
        (rosserRemovedEven factors r allowed).card := by
    calc
      _ = ∑ _subset ∈ rosserRemovedEven factors r allowed, (1 : Int) := by
        apply Finset.sum_congr rfl
        intro subset hsubset
        exact ((Finset.mem_filter.mp hsubset).2.neg_one_pow)
      _ = _ := by simp
  have hodd :
      (∑ subset ∈ rosserRemovedOdd factors r allowed,
          (-1 : Int) ^ subset.card) =
        -(rosserRemovedOdd factors r allowed).card := by
    calc
      _ = ∑ _subset ∈ rosserRemovedOdd factors r allowed, (-1 : Int) := by
        apply Finset.sum_congr rfl
        intro subset hsubset
        exact ((Finset.mem_filter.mp hsubset).2.neg_one_pow)
      _ = _ := by simp
  rw [heven, hodd]
  rw [sub_eq_add_neg]

omit [DecidableEq α] in
theorem rosserTruncated_alternatingSum_eq_allowed_add_removed
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool) :
    (∑ subset ∈ rosserTruncatedSubsets factors r,
        (-1 : Int) ^ subset.card) =
      rosserRestrictedAlternatingSum factors r allowed +
        ∑ subset ∈ rosserRemovedSubsets factors r allowed,
          (-1 : Int) ^ subset.card := by
  unfold rosserRestrictedAlternatingSum rosserAllowedSubsets
    rosserRemovedSubsets
  simpa using (Finset.sum_filter_add_sum_filter_not
    (s := rosserTruncatedSubsets factors r)
    (p := fun subset => allowed subset)
    (f := fun subset => (-1 : Int) ^ subset.card)).symm

/-- Generic sign-pairing consumer for Iwaniec restrictions.  Constructing an
injection from removed odd nodes to removed even nodes is enough to retain the
lower Bonferroni direction. -/
theorem rosserRestrictedAlternatingSum_le_truncated_of_card
    (factors : Finset α) (r : Nat) (allowed : Finset α → Bool)
    (hpair : (rosserRemovedOdd factors r allowed).card ≤
      (rosserRemovedEven factors r allowed).card) :
    rosserRestrictedAlternatingSum factors r allowed ≤
      ∑ subset ∈ rosserTruncatedSubsets factors r,
        (-1 : Int) ^ subset.card := by
  have hsplit := rosserTruncated_alternatingSum_eq_allowed_add_removed
    factors r allowed
  have hremoved := rosserRemoved_alternatingSum_eq_card_sub
    factors r allowed
  rw [hremoved] at hsplit
  have hpairInt :
      ((rosserRemovedOdd factors r allowed).card : Int) ≤
        (rosserRemovedEven factors r allowed).card := by
    exact_mod_cast hpair
  omega

end

end Erdos1212Kernel
