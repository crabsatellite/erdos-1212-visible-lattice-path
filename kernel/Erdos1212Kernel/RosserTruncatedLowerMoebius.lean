import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Erdos1212Kernel.RosserTruncatedAlternating

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega BigOperators
open Finset Nat UniqueFactorizationMonoid

set_option maxHeartbeats 1400000

def truncatedLowerMoebiusInt (r n : Nat) : Int :=
  if ArithmeticFunction.cardFactors n < 2 * r then
    ArithmeticFunction.moebius n
  else 0

def truncatedLowerMoebius (r n : Nat) : Real :=
  truncatedLowerMoebiusInt r n

theorem truncatedLowerMoebiusInt_of_squarefree
    {r n : Nat} (hsquare : Squarefree n) :
    truncatedLowerMoebiusInt r n =
      if ArithmeticFunction.cardFactors n < 2 * r then
        (-1 : Int) ^ ArithmeticFunction.cardFactors n
      else 0 := by
  simp [truncatedLowerMoebiusInt, hsquare]

theorem normalizedFactorSubset_prod_data
    {n : Nat}
    (t : Finset Nat)
    (ht : t ∈ (normalizedFactors n).toFinset.powerset) :
    Squarefree t.val.prod ∧
      ArithmeticFunction.cardFactors t.val.prod = t.card ∧
      ArithmeticFunction.moebius t.val.prod = (-1 : Int) ^ t.card := by
  have hsubset : t ⊆ (normalizedFactors n).toFinset :=
    Finset.mem_powerset.mp ht
  have hirr : ∀ x : Nat, x ∈ t.val → Irreducible x := by
    intro x hx
    apply irreducible_of_normalized_factor x
    apply Multiset.mem_toFinset.mp
    exact hsubset (by simpa using hx)
  have hprod0 : t.val.prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro hzero
    exact not_irreducible_zero (hirr 0 hzero)
  have hfactors : normalizedFactors t.val.prod = t.val :=
    Nat.factors_multiset_prod_of_irreducible hirr
  have hsquare : Squarefree t.val.prod := by
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      hprod0, hfactors]
    exact t.nodup
  have homega : ArithmeticFunction.cardFactors t.val.prod = t.card := by
    rw [ArithmeticFunction.cardFactors_apply, ← Multiset.coe_card,
      ← Nat.factors_eq, hfactors]
    rfl
  exact ⟨hsquare, homega, by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsquare, homega]⟩

theorem normalizedFactorSubset_prod_primeFactors
    {n : Nat}
    (t : Finset Nat)
    (ht : t ∈ (normalizedFactors n).toFinset.powerset) :
    (t.val.prod).primeFactors = t := by
  have hsubset : t ⊆ (normalizedFactors n).toFinset :=
    Finset.mem_powerset.mp ht
  have hirr : ∀ x : Nat, x ∈ t.val → Irreducible x := by
    intro x hx
    apply irreducible_of_normalized_factor x
    apply Multiset.mem_toFinset.mp
    exact hsubset (by simpa using hx)
  have hfactors : normalizedFactors t.val.prod = t.val :=
    Nat.factors_multiset_prod_of_irreducible hirr
  have hlist : (t.val.prod).primeFactorsList = t.val := by
    rw [← Nat.factors_eq]
    exact hfactors
  ext x
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList]
  constructor
  · intro hx
    have hx' : x ∈ ((t.val.prod).primeFactorsList : Multiset Nat) := hx
    have hxt : x ∈ t.val := hlist ▸ hx'
    exact hxt
  · intro hxt
    have hxt' : x ∈ t.val := hxt
    have hx : x ∈ ((t.val.prod).primeFactorsList : Multiset Nat) :=
      hlist.symm ▸ hxt'
    exact hx

theorem truncatedLowerMoebiusInt_subset_prod
    {n r : Nat}
    (t : Finset Nat)
    (ht : t ∈ (normalizedFactors n).toFinset.powerset) :
    truncatedLowerMoebiusInt r t.val.prod =
      if t.card < 2 * r then (-1 : Int) ^ t.card else 0 := by
  obtain ⟨hsquare, homega, hmu⟩ := normalizedFactorSubset_prod_data t ht
  unfold truncatedLowerMoebiusInt
  rw [homega, hmu]

theorem truncatedLowerMoebiusInt_divisor_sum_eq
    {n r : Nat} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, truncatedLowerMoebiusInt r d) =
      oddTruncatedAlternatingChoose
        (normalizedFactors n).toFinset.card r := by
  let factors := (normalizedFactors n).toFinset
  have hfilter :
      (∑ d ∈ n.divisors, truncatedLowerMoebiusInt r d) =
        ∑ d ∈ n.divisors with Squarefree d,
          truncatedLowerMoebiusInt r d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hnotSquare : ¬ Squarefree d := by
      intro hsquare
      exact hnot (Finset.mem_filter.mpr ⟨hd, hsquare⟩)
    simp [truncatedLowerMoebiusInt,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSquare]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hn]
  change
    (∑ t ∈ factors.powerset,
      truncatedLowerMoebiusInt r t.val.prod) = _
  calc
    (∑ t ∈ factors.powerset,
        truncatedLowerMoebiusInt r t.val.prod) =
      ∑ t ∈ factors.powerset,
        (if t.card < 2 * r then (-1 : Int) ^ t.card else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact truncatedLowerMoebiusInt_subset_prod t (by simpa [factors] using ht)
    _ = ∑ k ∈ Finset.range (factors.card + 1),
        factors.card.choose k •
          (if k < 2 * r then (-1 : Int) ^ k else 0) := by
      exact Finset.sum_powerset_apply_card
        (fun k => if k < 2 * r then (-1 : Int) ^ k else 0)
    _ = oddTruncatedAlternatingChoose factors.card r :=
      sum_choose_mul_truncated_eq_oddTruncated factors.card r

theorem truncatedLowerMoebiusInt_isLower (r : Nat) :
    ∀ n : Nat,
      (∑ d ∈ n.divisors, truncatedLowerMoebiusInt r d) ≤
        if n = 1 then 1 else 0 := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [truncatedLowerMoebiusInt]
  · rw [truncatedLowerMoebiusInt_divisor_sum_eq hn0]
    have hbound := oddTruncatedAlternatingChoose_le_indicator
      (normalizedFactors n).toFinset.card r
    by_cases hn1 : n = 1
    · subst n
      simpa using hbound
    · have hfactorsNonempty : (normalizedFactors n).toFinset.card ≠ 0 := by
        rw [Finset.card_ne_zero]
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hnormalized : normalizedFactors n = 0 := by
          rw [← Multiset.toFinset_eq_empty]
          exact hempty
        have hnUnit : IsUnit n :=
          (normalizedFactors_eq_zero_iff hn0).mp hnormalized
        exact hn1 (Nat.isUnit_iff.mp hnUnit)
      simpa [hn1, hfactorsNonempty] using hbound

theorem truncatedLowerMoebius_isLower (r : Nat) :
    BoundingSieve.IsLowerMoebius (truncatedLowerMoebius r) := by
  intro n
  have h := truncatedLowerMoebiusInt_isLower r n
  unfold truncatedLowerMoebius
  exact_mod_cast h

theorem abs_truncatedLowerMoebiusInt_le_one (r n : Nat) :
    |truncatedLowerMoebiusInt r n| ≤ 1 := by
  unfold truncatedLowerMoebiusInt
  split_ifs
  · exact ArithmeticFunction.abs_moebius_le_one
  · simp

theorem abs_truncatedLowerMoebius_le_one (r n : Nat) :
    |truncatedLowerMoebius r n| ≤ 1 := by
  unfold truncatedLowerMoebius
  exact_mod_cast abs_truncatedLowerMoebiusInt_le_one r n

theorem BoundingSieve.truncatedLower_errSum_le
    (s : BoundingSieve) (r : Nat) :
    s.errSum (truncatedLowerMoebius r) ≤
      ∑ d ∈ s.prodPrimes.divisors, |s.rem d| := by
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d _hd
  calc
    |truncatedLowerMoebius r d| * |s.rem d| ≤
        1 * |s.rem d| :=
      mul_le_mul_of_nonneg_right
        (abs_truncatedLowerMoebius_le_one r d) (abs_nonneg _)
    _ = |s.rem d| := one_mul _

theorem BoundingSieve.truncatedLower_main_sub_fullRemainder_le_sifted
    (s : BoundingSieve) (r : Nat) :
    s.totalMass * s.mainSum (truncatedLowerMoebius r) -
        (∑ d ∈ s.prodPrimes.divisors, |s.rem d|) ≤
      s.siftedSum := by
  have hlower := BoundingSieve.lowerMoebius_main_sub_error_le_siftedSum
    (s := s) (truncatedLowerMoebius r) (truncatedLowerMoebius_isLower r)
  have herr := BoundingSieve.truncatedLower_errSum_le s r
  linarith

end

end Erdos1212Kernel
