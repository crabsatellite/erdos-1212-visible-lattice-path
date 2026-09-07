import Erdos1212Kernel.ConcreteCorridorRankClosure

namespace Erdos1212Kernel

/-!
# The finite active label set of an actual bounded component

The exact rank records boundary labels above eleven.  For geometric
confinement it is convenient to adjoin the five permanent prime labels at
most eleven.  The resulting set still has cardinality at most `rank + 5`, and
every label in it is prime.  No information about the numerical sizes of the
nonpermanent labels is used.
-/

noncomputable def finiteSafeComponentActiveLabels
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) : Finset Nat :=
  exactNonpermanentBoundaryLabels start hbounded ∪ Nat.primesLE 11

theorem primesLE_eleven_card : (Nat.primesLE 11).card = 5 := by
  decide

theorem exactNonpermanentBoundaryLabel_prime
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {q : Nat}
    (hq : q ∈ exactNonpermanentBoundaryLabels start hbounded) :
    Nat.Prime q := by
  obtain ⟨hqImage, hqLarge⟩ := Finset.mem_filter.mp hq
  obtain ⟨site, _hsite, hsiteLabel⟩ := Finset.mem_image.mp hqImage
  have hgcdNeOne : Nat.gcd site.x site.y ≠ 1 := by
    intro hgcdOne
    have hlabelOne : commonPrimeLabel site = 1 := by
      simp [commonPrimeLabel, hgcdOne]
    omega
  rw [← hsiteLabel]
  exact Nat.minFac_prime hgcdNeOne

theorem finiteSafeComponentActiveLabel_prime
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {q : Nat}
    (hq : q ∈ finiteSafeComponentActiveLabels start hbounded) :
    Nat.Prime q := by
  rcases Finset.mem_union.mp hq with hqExact | hqSmall
  · exact exactNonpermanentBoundaryLabel_prime hqExact
  · exact (Nat.mem_primesLE.mp hqSmall).2

theorem finiteSafeComponentActiveLabels_card_le
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    (finiteSafeComponentActiveLabels start hbounded).card ≤
      (exactNonpermanentBoundaryLabels start hbounded).card + 5 := by
  calc
    (finiteSafeComponentActiveLabels start hbounded).card
        ≤ (exactNonpermanentBoundaryLabels start hbounded).card +
            (Nat.primesLE 11).card := by
      simpa [finiteSafeComponentActiveLabels] using
        (Finset.card_union_le
          (exactNonpermanentBoundaryLabels start hbounded)
          (Nat.primesLE 11))
    _ = (exactNonpermanentBoundaryLabels start hbounded).card + 5 := by
      rw [primesLE_eleven_card]

theorem exactBoundaryLabelRank_eq_card
    {start : LatticePoint}
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    exactBoundaryLabelRank start =
      (exactNonpermanentBoundaryLabels start hbounded).card := by
  simp [exactBoundaryLabelRank, hbounded]

theorem finiteSafeComponentActiveLabels_card_le_rank_add_five
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    (finiteSafeComponentActiveLabels start hbounded).card ≤
      exactBoundaryLabelRank start + 5 := by
  rw [exactBoundaryLabelRank_eq_card hbounded]
  exact finiteSafeComponentActiveLabels_card_le start hbounded

theorem commonPrimeLabel_mem_activeLabels_of_frontier
    {start site : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (hfrontier : site ∈ safeComponentFrontier start)
    (hnotVisible : ¬ Visible site) :
    commonPrimeLabel site ∈ finiteSafeComponentActiveLabels start hbounded := by
  have hprime : Nat.Prime (commonPrimeLabel site) :=
    (commonPrimeLabel_spec_of_not_visible hnotVisible).1
  by_cases hlarge : 11 < commonPrimeLabel site
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlarge⟩
    apply Finset.mem_image.mpr
    exact ⟨site, mem_finiteSafeComponentFrontier.mpr hfrontier, rfl⟩
  · apply Finset.mem_union_right
    apply Nat.mem_primesLE.mpr
    exact ⟨by omega, hprime⟩

end Erdos1212Kernel
