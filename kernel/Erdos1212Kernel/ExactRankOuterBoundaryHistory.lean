import Erdos1212Kernel.FiniteComponentBoundaryTrace
import Erdos1212Kernel.ActualPromotedExitHistory

namespace Erdos1212Kernel

/-!
# Exact-rank outer contour and its paid first-exit history

For a high corridor root of exact boundary-label rank `K`, the fixed-rank
barriers keep the actual component, and hence its exterior frontier, away
from the coordinate boundary strips.  The canonical wall-follower contour is
therefore made entirely of genuine deleted interior sites: each site is
either prime--prime or nonvisible.

Scanning this unchanged closed contour by the first-exit rule gives one
without-replacement list of actual common-prime labels.  Every recruited
label is a member of the exact nonpermanent boundary-label set, so the number
of new exits is at most the exact rank `K`.  This is the concrete geometric
binding between the canonical outer contour and the terminal promoted
history.
-/

theorem safeComponentFrontier_coordinates_interior_of_exact_rank
    {start point : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y)
    (hfrontier : point ∈ safeComponentFrontier start) :
    1 < point.x ∧ 1 < point.y := by
  obtain ⟨_hpointOutside, inside, hinside, hadjacent⟩ := hfrontier
  have hinsideBounds :=
    safeComponent_confined_of_exact_rank
      (hbounded := hbounded) hrank hxLarge hyLarge hinside
  have hnthTwo : 2 ≤ Nat.nth Nat.Prime (K + 5) :=
    (Nat.prime_nth_prime (K + 5)).two_le
  have hinsideX : 2 < inside.x := by
    dsimp [componentRankThreshold] at hxLarge
    omega
  have hinsideY : 2 < inside.y := by
    dsimp [componentRankThreshold] at hyLarge
    omega
  have hxStep := adjacent_x_le_succ (adjacent_symm hadjacent)
  have hyStep := adjacent_y_le_succ (adjacent_symm hadjacent)
  omega

theorem safeComponentFrontier_primePair_or_not_visible_of_exact_rank
    {start point : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y)
    (hfrontier : point ∈ safeComponentFrontier start) :
    PrimePair point ∨ ¬ Visible point := by
  by_cases hvisible : Visible point
  · left
    have hcoordinates :=
      safeComponentFrontier_coordinates_interior_of_exact_rank
        (hbounded := hbounded) hrank hxLarge hyLarge hfrontier
    exact primePair_of_mem_safeComponentFrontier_of_interiorVisible
      hfrontier ⟨hcoordinates.1, hcoordinates.2, hvisible⟩
  · exact Or.inr hvisible

/-- The canonical closed outer contour of an exact-rank high corridor root
is exhausted by one without-replacement first-exit history.  Its new-label
count is bounded by the literal exact boundary rank. -/
theorem exists_exactRankCanonicalOuterBoundaryHistory
    {N K : Nat} {root : Nat × Nat}
    (hN : 4 * componentRankThreshold K ≤ N)
    (hroot : root ∈ boundedHighCorridorRootsOfRank N K) :
    ∃ (hbounded :
        ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root))
      (hrootCorridor : root ∈ primeCorridorRoots N)
      (period : Nat)
      (anchor : LatticePoint)
      (walk : starLatticeGraph.Walk anchor anchor)
      (labels : List Nat)
      (residualLabels : Finset Nat),
      anchor = primeCorridorOuterBoundaryAnchor hrootCorridor hbounded ∧
      0 < period ∧
      ActualPromotedExitHistory (Nat.primesLE 11) walk.support labels ∧
      labels.Nodup ∧
      labels.length ≤ K ∧
      labels.toFinset ∪ residualLabels =
        exactNonpermanentBoundaryLabels
          (primeCorridorPoint root) hbounded ∧
      Disjoint labels.toFinset residualLabels ∧
      labels.length + residualLabels.card = K ∧
      (K ≤ 2 * labels.length ∨ K ≤ 2 * residualLabels.card) ∧
      (∀ point ∈ walk.support,
        point ∈ safeComponentFrontier (primeCorridorPoint root)) ∧
      (∀ point ∈ walk.support,
        point ∈ latticeWindow (primeCorridorPoint root)
          (componentRankGap K + 1)) ∧
      (∀ point ∈ walk.support,
        ActualPromotedStarReachable
          (promotedExitFinalLabels (Nat.primesLE 11) labels)
          anchor
          point) := by
  classical
  have hrootData :
      root ∈ boundedHighPrimeCorridorRoots N ∧
        exactBoundaryLabelRank (primeCorridorPoint root) = K := by
    simpa [boundedHighCorridorRootsOfRank] using hroot
  have hrootBounded :
      root ∈ highPrimeCorridorRoots N ∧
        ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root) := by
    simpa [boundedHighPrimeCorridorRoots] using hrootData.1
  let hrootHigh := hrootBounded.1
  let hbounded := hrootBounded.2
  let hrootCorridor : root ∈ primeCorridorRoots N :=
    highPrimeCorridorRoots_subset N hrootHigh
  let start := primeCorridorPoint root
  have hstartXLarge : componentRankThreshold K ≤ start.x := by
    rcases root with ⟨p, k⟩
    have hpLower :=
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hrootCorridor).1).2
    dsimp [start, primeCorridorPoint]
    omega
  have hstartYLarge : componentRankThreshold K ≤ start.y := by
    rcases root with ⟨p, k⟩
    have hkMem := (Finset.mem_product.mp hrootHigh).2
    rw [highCorridorHeights] at hkMem
    have hkLower := (Finset.mem_Icc.mp hkMem).1
    dsimp [start, primeCorridorPoint]
    omega
  obtain ⟨period, hperiodPositive, _hperiodBound, walk, hfrontier⟩ :=
    exists_primeCorridorCanonicalOuterBoundaryWalk
      hrootCorridor hbounded
  have hdeleted : ∀ point ∈ walk.support,
      PrimePair point ∨ ¬ Visible point := by
    intro point hpoint
    exact safeComponentFrontier_primePair_or_not_visible_of_exact_rank
      (hbounded := hbounded) hrootData.2 hstartXLarge hstartYLarge
      (hfrontier point hpoint)
  obtain ⟨labels, hhistory, hnodup, hlabelsPrime, hreachable⟩ :=
    exists_withoutReplacement_actualPromotedTraceHistory
      (R := Nat.primesLE 11) walk hdeleted
  have hlabelsSubset : labels.toFinset ⊆
      exactNonpermanentBoundaryLabels start hbounded := by
    intro q hq
    have hqList : q ∈ labels := List.mem_toFinset.mp hq
    obtain ⟨point, hpoint, _hnotAnchor, hnotVisible, hlabel⟩ :=
      hhistory.labels_witnessed q hqList
    have hpointFrontier := hfrontier point hpoint
    have hpointFinite :
        point ∈ finiteSafeComponentFrontier start hbounded :=
      mem_finiteSafeComponentFrontier.mpr (by
        simpa [start] using hpointFrontier)
    have hqPrime : Nat.Prime q := hlabelsPrime q hqList
    have hqFresh : q ∉ Nat.primesLE 11 :=
      hhistory.labels_fresh_from_initial q hqList
    have hqLarge : 11 < q := by
      by_contra hnotLarge
      exact hqFresh (Nat.mem_primesLE.mpr ⟨by omega, hqPrime⟩)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr
      ⟨point, hpointFinite, hlabel.symm⟩, hqLarge⟩
  have hrankCard :
      (exactNonpermanentBoundaryLabels start hbounded).card = K := by
    simpa [start, exactBoundaryLabelRank, hbounded] using hrootData.2
  have hlabelCard : labels.toFinset.card ≤ K := by
    rw [← hrankCard]
    exact Finset.card_le_card hlabelsSubset
  have hlengthEq : labels.toFinset.card = labels.length := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hnodup]
  have hlength : labels.length ≤ K := by omega
  let residualLabels :=
    exactNonpermanentBoundaryLabels start hbounded \ labels.toFinset
  have hlabelUnion : labels.toFinset ∪ residualLabels =
      exactNonpermanentBoundaryLabels
        (primeCorridorPoint root) hbounded := by
    simpa [residualLabels, start] using
      (Finset.union_sdiff_of_subset hlabelsSubset)
  have hlabelDisjoint : Disjoint labels.toFinset residualLabels := by
    exact Finset.disjoint_sdiff
  have hresidualCard : labels.length + residualLabels.card = K := by
    have hcard := Finset.card_sdiff_add_card_eq_card hlabelsSubset
    change residualLabels.card + labels.toFinset.card =
      (exactNonpermanentBoundaryLabels start hbounded).card at hcard
    rw [List.toFinset_card_of_nodup hnodup, hrankCard] at hcard
    omega
  have hrankDichotomy :
      K ≤ 2 * labels.length ∨ K ≤ 2 * residualLabels.card := by
    omega
  have hcomponentConfined :
      SafeComponentConfinedWithin start (componentRankGap K) := by
    intro finish hfinish
    exact safeComponent_confined_of_exact_rank
      (hbounded := hbounded) hrootData.2 hstartXLarge hstartYLarge hfinish
  have hwindow : ∀ point ∈ walk.support,
      point ∈ latticeWindow (primeCorridorPoint root)
        (componentRankGap K + 1) := by
    intro point hpoint
    have hpointWindow := frontier_mem_latticeWindow_of_component_confined
      hcomponentConfined (hfrontier point hpoint)
    simpa [start] using hpointWindow
  exact ⟨hbounded, hrootCorridor, period,
    primeCorridorOuterBoundaryAnchor hrootCorridor hbounded,
    walk, labels, residualLabels, rfl, hperiodPositive,
    hhistory, hnodup, hlength, hlabelUnion, hlabelDisjoint,
    hresidualCard, hrankDichotomy, hfrontier, hwindow, hreachable⟩

end Erdos1212Kernel
