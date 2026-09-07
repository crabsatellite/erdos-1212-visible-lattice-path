import Erdos1212Kernel.ActualRankBarrierRecruitment

namespace Erdos1212Kernel

/-!
# A certified outer-boundary prime anchor

The first descending prime on a corridor column is an actual deleted vertex,
but an arbitrary deleted vertex can lie on the boundary of a hole.  The
terminal paid history needs an anchor on the unbounded exterior boundary.

For a bounded safe component, take the lowest component vertex on the root's
prime column and step once downward.  The whole vertical ray below that site
is disjoint from the component, so the site is exposed to the exterior.  Its
successor is safe.  Since height two on a prime column is prime--prime, the
exposed site still has height at least two; it is visible below the prime
column height and hence is itself an actual prime--prime vertex.
-/

/-- Exact data retained at the lower outer-boundary anchor of a corridor
root.  The lower-ray certificate is the property that excludes a hole
boundary. -/
structure PrimeCorridorOuterBoundaryAnchorData (root : Nat × Nat) where
  anchor : LatticePoint
  sameColumn : anchor.x = root.1
  aboveBoundary : 1 < anchor.y
  belowRoot : anchor.y < (primeCorridorPoint root).y
  successorInside :
    verticalLinePoint root.1 (anchor.y + 1) ∈
      safeComponent (primeCorridorPoint root)
  frontier :
    anchor ∈ safeComponentFrontier (primeCorridorPoint root)
  lowerRayOutside :
    ∀ z, z ≤ anchor.y →
      verticalLinePoint root.1 z ∉ safeComponent (primeCorridorPoint root)
  primePair : PrimePair anchor

theorem primeCorridorPoint_mem_safeComponent
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N) :
    primeCorridorPoint root ∈ safeComponent (primeCorridorPoint root) := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro point hpoint
  have hpointEq : point = primeCorridorPoint root := by
    simpa using hpoint
  simpa [hpointEq] using primeCorridorPoint_safe hroot

/-- Every bounded corridor root has an actual prime--prime anchor certified
to lie on the lower exterior boundary, not on an internal hole. -/
theorem exists_primeCorridorOuterBoundaryAnchorData
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    Nonempty (PrimeCorridorOuterBoundaryAnchorData root) := by
  classical
  rcases root with ⟨p, k⟩
  have hrootInside :
      verticalLinePoint p (2 * k) ∈
        safeComponent (primeCorridorPoint (p, k)) := by
    simpa [primeCorridorPoint, verticalLinePoint] using
      (primeCorridorPoint_mem_safeComponent hroot)
  obtain ⟨height, hheightLe, hsuccessorInside, hfrontier,
      hlowerRayOutside⟩ :=
    exists_verticalLine_outer_frontier_below_of_component_meets
      (hbounded := hbounded) hrootInside
  have hp : Nat.Prime p :=
    (Nat.mem_primesLE.mp
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hroot).1).1).2
  have hk : 2 ≤ k :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp hroot).2).1
  have hkp : 2 * k < p := by
    have hpLower :=
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hroot).1).2
    have hkUpper :=
      (Finset.mem_Icc.mp (Finset.mem_product.mp hroot).2).2
    omega
  have hheightLt : height < 2 * k := by
    by_contra hnotLt
    have hheightEq : height = 2 * k := by omega
    exact hfrontier.1 (by
      simpa [hheightEq] using hrootInside)
  have hheightPositive : 0 < height := by
    have hsafe := safePoint_of_mem_safeComponent hsuccessorInside
    have : 1 < height + 1 := by
      simpa [verticalLinePoint] using hsafe.2.1
    omega
  have hheightNeOne : height ≠ 1 := by
    intro hheightOne
    have hpair : PrimePair (verticalLinePoint p (height + 1)) := by
      constructor
      · simpa [verticalLinePoint] using hp
      · simpa [verticalLinePoint, hheightOne] using Nat.prime_two
    exact primePair_not_mem_safeComponent hpair hsuccessorInside
  have hheightInterior : 1 < height := by omega
  have hvisible : InteriorVisible (verticalLinePoint p height) := by
    refine ⟨hp.one_lt, hheightInterior, ?_⟩
    simpa [verticalLinePoint, primeColumnPoint] using
      (primeColumnPoint_visible hp (by omega) (by omega : height < p))
  have hprimePair : PrimePair (verticalLinePoint p height) :=
    primePair_of_mem_safeComponentFrontier_of_interiorVisible
      hfrontier hvisible
  refine ⟨{
    anchor := verticalLinePoint p height
    sameColumn := rfl
    aboveBoundary := by simpa [verticalLinePoint]
    belowRoot := by simpa [verticalLinePoint, primeCorridorPoint]
    successorInside := by simpa [verticalLinePoint]
    frontier := hfrontier
    lowerRayOutside := by simpa [verticalLinePoint]
    primePair := hprimePair
  }⟩

/-- A canonical choice of the certified outer-boundary data. -/
noncomputable def primeCorridorOuterBoundaryAnchorData
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    PrimeCorridorOuterBoundaryAnchorData root :=
  Classical.choice
    (exists_primeCorridorOuterBoundaryAnchorData hroot hbounded)

/-- The actual prime--prime site carried by the canonical outer certificate. -/
noncomputable def primeCorridorOuterBoundaryAnchor
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    LatticePoint :=
  (primeCorridorOuterBoundaryAnchorData hroot hbounded).anchor

theorem primeCorridorOuterBoundaryAnchor_spec
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    let anchor := primeCorridorOuterBoundaryAnchor hroot hbounded
    anchor.x = root.1 ∧
      1 < anchor.y ∧
      anchor.y < (primeCorridorPoint root).y ∧
      verticalLinePoint root.1 (anchor.y + 1) ∈
        safeComponent (primeCorridorPoint root) ∧
      anchor ∈ safeComponentFrontier (primeCorridorPoint root) ∧
      (∀ z, z ≤ anchor.y →
        verticalLinePoint root.1 z ∉
          safeComponent (primeCorridorPoint root)) ∧
      PrimePair anchor := by
  dsimp [primeCorridorOuterBoundaryAnchor]
  let data := primeCorridorOuterBoundaryAnchorData hroot hbounded
  exact ⟨data.sameColumn, data.aboveBoundary, data.belowRoot,
    data.successorInside, data.frontier, data.lowerRayOutside,
    data.primePair⟩

end Erdos1212Kernel
