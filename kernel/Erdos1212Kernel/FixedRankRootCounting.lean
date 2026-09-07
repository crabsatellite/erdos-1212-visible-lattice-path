import Erdos1212Kernel.ComponentRankConfinement
import Erdos1212Kernel.PrimeCorridorBoundaryAnchor

namespace Erdos1212Kernel

set_option maxHeartbeats 800000

/-!
# Counting bounded corridor roots at fixed exact rank

The deterministic prime--prime boundary anchor of a corridor root lies one
edge outside its safe component.  Fixed-rank confinement therefore places
the root in a fixed box around that anchor.  The anchor map consequently has
uniformly bounded fibres, while its image lies in the set of prime pairs in a
linear-size box.  This gives the decisive extra logarithm.
-/

noncomputable def componentRankAnchorRadius (K : Nat) : Nat :=
  componentRankGap K + 1

noncomputable def fixedRankCorridorThreshold (K : Nat) : Nat :=
  4 * componentRankThreshold K + componentRankAnchorRadius K

theorem primeCorridorBoundaryAnchor_localized
    {N K : Nat} {root : Nat × Nat}
    (hN : fixedRankCorridorThreshold K ≤ N)
    (hroot : root ∈ boundedHighCorridorRootsOfRank N K) :
    let start := primeCorridorPoint root
    let anchor := primeCorridorBoundaryAnchor root
    PrimePair anchor ∧
      anchor.x ≤ start.x + componentRankAnchorRadius K ∧
      start.x ≤ anchor.x + componentRankAnchorRadius K ∧
      anchor.y ≤ start.y + componentRankAnchorRadius K ∧
      start.y ≤ anchor.y + componentRankAnchorRadius K := by
  classical
  have hrootRank :
      root ∈ boundedHighPrimeCorridorRoots N ∧
        exactBoundaryLabelRank (primeCorridorPoint root) = K := by
    simpa [boundedHighCorridorRootsOfRank] using hroot
  have hrootBounded :
      root ∈ highPrimeCorridorRoots N ∧
        ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root) := by
    simpa [boundedHighPrimeCorridorRoots] using hrootRank.1
  have hrootHigh := hrootBounded.1
  have hbounded := hrootBounded.2
  have hrank := hrootRank.2
  have hrootPrime := highPrimeCorridorRoots_subset N hrootHigh
  have hanchorSpec := primeCorridorBoundaryAnchor_spec hrootPrime
  let start := primeCorridorPoint root
  let anchor := primeCorridorBoundaryAnchor root
  obtain ⟨hanchorOutside, predecessor, hpredecessor, hadjacent⟩ :=
    hanchorSpec.1
  have hthresholdN : 4 * componentRankThreshold K ≤ N := by
    dsimp [fixedRankCorridorThreshold] at hN
    omega
  have hstartXLarge : componentRankThreshold K ≤ start.x := by
    rcases root with ⟨p, k⟩
    have hpData := Finset.mem_filter.mp
      (Finset.mem_product.mp hrootHigh).1
    dsimp [start, primeCorridorPoint]
    omega
  have hstartYLarge : componentRankThreshold K ≤ start.y := by
    rcases root with ⟨p, k⟩
    have hkData := Finset.mem_Icc.mp
      (Finset.mem_product.mp hrootHigh).2
    dsimp [start, primeCorridorPoint, highCorridorHeights] at hkData ⊢
    omega
  have hpredecessorBounds :=
    safeComponent_confined_of_exact_rank
      (hbounded := hbounded) hrank hstartXLarge hstartYLarge hpredecessor
  have hanchorXStep := adjacent_x_le_succ hadjacent
  have hpredecessorXStep := adjacent_x_le_succ (adjacent_symm hadjacent)
  have hanchorYStep := adjacent_y_le_succ hadjacent
  have hpredecessorYStep := adjacent_y_le_succ (adjacent_symm hadjacent)
  dsimp [componentRankAnchorRadius]
  exact ⟨hanchorSpec.2, by omega, by omega, by omega, by omega⟩

def coordinateWindow (center radius : Nat) : Finset Nat :=
  Finset.Icc (center - radius) (center + radius)

def pairToLatticePoint (coordinates : Nat × Nat) : LatticePoint :=
  ⟨coordinates.1, coordinates.2⟩

theorem pairToLatticePoint_injective : Function.Injective pairToLatticePoint := by
  intro left right heq
  have hx := congrArg LatticePoint.x heq
  have hy := congrArg LatticePoint.y heq
  exact Prod.ext hx hy

def latticeWindow (center : LatticePoint) (radius : Nat) : Finset LatticePoint :=
  ((coordinateWindow center.x radius) ×ˢ
      (coordinateWindow center.y radius)).image pairToLatticePoint

@[simp] theorem mem_latticeWindow
    {center point : LatticePoint} {radius : Nat} :
    point ∈ latticeWindow center radius ↔
      center.x ≤ point.x + radius ∧
      point.x ≤ center.x + radius ∧
      center.y ≤ point.y + radius ∧
      point.y ≤ center.y + radius := by
  constructor
  · intro hpoint
    obtain ⟨coordinates, hcoordinates, hcoordinatesEq⟩ :=
      Finset.mem_image.mp hpoint
    have hpair := Finset.mem_product.mp hcoordinates
    have hx := Finset.mem_Icc.mp hpair.1
    have hy := Finset.mem_Icc.mp hpair.2
    have hxeq : coordinates.1 = point.x :=
      congrArg LatticePoint.x hcoordinatesEq
    have hyeq : coordinates.2 = point.y :=
      congrArg LatticePoint.y hcoordinatesEq
    omega
  · rintro ⟨hxLower, hxUpper, hyLower, hyUpper⟩
    apply Finset.mem_image.mpr
    refine ⟨(point.x, point.y), ?_, rfl⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> omega

theorem coordinateWindow_card_le (center radius : Nat) :
    (coordinateWindow center radius).card ≤ 2 * radius + 1 := by
  simp [coordinateWindow]
  omega

theorem latticeWindow_card_le (center : LatticePoint) (radius : Nat) :
    (latticeWindow center radius).card ≤ (2 * radius + 1) ^ 2 := by
  rw [latticeWindow, Finset.card_image_of_injective _ pairToLatticePoint_injective]
  rw [Finset.card_product, pow_two]
  exact Nat.mul_le_mul
    (coordinateWindow_card_le center.x radius)
    (coordinateWindow_card_le center.y radius)

def primePairBox (bound : Nat) : Finset LatticePoint :=
  ((Nat.primesLE bound) ×ˢ (Nat.primesLE bound)).image pairToLatticePoint

@[simp] theorem mem_primePairBox {bound : Nat} {point : LatticePoint} :
    point ∈ primePairBox bound ↔
      PrimePair point ∧ point.x ≤ bound ∧ point.y ≤ bound := by
  constructor
  · intro hpoint
    obtain ⟨coordinates, hcoordinates, hcoordinatesEq⟩ :=
      Finset.mem_image.mp hpoint
    have hpair := Finset.mem_product.mp hcoordinates
    have hx := Nat.mem_primesLE.mp hpair.1
    have hy := Nat.mem_primesLE.mp hpair.2
    have hxeq : coordinates.1 = point.x :=
      congrArg LatticePoint.x hcoordinatesEq
    have hyeq : coordinates.2 = point.y :=
      congrArg LatticePoint.y hcoordinatesEq
    have hxPrime : Nat.Prime point.x := by
      rw [← hxeq]
      exact hx.2
    have hyPrime : Nat.Prime point.y := by
      rw [← hyeq]
      exact hy.2
    have hxBound : point.x ≤ bound := by
      rw [← hxeq]
      exact hx.1
    have hyBound : point.y ≤ bound := by
      rw [← hyeq]
      exact hy.1
    exact ⟨⟨hxPrime, hyPrime⟩, hxBound, hyBound⟩
  · rintro ⟨⟨hxPrime, hyPrime⟩, hxBound, hyBound⟩
    apply Finset.mem_image.mpr
    refine ⟨(point.x, point.y), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hxBound, hxPrime⟩,
        Nat.mem_primesLE.mpr ⟨hyBound, hyPrime⟩⟩

theorem primePairBox_card (bound : Nat) :
    (primePairBox bound).card = (Nat.primeCounting bound) ^ 2 := by
  rw [primePairBox, Finset.card_image_of_injective _ pairToLatticePoint_injective]
  simp [pow_two]

noncomputable def fixedRankAnchorImage (N K : Nat) : Finset LatticePoint :=
  (boundedHighCorridorRootsOfRank N K).image primeCorridorBoundaryAnchor

noncomputable def fixedRankAnchorFiber (N K : Nat) (anchor : LatticePoint) :
    Finset (Nat × Nat) :=
  (boundedHighCorridorRootsOfRank N K).filter fun root ↦
    primeCorridorBoundaryAnchor root = anchor

theorem fixedRankAnchorFiber_card_le
    {N K : Nat} (hN : fixedRankCorridorThreshold K ≤ N)
    (anchor : LatticePoint) :
    (fixedRankAnchorFiber N K anchor).card ≤
      (2 * componentRankAnchorRadius K + 1) ^ 2 := by
  rw [← Finset.card_image_of_injective _ primeCorridorPoint_injective]
  calc
    ((fixedRankAnchorFiber N K anchor).image primeCorridorPoint).card
        ≤ (latticeWindow anchor (componentRankAnchorRadius K)).card := by
      apply Finset.card_le_card
      intro start hstart
      obtain ⟨root, hrootFiber, hrootPoint⟩ := Finset.mem_image.mp hstart
      have hrootData :
          root ∈ boundedHighCorridorRootsOfRank N K ∧
            primeCorridorBoundaryAnchor root = anchor := by
        simpa [fixedRankAnchorFiber] using hrootFiber
      have hlocalized := primeCorridorBoundaryAnchor_localized hN hrootData.1
      have hanchorEq := hrootData.2
      rw [← hrootPoint]
      apply mem_latticeWindow.mpr
      dsimp only at hlocalized
      rw [hanchorEq] at hlocalized
      exact ⟨hlocalized.2.1, hlocalized.2.2.1,
        hlocalized.2.2.2.1, hlocalized.2.2.2.2⟩
    _ ≤ (2 * componentRankAnchorRadius K + 1) ^ 2 :=
      latticeWindow_card_le anchor (componentRankAnchorRadius K)

theorem fixedRankAnchorImage_subset_primePairBox
    {N K : Nat} (hN : fixedRankCorridorThreshold K ≤ N) :
    fixedRankAnchorImage N K ⊆ primePairBox (8 * N) := by
  classical
  intro anchor hanchor
  obtain ⟨root, hroot, hrootAnchor⟩ := Finset.mem_image.mp hanchor
  have hrootRank :
      root ∈ boundedHighPrimeCorridorRoots N ∧
        exactBoundaryLabelRank (primeCorridorPoint root) = K := by
    simpa [boundedHighCorridorRootsOfRank] using hroot
  have hrootBounded :
      root ∈ highPrimeCorridorRoots N ∧
        ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root) := by
    simpa [boundedHighPrimeCorridorRoots] using hrootRank.1
  have hrootHigh := hrootBounded.1
  have hlocalized := primeCorridorBoundaryAnchor_localized hN hroot
  have hNRadius : componentRankAnchorRadius K ≤ N := by
    dsimp [fixedRankCorridorThreshold] at hN
    omega
  rcases root with ⟨p, k⟩
  have hpData := Finset.mem_filter.mp (Finset.mem_product.mp hrootHigh).1
  have hkData := Finset.mem_Icc.mp (Finset.mem_product.mp hrootHigh).2
  have hpBound : p ≤ 4 * N :=
    (Nat.mem_primesLE.mp hpData.1).1
  have hkUpper : k ≤ N / 2 := hkData.2
  rw [← hrootAnchor]
  apply mem_primePairBox.mpr
  dsimp only at hlocalized
  dsimp [primeCorridorPoint] at hlocalized
  exact ⟨hlocalized.1, by omega, by omega⟩

theorem boundedHighCorridorRootsOfRank_card_le
    {N K : Nat} (hN : fixedRankCorridorThreshold K ≤ N) :
    (boundedHighCorridorRootsOfRank N K).card ≤
      (Nat.primeCounting (8 * N)) ^ 2 *
        (2 * componentRankAnchorRadius K + 1) ^ 2 := by
  classical
  let roots := boundedHighCorridorRootsOfRank N K
  let anchors := fixedRankAnchorImage N K
  let fibreBound := (2 * componentRankAnchorRadius K + 1) ^ 2
  have himageCard : anchors.card ≤ (primePairBox (8 * N)).card :=
    Finset.card_le_card (fixedRankAnchorImage_subset_primePairBox hN)
  calc
    roots.card =
        ∑ anchor ∈ anchors,
          (fixedRankAnchorFiber N K anchor).card := by
      dsimp [roots, anchors, fixedRankAnchorFiber, fixedRankAnchorImage]
      simpa using
        (Finset.card_eq_sum_card_image
          primeCorridorBoundaryAnchor (boundedHighCorridorRootsOfRank N K))
    _ ≤ ∑ _anchor ∈ anchors, fibreBound := by
      apply Finset.sum_le_sum
      intro anchor _hanchor
      exact fixedRankAnchorFiber_card_le hN anchor
    _ = anchors.card * fibreBound := by simp
    _ ≤ (primePairBox (8 * N)).card * fibreBound :=
      Nat.mul_le_mul_right fibreBound himageCard
    _ = (Nat.primeCounting (8 * N)) ^ 2 *
        (2 * componentRankAnchorRadius K + 1) ^ 2 := by
      rw [primePairBox_card]

end Erdos1212Kernel
