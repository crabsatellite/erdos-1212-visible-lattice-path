import Mathlib.Data.Fintype.Pigeonhole
import Erdos1212Kernel.PrimeCorridorOuterBoundaryAnchor
import Erdos1212Kernel.ActualPromotedComponentConfinement

namespace Erdos1212Kernel

/-!
# Canonical wall following on the actual finite safe component

The exterior vertex frontier need not be star-connected when the component
has holes.  We therefore work with oriented boundary darts of the finite
polyomino formed by the actual safe component.  A dart consists of an inside
cell and one outward grid direction whose neighbouring cell is outside.

The successor below is the usual left-hand wall follower.  At the terminal
corner of a side it first takes a concave turn when the forward diagonal cell
is occupied, otherwise continues straight when the forward side cell is
occupied, and otherwise takes the convex turn around the current cell.  This
uses the actual finite component and introduces no contour surrogate.
-/

def gridDirectionCCW : GridDirection → GridDirection
  | .east => .north
  | .north => .west
  | .west => .south
  | .south => .east

def gridDirectionCW : GridDirection → GridDirection
  | .east => .south
  | .south => .west
  | .west => .north
  | .north => .east

def gridDirectionOpposite : GridDirection → GridDirection
  | .east => .west
  | .west => .east
  | .north => .south
  | .south => .north

@[simp] theorem gridDirectionCW_ccw (direction : GridDirection) :
    gridDirectionCW (gridDirectionCCW direction) = direction := by
  cases direction <;> rfl

@[simp] theorem gridDirectionCCW_cw (direction : GridDirection) :
    gridDirectionCCW (gridDirectionCW direction) = direction := by
  cases direction <;> rfl

@[simp] theorem gridDirectionOpposite_ccw (direction : GridDirection) :
    gridDirectionOpposite (gridDirectionCCW direction) =
      gridDirectionCW direction := by
  cases direction <;> rfl

/-- The literal boundary darts of the finite safe component. -/
noncomputable def finiteSafeBoundaryDarts
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    Finset (LatticePoint × GridDirection) :=
  ((finiteSafeComponent start hbounded) ×ˢ
      (Finset.univ : Finset GridDirection)).filter fun dart ↦
    gridStep dart.1 dart.2 ∉ finiteSafeComponent start hbounded

@[simp] theorem mem_finiteSafeBoundaryDarts
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {dart : LatticePoint × GridDirection} :
    dart ∈ finiteSafeBoundaryDarts start hbounded ↔
      dart.1 ∈ safeComponent start ∧
      gridStep dart.1 dart.2 ∉ safeComponent start := by
  classical
  simp [finiteSafeBoundaryDarts]

/-- Forward side cell at the terminal corner of a dart. -/
def boundaryForwardSide (dart : LatticePoint × GridDirection) :
    LatticePoint :=
  gridStep dart.1 (gridDirectionCCW dart.2)

/-- Forward diagonal cell at the terminal corner of a dart. -/
def boundaryForwardDiagonal (dart : LatticePoint × GridDirection) :
    LatticePoint :=
  gridStep (gridStep dart.1 dart.2) (gridDirectionCCW dart.2)

/-- Raw left-hand wall-follower transition relative to a finite cell set. -/
def boundaryDartSuccessorRaw
    (component : Finset LatticePoint)
    (dart : LatticePoint × GridDirection) :
    LatticePoint × GridDirection :=
  if boundaryForwardDiagonal dart ∈ component then
    (boundaryForwardDiagonal dart, gridDirectionCW dart.2)
  else if boundaryForwardSide dart ∈ component then
    (boundaryForwardSide dart, dart.2)
  else
    (dart.1, gridDirectionCCW dart.2)

/-- Backward side cell at the initial corner of a dart. -/
def boundaryBackwardSide (dart : LatticePoint × GridDirection) :
    LatticePoint :=
  gridStep dart.1 (gridDirectionCW dart.2)

/-- Backward diagonal cell at the initial corner of a dart. -/
def boundaryBackwardDiagonal (dart : LatticePoint × GridDirection) :
    LatticePoint :=
  gridStep (gridStep dart.1 dart.2) (gridDirectionCW dart.2)

/-- Reverse wall-follower transition. -/
def boundaryDartPredecessorRaw
    (component : Finset LatticePoint)
    (dart : LatticePoint × GridDirection) :
    LatticePoint × GridDirection :=
  if boundaryBackwardDiagonal dart ∈ component then
    (boundaryBackwardDiagonal dart, gridDirectionCCW dart.2)
  else if boundaryBackwardSide dart ∈ component then
    (boundaryBackwardSide dart, dart.2)
  else
    (dart.1, gridDirectionCW dart.2)

theorem boundaryForwardDiagonal_step_cw
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    gridStep
        (boundaryForwardDiagonal (cell, direction))
        (gridDirectionCW direction) =
      gridStep cell direction := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryForwardDiagonal, gridDirectionCCW,
      gridDirectionCW, gridStep] <;> omega

theorem boundaryForwardSide_step_outward
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    gridStep (boundaryForwardSide (cell, direction)) direction =
      boundaryForwardDiagonal (cell, direction) := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryForwardSide, boundaryForwardDiagonal,
      gridDirectionCCW, gridStep] <;> omega

theorem backwardDiagonal_after_concaveSuccessor
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    boundaryBackwardDiagonal
        (boundaryForwardDiagonal (cell, direction),
          gridDirectionCW direction) = cell := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryBackwardDiagonal, boundaryForwardDiagonal,
      gridDirectionCCW, gridDirectionCW, gridStep] <;> omega

theorem backwardDiagonal_after_straightSuccessor
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    boundaryBackwardDiagonal
        (boundaryForwardSide (cell, direction), direction) =
      gridStep cell direction := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryBackwardDiagonal, boundaryForwardSide,
      gridDirectionCCW, gridDirectionCW, gridStep] <;> omega

theorem backwardSide_after_straightSuccessor
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    boundaryBackwardSide
        (boundaryForwardSide (cell, direction), direction) = cell := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryBackwardSide, boundaryForwardSide,
      gridDirectionCCW, gridDirectionCW, gridStep] <;> omega

theorem backwardDiagonal_after_convexSuccessor
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    boundaryBackwardDiagonal (cell, gridDirectionCCW direction) =
      boundaryForwardDiagonal (cell, direction) := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryBackwardDiagonal, boundaryForwardDiagonal,
      gridDirectionCCW, gridDirectionCW, gridStep] <;> omega

theorem backwardSide_after_convexSuccessor
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    boundaryBackwardSide (cell, gridDirectionCCW direction) =
      gridStep cell direction := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    apply LatticePoint.ext <;>
    simp [boundaryBackwardSide, boundaryForwardSide,
      gridDirectionCCW, gridDirectionCW, gridStep] <;> omega

/-- The wall follower preserves the finite set of literal boundary darts. -/
theorem boundaryDartSuccessorRaw_mem
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {dart : LatticePoint × GridDirection}
    (hdart : dart ∈ finiteSafeBoundaryDarts start hbounded) :
    boundaryDartSuccessorRaw (finiteSafeComponent start hbounded) dart ∈
      finiteSafeBoundaryDarts start hbounded := by
  classical
  have hdata := mem_finiteSafeBoundaryDarts.mp hdart
  have hsafe := safePoint_of_mem_safeComponent hdata.1
  by_cases hdiagonal :
      boundaryForwardDiagonal dart ∈ finiteSafeComponent start hbounded
  · have hdiagonalComponent :
        boundaryForwardDiagonal dart ∈ safeComponent start :=
      mem_finiteSafeComponent.mp hdiagonal
    apply mem_finiteSafeBoundaryDarts.mpr
    refine ⟨?_, ?_⟩
    · simpa [boundaryDartSuccessorRaw, hdiagonal] using
        hdiagonalComponent
    · simpa [boundaryDartSuccessorRaw, hdiagonal,
        boundaryForwardDiagonal_step_cw hsafe] using hdata.2
  · by_cases hside :
        boundaryForwardSide dart ∈ finiteSafeComponent start hbounded
    · have hsideComponent :
          boundaryForwardSide dart ∈ safeComponent start :=
        mem_finiteSafeComponent.mp hside
      apply mem_finiteSafeBoundaryDarts.mpr
      refine ⟨?_, ?_⟩
      · simpa [boundaryDartSuccessorRaw, hdiagonal, hside] using
          hsideComponent
      · have hdiagonalOutside :
            boundaryForwardDiagonal dart ∉ safeComponent start := by
          simpa using hdiagonal
        simpa [boundaryDartSuccessorRaw, hdiagonal, hside,
          boundaryForwardSide_step_outward hsafe] using
            hdiagonalOutside
    · have hsideOutside :
          boundaryForwardSide dart ∉ safeComponent start := by
        simpa using hside
      have hsuccessor :
          boundaryDartSuccessorRaw
              (finiteSafeComponent start hbounded) dart =
            (dart.1, gridDirectionCCW dart.2) := by
        simp [boundaryDartSuccessorRaw, hdiagonal, hside]
      rw [hsuccessor]
      apply mem_finiteSafeBoundaryDarts.mpr
      refine ⟨?_, ?_⟩
      · exact hdata.1
      · simpa [boundaryForwardSide] using hsideOutside

/-- The reverse local rule is a left inverse of the forward wall follower on
actual boundary darts. -/
theorem boundaryDartPredecessorRaw_successorRaw
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {dart : LatticePoint × GridDirection}
    (hdart : dart ∈ finiteSafeBoundaryDarts start hbounded) :
    boundaryDartPredecessorRaw (finiteSafeComponent start hbounded)
        (boundaryDartSuccessorRaw
          (finiteSafeComponent start hbounded) dart) = dart := by
  classical
  rcases dart with ⟨cell, direction⟩
  have hdata := mem_finiteSafeBoundaryDarts.mp hdart
  have hcell : cell ∈ finiteSafeComponent start hbounded :=
    mem_finiteSafeComponent.mpr hdata.1
  have houtside :
      gridStep cell direction ∉ finiteSafeComponent start hbounded := by
    simpa using hdata.2
  have hsafe := safePoint_of_mem_safeComponent hdata.1
  by_cases hdiagonal :
      boundaryForwardDiagonal (cell, direction) ∈
        finiteSafeComponent start hbounded
  · have hback := backwardDiagonal_after_concaveSuccessor
      (cell := cell) (direction := direction) hsafe
    simp [boundaryDartSuccessorRaw, hdiagonal,
      boundaryDartPredecessorRaw, hback, hcell]
  · by_cases hside :
        boundaryForwardSide (cell, direction) ∈
          finiteSafeComponent start hbounded
    · have hbackDiagonal :=
        backwardDiagonal_after_straightSuccessor
          (cell := cell) (direction := direction) hsafe
      have hbackSide := backwardSide_after_straightSuccessor
        (cell := cell) (direction := direction) hsafe
      simp [boundaryDartSuccessorRaw, hdiagonal, hside,
        boundaryDartPredecessorRaw, hbackDiagonal, hbackSide,
        houtside, hcell]
    · have hbackDiagonal :=
        backwardDiagonal_after_convexSuccessor
          (cell := cell) (direction := direction) hsafe
      have hbackSide := backwardSide_after_convexSuccessor
        (cell := cell) (direction := direction) hsafe
      simp [boundaryDartSuccessorRaw, hdiagonal, hside,
        boundaryDartPredecessorRaw, hbackDiagonal, hbackSide,
        houtside]

/-- The finite-type wall follower on actual boundary darts. -/
noncomputable def finiteSafeBoundaryDartSuccessor
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    {dart // dart ∈ finiteSafeBoundaryDarts start hbounded} →
      {dart // dart ∈ finiteSafeBoundaryDarts start hbounded} :=
  fun dart ↦
    ⟨boundaryDartSuccessorRaw
        (finiteSafeComponent start hbounded) dart.1,
      boundaryDartSuccessorRaw_mem dart.2⟩

theorem finiteSafeBoundaryDartSuccessor_injective
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    Function.Injective (finiteSafeBoundaryDartSuccessor start hbounded) := by
  intro left right heq
  apply Subtype.ext
  have hvalues := congrArg Subtype.val heq
  have hpred := congrArg
    (boundaryDartPredecessorRaw (finiteSafeComponent start hbounded))
    hvalues
  simpa [finiteSafeBoundaryDartSuccessor,
    boundaryDartPredecessorRaw_successorRaw left.2,
    boundaryDartPredecessorRaw_successorRaw right.2] using hpred

/-- Exterior lattice site carried by a boundary dart. -/
def boundaryDartOutside (dart : LatticePoint × GridDirection) :
    LatticePoint :=
  gridStep dart.1 dart.2

theorem boundaryDartOutside_mem_safeComponentFrontier
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {dart : LatticePoint × GridDirection}
    (hdart : dart ∈ finiteSafeBoundaryDarts start hbounded) :
    boundaryDartOutside dart ∈ safeComponentFrontier start := by
  have hdata := mem_finiteSafeBoundaryDarts.mp hdart
  have hsafe := safePoint_of_mem_safeComponent hdata.1
  exact ⟨hdata.2, dart.1, hdata.1,
    by simpa [boundaryDartOutside] using
      adjacent_gridStep dart.1 dart.2 hsafe⟩

/-- Reflexive closure of star adjacency, used because two consecutive
polyomino sides at a concave corner can carry the same exterior lattice
site. -/
def StarAdjacentOrEq (left right : LatticePoint) : Prop :=
  left = right ∨ StarAdjacent left right

theorem boundaryOutside_starAdjacent_forwardDiagonal
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    StarAdjacent (gridStep cell direction)
      (boundaryForwardDiagonal (cell, direction)) := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    simp [StarAdjacent, boundaryForwardDiagonal,
      gridDirectionCCW, gridStep] <;> omega

theorem boundaryOutside_starAdjacent_forwardSide
    {cell : LatticePoint} {direction : GridDirection}
    (hsafe : SafePoint cell) :
    StarAdjacent (gridStep cell direction)
      (boundaryForwardSide (cell, direction)) := by
  rcases hsafe with ⟨hx, hy, _⟩
  cases direction <;>
    simp [StarAdjacent, boundaryForwardSide,
      gridDirectionCCW, gridStep] <;> omega

/-- Consecutive wall-follower darts carry equal or star-adjacent exterior
frontier sites. -/
theorem boundaryDartOutside_successor_starAdjacentOrEq
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {dart : LatticePoint × GridDirection}
    (hdart : dart ∈ finiteSafeBoundaryDarts start hbounded) :
    StarAdjacentOrEq (boundaryDartOutside dart)
      (boundaryDartOutside
        (boundaryDartSuccessorRaw
          (finiteSafeComponent start hbounded) dart)) := by
  classical
  have hdata := mem_finiteSafeBoundaryDarts.mp hdart
  have hsafe := safePoint_of_mem_safeComponent hdata.1
  by_cases hdiagonal :
      boundaryForwardDiagonal dart ∈ finiteSafeComponent start hbounded
  · left
    simpa [boundaryDartOutside, boundaryDartSuccessorRaw, hdiagonal]
      using (boundaryForwardDiagonal_step_cw hsafe).symm
  · by_cases hside :
        boundaryForwardSide dart ∈ finiteSafeComponent start hbounded
    · right
      simpa [boundaryDartOutside, boundaryDartSuccessorRaw,
        hdiagonal, hside,
        boundaryForwardSide_step_outward hsafe] using
          boundaryOutside_starAdjacent_forwardDiagonal hsafe
    · right
      simpa [boundaryDartOutside, boundaryDartSuccessorRaw,
        hdiagonal, hside] using
          boundaryOutside_starAdjacent_forwardSide hsafe

noncomputable def finiteSafeBoundaryDartOutside
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (dart : {value // value ∈ finiteSafeBoundaryDarts start hbounded}) :
    LatticePoint :=
  boundaryDartOutside dart.1

theorem finiteSafeBoundaryDartOutside_successor_starAdjacentOrEq
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (dart : {value // value ∈ finiteSafeBoundaryDarts start hbounded}) :
    StarAdjacentOrEq (finiteSafeBoundaryDartOutside dart)
      (finiteSafeBoundaryDartOutside
        (finiteSafeBoundaryDartSuccessor start hbounded dart)) := by
  simpa [finiteSafeBoundaryDartOutside,
    finiteSafeBoundaryDartSuccessor] using
      boundaryDartOutside_successor_starAdjacentOrEq dart.2

/-- The exterior sites carried by any finite wall-follower orbit form one
star walk after consecutive duplicate sites at concave corners are suppressed.
Every orbit site remains in the support of the resulting walk. -/
theorem exists_finiteSafeBoundaryOutsideOrbitWalk_with_length
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (dart : {value // value ∈ finiteSafeBoundaryDarts start hbounded})
    (steps : Nat) :
    ∃ walk : starLatticeGraph.Walk
        (finiteSafeBoundaryDartOutside dart)
        (finiteSafeBoundaryDartOutside
          ((finiteSafeBoundaryDartSuccessor start hbounded)^[steps] dart)),
      walk.length ≤ steps ∧
      (∀ index, index ≤ steps →
        finiteSafeBoundaryDartOutside
            ((finiteSafeBoundaryDartSuccessor start hbounded)^[index] dart) ∈
          walk.support) ∧
      (∀ point ∈ walk.support,
        ∃ index ≤ steps,
          point = finiteSafeBoundaryDartOutside
            ((finiteSafeBoundaryDartSuccessor start hbounded)^[index] dart)) := by
  let successor := finiteSafeBoundaryDartSuccessor start hbounded
  induction steps with
  | zero =>
      refine ⟨SimpleGraph.Walk.nil, by simp, ?_, ?_⟩
      · intro index hindex
        have hzero : index = 0 := by omega
        subst index
        simp
      · intro point hpoint
        have hpointEq :
            point = finiteSafeBoundaryDartOutside dart := by
          simpa using hpoint
        exact ⟨0, le_refl _, by simpa using hpointEq⟩
  | succ steps ih =>
      obtain ⟨walk, hlength, hcover, horbit⟩ := ih
      let current := successor^[steps] dart
      let next := successor current
      have hiterate : successor^[steps + 1] dart = next := by
        simpa [current, next] using
          (Function.iterate_succ_apply' successor steps dart)
      rw [hiterate]
      have hnear : StarAdjacentOrEq
          (finiteSafeBoundaryDartOutside current)
          (finiteSafeBoundaryDartOutside next) := by
        simpa [successor, next] using
          finiteSafeBoundaryDartOutside_successor_starAdjacentOrEq current
      rcases hnear with hequal | hadjacent
      · let copied : starLatticeGraph.Walk
            (finiteSafeBoundaryDartOutside dart)
            (finiteSafeBoundaryDartOutside next) :=
          walk.copy rfl hequal
        refine ⟨copied, ?_, ?_, ?_⟩
        · simpa [copied] using hlength.trans (Nat.le_succ steps)
        · intro index hindex
          by_cases hprevious : index ≤ steps
          · simpa [copied] using hcover index hprevious
          · have hlast : index = steps + 1 := by omega
            subst index
            have hcurrentMem :
                finiteSafeBoundaryDartOutside current ∈ walk.support := by
              change finiteSafeBoundaryDartOutside
                (successor^[steps] dart) ∈ walk.support
              exact hcover steps (le_refl _)
            change finiteSafeBoundaryDartOutside
                (successor^[steps + 1] dart) ∈ copied.support
            rw [hiterate]
            rw [SimpleGraph.Walk.support_copy]
            rw [← hequal]
            exact hcurrentMem
        · intro point hpoint
          have hpointWalk : point ∈ walk.support := by
            simpa [copied] using hpoint
          obtain ⟨index, hindex, hpointEq⟩ := horbit point hpointWalk
          exact ⟨index, hindex.trans (Nat.le_succ _), hpointEq⟩
      · let extended : starLatticeGraph.Walk
            (finiteSafeBoundaryDartOutside dart)
            (finiteSafeBoundaryDartOutside next) :=
          walk.concat hadjacent
        refine ⟨extended, ?_, ?_, ?_⟩
        · simp only [extended, SimpleGraph.Walk.length_concat]
          omega
        · intro index hindex
          by_cases hprevious : index ≤ steps
          · apply walk.support_subset_support_concat hadjacent
            simpa [current] using hcover index hprevious
          · have hlast : index = steps + 1 := by omega
            subst index
            change finiteSafeBoundaryDartOutside
                (successor^[steps + 1] dart) ∈ extended.support
            rw [hiterate]
            simpa [extended] using
              extended.getVert_mem_support extended.length
        · intro point hpoint
          rw [show extended.support =
              walk.support ++ [finiteSafeBoundaryDartOutside next] by
            simp [extended]] at hpoint
          rcases List.mem_append.mp hpoint with hpointWalk | hpointLast
          · obtain ⟨index, hindex, hpointEq⟩ := horbit point hpointWalk
            exact ⟨index, hindex.trans (Nat.le_succ _), hpointEq⟩
          · have hpointEq : point = finiteSafeBoundaryDartOutside next := by
              simpa using hpointLast
            refine ⟨steps + 1, le_refl _, ?_⟩
            rw [hiterate]
            exact hpointEq

/-- Compatibility projection of the length-controlled construction. -/
theorem exists_finiteSafeBoundaryOutsideOrbitWalk
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (dart : {value // value ∈ finiteSafeBoundaryDarts start hbounded})
    (steps : Nat) :
    ∃ walk : starLatticeGraph.Walk
        (finiteSafeBoundaryDartOutside dart)
        (finiteSafeBoundaryDartOutside
          ((finiteSafeBoundaryDartSuccessor start hbounded)^[steps] dart)),
      (∀ index, index ≤ steps →
        finiteSafeBoundaryDartOutside
            ((finiteSafeBoundaryDartSuccessor start hbounded)^[index] dart) ∈
          walk.support) ∧
      (∀ point ∈ walk.support,
        ∃ index ≤ steps,
          point = finiteSafeBoundaryDartOutside
            ((finiteSafeBoundaryDartSuccessor start hbounded)^[index] dart)) := by
  obtain ⟨walk, _hlength, hcover, horbit⟩ :=
    exists_finiteSafeBoundaryOutsideOrbitWalk_with_length dart steps
  exact ⟨walk, hcover, horbit⟩

/-- Every point of an injective self-map of a finite type is periodic, with
a positive return time bounded by the cardinality of the type. -/
theorem exists_positive_iterate_eq_self_of_fintype_injective
    {α : Type*} [Fintype α]
    (f : α → α) (hinjective : Function.Injective f) (x : α) :
    ∃ period,
      0 < period ∧ period ≤ Fintype.card α ∧ f^[period] x = x := by
  let orbit : Fin (Fintype.card α + 1) → α :=
    fun index ↦ f^[index.val] x
  have hcard :
      Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨left, right, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt orbit hcard
  have hvalNe : left.val ≠ right.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hvalNe with hleft | hright
  · let period := right.val - left.val
    have hperiodPositive : 0 < period := by
      dsimp [period]
      omega
    have hperiodBound : period ≤ Fintype.card α := by
      have hrightBound := right.isLt
      dsimp [period]
      omega
    have hreturn : f^[period] x = x := by
      apply Function.iterate_cancel hinjective
      dsimp [orbit] at heq
      exact heq.symm
    exact ⟨period, hperiodPositive, hperiodBound, hreturn⟩
  · let period := left.val - right.val
    have hperiodPositive : 0 < period := by
      dsimp [period]
      omega
    have hperiodBound : period ≤ Fintype.card α := by
      have hleftBound := left.isLt
      dsimp [period]
      omega
    have hreturn : f^[period] x = x := by
      apply Function.iterate_cancel hinjective
      dsimp [orbit] at heq
      exact heq
    exact ⟨period, hperiodPositive, hperiodBound, hreturn⟩

/-- The south side immediately above the certified lower exterior anchor is
the canonical initial boundary dart. -/
theorem primeCorridorOuterBoundaryAnchor_southDart_mem
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    (verticalLinePoint root.1
        ((primeCorridorOuterBoundaryAnchor hroot hbounded).y + 1),
      GridDirection.south) ∈
      finiteSafeBoundaryDarts (primeCorridorPoint root) hbounded := by
  classical
  let anchor := primeCorridorOuterBoundaryAnchor hroot hbounded
  have hspec := primeCorridorOuterBoundaryAnchor_spec hroot hbounded
  apply mem_finiteSafeBoundaryDarts.mpr
  constructor
  · simpa [anchor] using hspec.2.2.2.1
  · have hstep :
        gridStep (verticalLinePoint root.1 (anchor.y + 1))
            GridDirection.south = anchor := by
      apply LatticePoint.ext
      · simpa [anchor, verticalLinePoint, gridStep] using hspec.1.symm
      · simp [verticalLinePoint, gridStep]
    rw [hstep]
    exact hspec.2.2.2.2.1.1

/-- The canonical initial dart as an element of the finite dart type. -/
noncomputable def primeCorridorOuterBoundaryAnchorDart
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    {dart // dart ∈
      finiteSafeBoundaryDarts (primeCorridorPoint root) hbounded} :=
  ⟨(verticalLinePoint root.1
      ((primeCorridorOuterBoundaryAnchor hroot hbounded).y + 1),
      GridDirection.south),
    primeCorridorOuterBoundaryAnchor_southDart_mem hroot hbounded⟩

/-- The wall follower returns to the certified outer-anchor dart.  Injectivity
removes the transient part that an arbitrary finite functional graph could
have, so the returned orbit is rooted at the actual lower exterior anchor. -/
theorem exists_primeCorridorOuterBoundaryDart_period
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    ∃ period,
      0 < period ∧
      period ≤ (finiteSafeBoundaryDarts
        (primeCorridorPoint root) hbounded).card ∧
      (finiteSafeBoundaryDartSuccessor
          (primeCorridorPoint root) hbounded)^[period]
        (primeCorridorOuterBoundaryAnchorDart hroot hbounded) =
          primeCorridorOuterBoundaryAnchorDart hroot hbounded := by
  simpa using
    exists_positive_iterate_eq_self_of_fintype_injective
      (finiteSafeBoundaryDartSuccessor
        (primeCorridorPoint root) hbounded)
      (finiteSafeBoundaryDartSuccessor_injective
        (primeCorridorPoint root) hbounded)
      (primeCorridorOuterBoundaryAnchorDart hroot hbounded)

theorem primeCorridorOuterBoundaryAnchorDart_outside
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    finiteSafeBoundaryDartOutside
        (primeCorridorOuterBoundaryAnchorDart hroot hbounded) =
      primeCorridorOuterBoundaryAnchor hroot hbounded := by
  have hspec := primeCorridorOuterBoundaryAnchor_spec hroot hbounded
  apply LatticePoint.ext
  · simpa [finiteSafeBoundaryDartOutside, boundaryDartOutside,
      primeCorridorOuterBoundaryAnchorDart, verticalLinePoint,
      gridStep] using hspec.1.symm
  · simp [finiteSafeBoundaryDartOutside, boundaryDartOutside,
      primeCorridorOuterBoundaryAnchorDart, verticalLinePoint,
      gridStep]

/-- A closed, actual exterior-frontier star walk rooted at the certified
prime--prime outer anchor.  Every walk vertex is a literal exterior vertex of
the original finite safe component. -/
theorem exists_primeCorridorCanonicalOuterBoundaryWalk
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N)
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root)) :
    ∃ period,
      0 < period ∧
      period ≤ (finiteSafeBoundaryDarts
        (primeCorridorPoint root) hbounded).card ∧
      ∃ walk : starLatticeGraph.Walk
          (primeCorridorOuterBoundaryAnchor hroot hbounded)
          (primeCorridorOuterBoundaryAnchor hroot hbounded),
        ∀ point ∈ walk.support,
          point ∈ safeComponentFrontier (primeCorridorPoint root) := by
  classical
  let start := primeCorridorPoint root
  let dart := primeCorridorOuterBoundaryAnchorDart hroot hbounded
  let successor := finiteSafeBoundaryDartSuccessor start hbounded
  obtain ⟨period, hperiodPositive, hperiodBound, hreturn⟩ :=
    exists_primeCorridorOuterBoundaryDart_period hroot hbounded
  obtain ⟨rawWalk, _hcover, horbit⟩ :=
    exists_finiteSafeBoundaryOutsideOrbitWalk dart period
  have hstartOutside :
      finiteSafeBoundaryDartOutside dart =
        primeCorridorOuterBoundaryAnchor hroot hbounded := by
    simpa [dart] using
      primeCorridorOuterBoundaryAnchorDart_outside hroot hbounded
  have hendOutside :
      finiteSafeBoundaryDartOutside (successor^[period] dart) =
        primeCorridorOuterBoundaryAnchor hroot hbounded := by
    have hreturn' : successor^[period] dart = dart := by
      simpa [successor, start, dart] using hreturn
    rw [hreturn', hstartOutside]
  let walk : starLatticeGraph.Walk
      (primeCorridorOuterBoundaryAnchor hroot hbounded)
      (primeCorridorOuterBoundaryAnchor hroot hbounded) :=
    rawWalk.copy hstartOutside hendOutside
  refine ⟨period, hperiodPositive, hperiodBound, walk, ?_⟩
  intro point hpoint
  have hpointRaw : point ∈ rawWalk.support := by
    simpa [walk] using hpoint
  obtain ⟨index, hindex, hpointEq⟩ := horbit point hpointRaw
  have hdartMem :=
    boundaryDartOutside_mem_safeComponentFrontier
      ((successor^[index] dart).2)
  rw [hpointEq]
  simpa [finiteSafeBoundaryDartOutside, successor, start] using hdartMem

end Erdos1212Kernel
