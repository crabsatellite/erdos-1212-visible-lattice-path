import Erdos1212Kernel.AlgebraicCorridorRectangleReachability
import Erdos1212Kernel.FiniteComponentBoundaryTrace

namespace Erdos1212Kernel
noncomputable section

def CorridorRectangle.leftCells (R : CorridorRectangle) : Finset LatticePoint :=
  R.leftReachable_finite.toFinset

@[simp] theorem CorridorRectangle.mem_leftCells (R : CorridorRectangle) (p : LatticePoint) :
    p ∈ R.leftCells ↔ R.LeftReachable p := Set.Finite.mem_toFinset _

def CorridorRectangle.BoundaryDart (R : CorridorRectangle)
    (d : LatticePoint × GridDirection) : Prop :=
  d.1 ∈ R.leftCells ∧ gridStep d.1 d.2 ∉ R.leftCells

theorem CorridorRectangle.boundary_successor (R : CorridorRectangle)
    {d : LatticePoint × GridDirection} (hd : R.BoundaryDart d) :
    R.BoundaryDart (boundaryDartSuccessorRaw R.leftCells d) := by
  classical
  have hs := (R.leftReachable_mem ((R.mem_leftCells d.1).mp hd.1)).2
  by_cases hdiag : boundaryForwardDiagonal d ∈ R.leftCells
  · constructor
    · simpa [boundaryDartSuccessorRaw, hdiag] using hdiag
    · simpa [boundaryDartSuccessorRaw, hdiag,
        boundaryForwardDiagonal_step_cw hs] using hd.2
  · by_cases hside : boundaryForwardSide d ∈ R.leftCells
    · constructor
      · simpa [boundaryDartSuccessorRaw, hdiag, hside] using hside
      · simpa [boundaryDartSuccessorRaw, hdiag, hside,
          boundaryForwardSide_step_outward hs] using hdiag
    · constructor
      · simpa [boundaryDartSuccessorRaw, hdiag, hside] using hd.1
      · simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside]
        exact hside

theorem CorridorRectangle.boundary_predecessor_successor (R : CorridorRectangle)
    {d : LatticePoint × GridDirection} (hd : R.BoundaryDart d) :
    boundaryDartPredecessorRaw R.leftCells
      (boundaryDartSuccessorRaw R.leftCells d) = d := by
  classical
  rcases d with ⟨cell, direction⟩
  have hs := (R.leftReachable_mem ((R.mem_leftCells cell).mp hd.1)).2
  have hcell := hd.1
  have hout := hd.2
  by_cases hdiag : boundaryForwardDiagonal (cell, direction) ∈ R.leftCells
  · have hb := backwardDiagonal_after_concaveSuccessor
      (cell := cell) (direction := direction) hs
    simp [boundaryDartSuccessorRaw, hdiag, boundaryDartPredecessorRaw, hb, hcell]
  · by_cases hside : boundaryForwardSide (cell, direction) ∈ R.leftCells
    · have hb := backwardDiagonal_after_straightSuccessor
        (cell := cell) (direction := direction) hs
      have hc := backwardSide_after_straightSuccessor
        (cell := cell) (direction := direction) hs
      simp [boundaryDartSuccessorRaw, hdiag, hside,
        boundaryDartPredecessorRaw, hb, hc, hout, hcell]
    · have hb := backwardDiagonal_after_convexSuccessor
        (cell := cell) (direction := direction) hs
      have hc := backwardSide_after_convexSuccessor
        (cell := cell) (direction := direction) hs
      simp [boundaryDartSuccessorRaw, hdiag, hside,
        boundaryDartPredecessorRaw, hb, hc, hout]

theorem CorridorRectangle.boundary_outside_step (R : CorridorRectangle)
    {d : LatticePoint × GridDirection} (hd : R.BoundaryDart d) :
    StarAdjacentOrEq (boundaryDartOutside d)
      (boundaryDartOutside (boundaryDartSuccessorRaw R.leftCells d)) := by
  classical
  have hs := (R.leftReachable_mem ((R.mem_leftCells d.1).mp hd.1)).2
  by_cases hdiag : boundaryForwardDiagonal d ∈ R.leftCells
  · left
    simpa [boundaryDartOutside, boundaryDartSuccessorRaw, hdiag]
      using (boundaryForwardDiagonal_step_cw hs).symm
  · by_cases hside : boundaryForwardSide d ∈ R.leftCells
    · right
      simpa [boundaryDartOutside, boundaryDartSuccessorRaw, hdiag, hside,
        boundaryForwardSide_step_outward hs] using
        boundaryOutside_starAdjacent_forwardDiagonal hs
    · right
      simpa [boundaryDartOutside, boundaryDartSuccessorRaw, hdiag, hside] using
        boundaryOutside_starAdjacent_forwardSide hs

end
end Erdos1212Kernel
