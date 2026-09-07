import Erdos1212Kernel.AlgebraicCorridorAuxiliarySide

namespace Erdos1212Kernel
noncomputable section

def CorridorRectangle.augmentedCells (R : CorridorRectangle) : Finset LatticePoint :=
  R.augmentedLeft_finite.toFinset

@[simp] theorem CorridorRectangle.mem_augmentedCells (R : CorridorRectangle) (p : LatticePoint) :
    p ∈ R.augmentedCells ↔ R.AugmentedLeft p := Set.Finite.mem_toFinset _

def CorridorRectangle.AugmentedDart (R : CorridorRectangle)
    (d : LatticePoint × GridDirection) : Prop :=
  d.1 ∈ R.augmentedCells ∧ gridStep d.1 d.2 ∉ R.augmentedCells

theorem CorridorRectangle.augmented_coords {R : CorridorRectangle}
    (hl : 2 < R.left) (hb : 1 < R.bottom) {p : LatticePoint}
    (hp : R.AugmentedLeft p) : 1 < p.x ∧ 1 < p.y := by
  rcases hp with hp | hp
  · have hx := hp.1
    have hy := hp.2.1
    constructor <;> omega
  · have h := (R.leftReachable_mem hp).1
    constructor
    · have hx := h.1
      omega
    · have hy := h.2.2.1
      omega

/-- The wall follower uses only the positive lattice coordinates, not safety
of the auxiliary side. -/
theorem CorridorRectangle.augmented_boundary_successor (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d) :
    R.AugmentedDart (boundaryDartSuccessorRaw R.augmentedCells d) := by
  classical
  have hpos := R.augmented_coords hl hb ((R.mem_augmentedCells d.1).mp hd.1)
  have hdiagEq : gridStep (boundaryForwardDiagonal d) (gridDirectionCW d.2) =
      gridStep d.1 d.2 := by
    rcases d with ⟨p, dir⟩
    rcases hpos with ⟨hx, hy⟩
    change 1 < p.x at hx
    change 1 < p.y at hy
    cases dir <;> apply LatticePoint.ext <;>
      simp [boundaryForwardDiagonal, gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
  have hsideEq : gridStep (boundaryForwardSide d) d.2 = boundaryForwardDiagonal d := by
    rcases d with ⟨p, dir⟩
    rcases hpos with ⟨hx, hy⟩
    change 1 < p.x at hx
    change 1 < p.y at hy
    cases dir <;> apply LatticePoint.ext <;>
      simp [boundaryForwardSide, boundaryForwardDiagonal, gridDirectionCCW, gridStep] <;> omega
  by_cases hdiag : boundaryForwardDiagonal d ∈ R.augmentedCells
  · constructor
    · simpa only [boundaryDartSuccessorRaw, if_pos hdiag] using hdiag
    · simpa only [boundaryDartSuccessorRaw, if_pos hdiag, hdiagEq] using hd.2
  · by_cases hside : boundaryForwardSide d ∈ R.augmentedCells
    · constructor
      · simpa only [boundaryDartSuccessorRaw, if_neg hdiag, if_pos hside] using hside
      · simpa only [boundaryDartSuccessorRaw, if_neg hdiag, if_pos hside, hsideEq] using hdiag
    · constructor
      · simpa only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside] using hd.1
      · simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside]
        exact hside

theorem CorridorRectangle.augmented_boundary_outside_bad (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d)
    (hin : R.Contains (boundaryDartOutside d)) : CorridorBad (boundaryDartOutside d) := by
  have hp := (R.mem_augmentedCells d.1).mp hd.1
  have hpos := R.augmented_coords hl hb hp
  have hadj : Adjacent d.1 (boundaryDartOutside d) := by
    rcases d with ⟨p, dir⟩
    rcases hpos with ⟨hx, hy⟩
    change 1 < p.x at hx
    change 1 < p.y at hy
    cases dir <;> simp [boundaryDartOutside, gridStep, Adjacent] <;> omega
  exact R.augmented_frontier_bad hp hin hadj
    (fun h => hd.2 ((R.mem_augmentedCells _).mpr h))

theorem CorridorRectangle.augmented_boundary_outside_step (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d) :
    StarAdjacentOrEq (boundaryDartOutside d)
      (boundaryDartOutside (boundaryDartSuccessorRaw R.augmentedCells d)) := by
  classical
  have hpos := R.augmented_coords hl hb ((R.mem_augmentedCells d.1).mp hd.1)
  rcases d with ⟨p, dir⟩
  rcases hpos with ⟨hx, hy⟩
  change 1 < p.x at hx
  change 1 < p.y at hy
  by_cases hdiag : boundaryForwardDiagonal (p, dir) ∈ R.augmentedCells
  · left
    simp only [boundaryDartSuccessorRaw, if_pos hdiag]
    cases dir <;> apply LatticePoint.ext <;>
      simp [boundaryDartOutside, boundaryForwardDiagonal,
        gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
  · by_cases hside : boundaryForwardSide (p, dir) ∈ R.augmentedCells
    · right
      simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_pos hside]
      cases dir <;>
        simp [boundaryDartOutside, boundaryForwardSide, gridDirectionCCW,
          gridStep, StarAdjacent] <;> omega
    · right
      simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside]
      cases dir <;>
        simp [boundaryDartOutside, gridDirectionCCW, gridStep, StarAdjacent] <;> omega

theorem CorridorRectangle.augmented_predecessor_successor (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d) :
    boundaryDartPredecessorRaw R.augmentedCells
      (boundaryDartSuccessorRaw R.augmentedCells d) = d := by
  classical
  have hpos := R.augmented_coords hl hb ((R.mem_augmentedCells d.1).mp hd.1)
  rcases d with ⟨p, dir⟩
  rcases hpos with ⟨hx, hy⟩
  change 1 < p.x at hx
  change 1 < p.y at hy
  have hcell := hd.1
  have hout := hd.2
  by_cases hdiag : boundaryForwardDiagonal (p, dir) ∈ R.augmentedCells
  · have heq : boundaryBackwardDiagonal
        (boundaryForwardDiagonal (p, dir), gridDirectionCW dir) = p := by
      cases dir <;> apply LatticePoint.ext <;>
        simp [boundaryBackwardDiagonal, boundaryForwardDiagonal,
          gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
    simp [boundaryDartSuccessorRaw, hdiag, boundaryDartPredecessorRaw, heq, hcell]
  · by_cases hside : boundaryForwardSide (p, dir) ∈ R.augmentedCells
    · have hdg : boundaryBackwardDiagonal (boundaryForwardSide (p, dir), dir) =
          gridStep p dir := by
        cases dir <;> apply LatticePoint.ext <;>
          simp [boundaryBackwardDiagonal, boundaryForwardSide,
            gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
      have hsd : boundaryBackwardSide (boundaryForwardSide (p, dir), dir) = p := by
        cases dir <;> apply LatticePoint.ext <;>
          simp [boundaryBackwardSide, boundaryForwardSide,
            gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
      simp [boundaryDartSuccessorRaw, hdiag, hside, boundaryDartPredecessorRaw,
        hdg, hsd, hout, hcell]
    · have hdg : boundaryBackwardDiagonal (p, gridDirectionCCW dir) =
          boundaryForwardDiagonal (p, dir) := by
        cases dir <;> apply LatticePoint.ext <;>
          simp [boundaryBackwardDiagonal, boundaryForwardDiagonal,
            gridDirectionCCW, gridDirectionCW, gridStep] <;> omega
      have hsd : boundaryBackwardSide (p, gridDirectionCCW dir) = gridStep p dir := by
        cases dir <;> rfl
      simp [boundaryDartSuccessorRaw, hdiag, hside, boundaryDartPredecessorRaw,
        hdg, hsd, hout]

theorem CorridorRectangle.augmented_successor_injective (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    Set.InjOn (boundaryDartSuccessorRaw R.augmentedCells)
      {d | R.AugmentedDart d} := by
  intro d hd e he h
  have h' := congrArg (boundaryDartPredecessorRaw R.augmentedCells) h
  rwa [R.augmented_predecessor_successor hl hb hd,
    R.augmented_predecessor_successor hl hb he] at h'

def CorridorRectangle.augmentedDarts (R : CorridorRectangle) :
    Finset (LatticePoint × GridDirection) := by
  classical
  exact (R.augmentedCells ×ˢ Finset.univ).filter
    (fun d => gridStep d.1 d.2 ∉ R.augmentedCells)

@[simp] theorem CorridorRectangle.mem_augmentedDarts (R : CorridorRectangle)
    (d : LatticePoint × GridDirection) : d ∈ R.augmentedDarts ↔ R.AugmentedDart d := by
  classical
  simp [augmentedDarts, AugmentedDart]

def CorridorRectangle.augmentedSuccessor (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) : R.augmentedDarts → R.augmentedDarts :=
  fun d => ⟨boundaryDartSuccessorRaw R.augmentedCells d.val,
    (R.mem_augmentedDarts _).mpr
      (R.augmented_boundary_successor hl hb ((R.mem_augmentedDarts _).mp d.property))⟩

theorem CorridorRectangle.augmentedSuccessor_injective (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    Function.Injective (R.augmentedSuccessor hl hb) := by
  intro d e h
  apply Subtype.ext
  exact R.augmented_successor_injective hl hb
    ((R.mem_augmentedDarts _).mp d.property)
    ((R.mem_augmentedDarts _).mp e.property) (congrArg Subtype.val h)

theorem CorridorRectangle.augmented_orbit_returns (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) (d : R.augmentedDarts) :
    ∃ n : ℕ, 0 < n ∧ n ≤ R.augmentedDarts.card ∧
      (R.augmentedSuccessor hl hb)^[n] d = d := by
  classical
  simpa only [Fintype.card_coe] using
    exists_positive_iterate_eq_self_of_fintype_injective
      (R.augmentedSuccessor hl hb) (R.augmentedSuccessor_injective hl hb) d

end
end Erdos1212Kernel
