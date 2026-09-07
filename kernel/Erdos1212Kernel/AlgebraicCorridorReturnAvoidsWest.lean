import Erdos1212Kernel.AlgebraicCorridorBoundaryLocation

namespace Erdos1212Kernel
noncomputable section

theorem CorridorRectangle.southCorner_mem (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) : R.AugmentedDart R.southCorner := by
  have h := R.augmented_boundary_successor hl hb
    (R.westDart_mem hl ⟨le_rfl, R.vertical⟩)
  rwa [R.westDart_bottom_turn hl (by omega)] at h

theorem CorridorRectangle.predecessor_of_west (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d)
    {y : ℕ} (hy : R.bottom ≤ y ∧ y ≤ R.top)
    (hstep : boundaryDartSuccessorRaw R.augmentedCells d = R.westDart y) :
    d = R.northCorner ∨ d = R.westDart (y + 1) := by
  by_cases ht : y = R.top
  · left
    apply R.augmented_successor_injective hl hb hd (R.northCorner_mem hl)
    rw [R.northCorner_successor hl, hstep, ht]
  · right
    have hyNext : R.bottom ≤ y + 1 ∧ y + 1 ≤ R.top := by omega
    apply R.augmented_successor_injective hl hb hd (R.westDart_mem hl hyNext)
    rw [R.westDart_successor hl (by omega) hyNext.2]
    simpa using hstep

/-- Before the first north-corner visit, the return orbit cannot enter the
explicit auxiliary west-side segment. -/
theorem CorridorRectangle.return_orbit_avoids_west (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) (n : ℕ)
    (hbefore : ∀ i < n,
      (boundaryDartSuccessorRaw R.augmentedCells)^[i] R.southCorner ≠ R.northCorner) :
    ∀ y, R.bottom ≤ y → y ≤ R.top →
      (boundaryDartSuccessorRaw R.augmentedCells)^[n] R.southCorner ≠ R.westDart y := by
  induction n with
  | zero =>
    intro y hyl hyu heq
    have hdir := congrArg Prod.snd heq
    simp [southCorner, westDart] at hdir
  | succ n ih =>
    intro y hyl hyu heq
    have hmem := R.augmented_raw_iterate_mem hl hb (R.southCorner_mem hl hb) n
    rw [Function.iterate_succ_apply'] at heq
    rcases R.predecessor_of_west hl hb hmem ⟨hyl, hyu⟩ heq with hn | hw
    · exact hbefore n (by omega) hn
    · have hpre := (R.mem_augmentedCells _).mp hmem.1
      rw [hw] at hpre
      have hyNext := R.augmented_y_bounds hpre
      exact ih (fun i hi => hbefore i (by omega)) (y + 1)
        (by omega) hyNext.2 hw

theorem CorridorRectangle.first_return_inside (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) (hno : ¬R.SafeHorizontalCrossing)
    (n : ℕ)
    (hbefore : ∀ i < n,
      (boundaryDartSuccessorRaw R.augmentedCells)^[i] R.southCorner ≠ R.northCorner)
    (hy : R.bottom ≤ (boundaryDartOutside
        ((boundaryDartSuccessorRaw R.augmentedCells)^[n] R.southCorner)).y ∧
      (boundaryDartOutside
        ((boundaryDartSuccessorRaw R.augmentedCells)^[n] R.southCorner)).y ≤ R.top) :
    R.Contains (boundaryDartOutside
      ((boundaryDartSuccessorRaw R.augmentedCells)^[n] R.southCorner)) := by
  apply R.boundary_inside_of_not_west hl hno
    (R.augmented_raw_iterate_mem hl hb (R.southCorner_mem hl hb) n) hy
  exact R.return_orbit_avoids_west hl hb n hbefore _ hy.1 hy.2

end
end Erdos1212Kernel
