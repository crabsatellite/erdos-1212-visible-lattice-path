import Erdos1212Kernel.AlgebraicCorridorAugmentedBoundary

namespace Erdos1212Kernel
noncomputable section

theorem CorridorRectangle.augmented_x_lower {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.AugmentedLeft p) : R.left ≤ p.x + 1 := by
  rcases hp with hp | hp
  · exact hp.1.ge
  · have h := (R.leftReachable_mem hp).1.1
    omega

theorem CorridorRectangle.augmented_y_bounds {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.AugmentedLeft p) : R.bottom ≤ p.y ∧ p.y ≤ R.top := by
  rcases hp with hp | hp
  · exact hp.2
  · exact (R.leftReachable_mem hp).1.2.2

def CorridorRectangle.westDart (R : CorridorRectangle) (y : ℕ) :
    LatticePoint × GridDirection := (⟨R.left - 1, y⟩, .west)

theorem CorridorRectangle.westDart_mem (R : CorridorRectangle)
    (hl : 2 < R.left) {y : ℕ} (hy : R.bottom ≤ y ∧ y ≤ R.top) :
    R.AugmentedDart (R.westDart y) := by
  constructor
  · apply (R.mem_augmentedCells _).mpr
    left
    exact ⟨by dsimp [westDart]; omega, hy⟩
  · intro h
    have hx := R.augmented_x_lower ((R.mem_augmentedCells _).mp h)
    dsimp [westDart, gridStep] at hx
    omega

theorem CorridorRectangle.westDart_successor (R : CorridorRectangle)
    (hl : 2 < R.left) {y : ℕ} (hy : R.bottom < y) (ht : y ≤ R.top) :
    boundaryDartSuccessorRaw R.augmentedCells (R.westDart y) =
      R.westDart (y - 1) := by
  classical
  have hdiag : boundaryForwardDiagonal (R.westDart y) ∉ R.augmentedCells := by
    intro h
    have hx := R.augmented_x_lower ((R.mem_augmentedCells _).mp h)
    dsimp [westDart, boundaryForwardDiagonal, gridDirectionCCW, gridStep] at hx
    omega
  have hside : boundaryForwardSide (R.westDart y) ∈ R.augmentedCells := by
    apply (R.mem_augmentedCells _).mpr
    left
    dsimp [AuxiliaryLeft, boundaryForwardSide, westDart, gridDirectionCCW, gridStep]
    exact ⟨by omega, by omega, by omega⟩
  simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_pos hside]
  rfl

theorem CorridorRectangle.westDart_bottom_turn (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 0 < R.bottom) :
    boundaryDartSuccessorRaw R.augmentedCells (R.westDart R.bottom) =
      (⟨R.left - 1, R.bottom⟩, GridDirection.south) := by
  classical
  have hdiag : boundaryForwardDiagonal (R.westDart R.bottom) ∉ R.augmentedCells := by
    intro h
    have hx := R.augmented_x_lower ((R.mem_augmentedCells _).mp h)
    dsimp [westDart, boundaryForwardDiagonal, gridDirectionCCW, gridStep] at hx
    omega
  have hside : boundaryForwardSide (R.westDart R.bottom) ∉ R.augmentedCells := by
    intro h
    have hy := (R.augmented_y_bounds ((R.mem_augmentedCells _).mp h)).1
    dsimp [westDart, boundaryForwardSide, gridDirectionCCW, gridStep] at hy
    omega
  simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside]
  rfl

theorem CorridorRectangle.westDart_iterate_to_bottom (R : CorridorRectangle)
    (hl : 2 < R.left) (k : ℕ) (hk : R.bottom + k ≤ R.top) :
    (boundaryDartSuccessorRaw R.augmentedCells)^[k]
      (R.westDart (R.bottom + k)) = R.westDart R.bottom := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [R.westDart_successor hl (by omega) hk]
    have hy : R.bottom + (k + 1) - 1 = R.bottom + k := by omega
    rw [hy]
    exact ih (by omega)

theorem CorridorRectangle.westDart_top_to_bottom (R : CorridorRectangle)
    (hl : 2 < R.left) :
    (boundaryDartSuccessorRaw R.augmentedCells)^[R.top - R.bottom]
      (R.westDart R.top) = R.westDart R.bottom := by
  have hy : R.bottom + (R.top - R.bottom) = R.top := by
    have h := R.vertical
    omega
  have h := R.westDart_iterate_to_bottom hl (R.top - R.bottom) (by omega)
  rwa [hy] at h

end
end Erdos1212Kernel
