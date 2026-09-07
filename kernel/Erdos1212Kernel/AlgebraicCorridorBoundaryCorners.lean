import Erdos1212Kernel.AlgebraicCorridorReturnOrbit

namespace Erdos1212Kernel
noncomputable section

def CorridorRectangle.northCorner (R : CorridorRectangle) : LatticePoint × GridDirection :=
  (⟨R.left - 1, R.top⟩, .north)
def CorridorRectangle.southCorner (R : CorridorRectangle) : LatticePoint × GridDirection :=
  (⟨R.left - 1, R.bottom⟩, .south)

theorem CorridorRectangle.northCorner_mem (R : CorridorRectangle) (hl : 2 < R.left) :
    R.AugmentedDart R.northCorner := by
  constructor
  · apply (R.mem_augmentedCells _).mpr
    left
    exact ⟨by dsimp [northCorner]; omega, R.vertical, le_rfl⟩
  · intro h
    have hy := (R.augmented_y_bounds ((R.mem_augmentedCells _).mp h)).2
    dsimp [northCorner, gridStep] at hy
    omega

theorem CorridorRectangle.northCorner_successor (R : CorridorRectangle)
    (hl : 2 < R.left) :
    boundaryDartSuccessorRaw R.augmentedCells R.northCorner = R.westDart R.top := by
  classical
  have hdiag : boundaryForwardDiagonal R.northCorner ∉ R.augmentedCells := by
    intro h
    have hy := (R.augmented_y_bounds ((R.mem_augmentedCells _).mp h)).2
    dsimp [northCorner, boundaryForwardDiagonal, gridDirectionCCW, gridStep] at hy
    omega
  have hside : boundaryForwardSide R.northCorner ∉ R.augmentedCells := by
    intro h
    have hx := R.augmented_x_lower ((R.mem_augmentedCells _).mp h)
    dsimp [northCorner, boundaryForwardSide, gridDirectionCCW, gridStep] at hx
    omega
  simp only [boundaryDartSuccessorRaw, if_neg hdiag, if_neg hside]
  rfl

theorem CorridorRectangle.north_to_south_exterior (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    (boundaryDartSuccessorRaw R.augmentedCells)^[R.top - R.bottom + 2]
      R.northCorner = R.southCorner := by
  rw [show R.top - R.bottom + 2 = (R.top - R.bottom + 1) + 1 by omega,
    Function.iterate_succ_apply, R.northCorner_successor hl,
    Function.iterate_succ_apply', R.westDart_top_to_bottom hl,
    R.westDart_bottom_turn hl (by omega)]
  rfl

theorem CorridorRectangle.south_to_north_orbit (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    ∃ n : ℕ, (boundaryDartSuccessorRaw R.augmentedCells)^[n]
      R.southCorner = R.northCorner := by
  let d : R.augmentedDarts := ⟨R.northCorner,
    (R.mem_augmentedDarts _).mpr (R.northCorner_mem hl)⟩
  obtain ⟨m, hm, _, hperiod⟩ := R.augmented_orbit_returns hl hb d
  have hraw := congrArg Subtype.val hperiod
  rw [R.augmented_iterate_val] at hraw
  let k := R.top - R.bottom + 2
  have hlong : (boundaryDartSuccessorRaw R.augmentedCells)^[m * (k + 1)]
      R.northCorner = R.northCorner :=
    (Function.IsPeriodicPt.mul_const hraw (k + 1)).eq
  have hle : k ≤ m * (k + 1) := by nlinarith
  refine ⟨m * (k + 1) - k, ?_⟩
  rw [← R.north_to_south_exterior hl hb, ← Function.iterate_add_apply]
  change (boundaryDartSuccessorRaw R.augmentedCells)^[m * (k + 1) - k + k]
    R.northCorner = _
  rw [Nat.sub_add_cancel hle]
  exact hlong

end
end Erdos1212Kernel
