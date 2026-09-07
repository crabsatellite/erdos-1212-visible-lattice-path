import Erdos1212Kernel.AlgebraicCorridorWestBoundary
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Erdos1212Kernel
noncomputable section

theorem CorridorRectangle.augmented_iterate_val (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) (d : R.augmentedDarts) (n : ℕ) :
    ((R.augmentedSuccessor hl hb)^[n] d).val =
      (boundaryDartSuccessorRaw R.augmentedCells)^[n] d.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change boundaryDartSuccessorRaw R.augmentedCells
      ((R.augmentedSuccessor hl hb)^[n] d).val = _
    rw [ih]

theorem CorridorRectangle.augmented_raw_iterate_mem (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d) (n : ℕ) :
    R.AugmentedDart ((boundaryDartSuccessorRaw R.augmentedCells)^[n] d) := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact R.augmented_boundary_successor hl hb ih

theorem CorridorRectangle.westDart_raw_period (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    ∃ n : ℕ, 0 < n ∧
      (boundaryDartSuccessorRaw R.augmentedCells)^[n] (R.westDart R.top) =
        R.westDart R.top := by
  let d : R.augmentedDarts := ⟨R.westDart R.top,
    (R.mem_augmentedDarts _).mpr (R.westDart_mem hl ⟨R.vertical, le_rfl⟩)⟩
  obtain ⟨n, hn, _, hreturn⟩ := R.augmented_orbit_returns hl hb d
  refine ⟨n, hn, ?_⟩
  have h := congrArg Subtype.val hreturn
  rw [R.augmented_iterate_val] at h
  exact h

theorem CorridorRectangle.westDart_bottom_to_top (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) :
    ∃ n : ℕ,
      (boundaryDartSuccessorRaw R.augmentedCells)^[n] (R.westDart R.bottom) =
        R.westDart R.top := by
  obtain ⟨m, hm, hperiod⟩ := R.westDart_raw_period hl hb
  let k := R.top - R.bottom
  have hlong : (boundaryDartSuccessorRaw R.augmentedCells)^[m * (k + 1)]
      (R.westDart R.top) = R.westDart R.top :=
    (Function.IsPeriodicPt.mul_const hperiod (k + 1)).eq
  have hle : k ≤ m * (k + 1) := by nlinarith
  refine ⟨m * (k + 1) - k, ?_⟩
  rw [← R.westDart_top_to_bottom hl, ← Function.iterate_add_apply]
  change (boundaryDartSuccessorRaw R.augmentedCells)^[m * (k + 1) - k + k]
    (R.westDart R.top) = _
  rw [Nat.sub_add_cancel hle]
  exact hlong

end
end Erdos1212Kernel
