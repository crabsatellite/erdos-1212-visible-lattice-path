import Erdos1212Kernel.Target
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum

namespace Erdos1212Kernel

open Filter MeasureTheory

/-!
Literal formal statement of Theorem 1.1 of the published paper.
This module states the target; it does not assert a proof of it.
The historical Erdos1212FullClose proposition is weaker, so it is not used
as a replacement for the simple-ray and limiting-direction conclusion.
-/

def algebraicCorridorSlopeInterval : Set ℝ :=
  Set.Ioo (4 / 3 : ℝ) (5 / 3 : ℝ)

def AlgebraicCorridorRayAt (α : ℝ) : Prop :=
  ∃ P : ℕ → LatticePoint,
    Function.Injective P ∧
    (∀ n, SafePoint (P n)) ∧
    (∀ n, Adjacent (P n) (P (n + 1))) ∧
    Tendsto (fun n => (P n).x / ((P n).y : ℝ)) atTop (nhds α)

def AlgebraicCorridorPaperStatement : Prop :=
  ∀ᵐ α : ℝ ∂(volume.restrict algebraicCorridorSlopeInterval),
    AlgebraicCorridorRayAt α

/-- The almost-everywhere target is on a positive-measure real interval, not an empty nat-division interval. -/
theorem algebraicCorridorSlopeInterval_volume_pos :
    0 < volume algebraicCorridorSlopeInterval := by
  norm_num [algebraicCorridorSlopeInterval, Real.volume_Ioo]

end Erdos1212Kernel
