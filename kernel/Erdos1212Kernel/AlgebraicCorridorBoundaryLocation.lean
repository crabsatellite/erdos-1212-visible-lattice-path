import Erdos1212Kernel.AlgebraicCorridorBoundaryCorners

namespace Erdos1212Kernel
noncomputable section

theorem CorridorRectangle.augmented_x_upper {R : CorridorRectangle}
    {p : LatticePoint} (hp : R.AugmentedLeft p) : p.x ≤ R.right := by
  rcases hp with hp | hp
  · have hx := hp.1
    have h := R.horizontal
    omega
  · exact (R.leftReachable_mem hp).1.2.1

theorem CorridorRectangle.boundary_outside_x_upper (R : CorridorRectangle)
    (hno : ¬R.SafeHorizontalCrossing)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d) :
    (boundaryDartOutside d).x ≤ R.right := by
  have hp := (R.mem_augmentedCells _).mp hd.1
  have hu := R.augmented_x_upper hp
  have hn := R.augmentedLeft_misses_right hno hp
  rcases d with ⟨p, dir⟩
  change p.x ≤ R.right at hu
  change p.x ≠ R.right at hn
  cases dir <;> simp [boundaryDartOutside, gridStep] <;> omega

theorem CorridorRectangle.boundary_left_of_rectangle_is_west (R : CorridorRectangle)
    (hl : 2 < R.left) {d : LatticePoint × GridDirection}
    (hd : R.AugmentedDart d)
    (hy : R.bottom ≤ (boundaryDartOutside d).y ∧
      (boundaryDartOutside d).y ≤ R.top)
    (hx : (boundaryDartOutside d).x < R.left) :
    d = R.westDart (boundaryDartOutside d).y := by
  have hp := (R.mem_augmentedCells _).mp hd.1
  have hmin := R.augmented_x_lower hp
  have hqnot : ¬R.AugmentedLeft (boundaryDartOutside d) :=
    fun h => hd.2 ((R.mem_augmentedCells _).mpr h)
  have hqNe : (boundaryDartOutside d).x + 1 ≠ R.left := by
    intro heq
    exact hqnot (Or.inl ⟨heq, hy⟩)
  rcases d with ⟨p, dir⟩
  change R.left ≤ p.x + 1 at hmin
  cases dir
  · simp [boundaryDartOutside, gridStep] at hx hqNe
    omega
  · have hpEq : p.x = R.left - 1 := by
      simp [boundaryDartOutside, gridStep] at hx hqNe
      omega
    simp [westDart, boundaryDartOutside, gridStep, hpEq]
    exact LatticePoint.ext hpEq rfl
  · simp [boundaryDartOutside, gridStep] at hx hqNe
    omega
  · simp [boundaryDartOutside, gridStep] at hx hqNe
    omega

theorem CorridorRectangle.boundary_inside_of_not_west (R : CorridorRectangle)
    (hl : 2 < R.left) (hno : ¬R.SafeHorizontalCrossing)
    {d : LatticePoint × GridDirection} (hd : R.AugmentedDart d)
    (hy : R.bottom ≤ (boundaryDartOutside d).y ∧
      (boundaryDartOutside d).y ≤ R.top)
    (hn : d ≠ R.westDart (boundaryDartOutside d).y) :
    R.Contains (boundaryDartOutside d) := by
  refine ⟨?_, R.boundary_outside_x_upper hno hd, hy⟩
  by_contra h
  exact hn (R.boundary_left_of_rectangle_is_west hl hd hy (Nat.lt_of_not_ge h))

end
end Erdos1212Kernel
