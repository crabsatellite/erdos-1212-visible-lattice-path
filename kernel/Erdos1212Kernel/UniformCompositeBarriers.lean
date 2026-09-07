import Erdos1212Kernel.ExactBoundaryActiveLabels
import Erdos1212Kernel.UniformCompositeSurvivor

namespace Erdos1212Kernel

/-!
# Composite barrier lines for an actual bounded safe component

Let `Q` be the active boundary-label set of a bounded component.  A composite
coordinate divisible by no prime in `Q` cannot occur on the component
frontier: such a frontier point would be nonvisible, and its least common
prime divisor would belong to `Q` while dividing that coordinate.

If the component touched a whole horizontal or vertical line with this
property, it would propagate forever along the line.  Boundedness therefore
forces the component to avoid every such line.
-/

def horizontalLinePoint (x height : Nat) : LatticePoint :=
  ⟨x, height⟩

def verticalLinePoint (width y : Nat) : LatticePoint :=
  ⟨width, y⟩

theorem composite_one_lt {n : Nat} (hn : Composite n) : 1 < n := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hn
  nlinarith

theorem horizontalLinePoint_not_frontier
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {height x : Nat}
    (hheight : Composite height)
    (hx : 1 < x)
    (havoids : ∀ q ∈ finiteSafeComponentActiveLabels start hbounded,
      ¬ q ∣ height) :
    horizontalLinePoint x height ∉ safeComponentFrontier start := by
  intro hfrontier
  have hnotSafe := safeComponentFrontier_not_safe hfrontier
  have hnotPrimePair : ¬ PrimePair (horizontalLinePoint x height) := by
    rintro ⟨_hxPrime, hheightPrime⟩
    exact (composite_iff_not_prime_of_one_lt (composite_one_lt hheight)).mp
      hheight hheightPrime
  have hnotVisible : ¬ Visible (horizontalLinePoint x height) := by
    intro hvisible
    apply hnotSafe
    apply (safePoint_iff_interiorVisible_not_primePair _).mpr
    exact ⟨⟨hx, composite_one_lt hheight, hvisible⟩, hnotPrimePair⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelMem :
      commonPrimeLabel (horizontalLinePoint x height) ∈
        finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier
      hnotVisible
  exact havoids _ hlabelMem (by simpa [horizontalLinePoint] using hlabelSpec.2.2)

theorem verticalLinePoint_not_frontier
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {width y : Nat}
    (hwidth : Composite width)
    (hy : 1 < y)
    (havoids : ∀ q ∈ finiteSafeComponentActiveLabels start hbounded,
      ¬ q ∣ width) :
    verticalLinePoint width y ∉ safeComponentFrontier start := by
  intro hfrontier
  have hnotSafe := safeComponentFrontier_not_safe hfrontier
  have hnotPrimePair : ¬ PrimePair (verticalLinePoint width y) := by
    rintro ⟨hwidthPrime, _hyPrime⟩
    exact (composite_iff_not_prime_of_one_lt (composite_one_lt hwidth)).mp
      hwidth hwidthPrime
  have hnotVisible : ¬ Visible (verticalLinePoint width y) := by
    intro hvisible
    apply hnotSafe
    apply (safePoint_iff_interiorVisible_not_primePair _).mpr
    exact ⟨⟨composite_one_lt hwidth, hy, hvisible⟩, hnotPrimePair⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelMem :
      commonPrimeLabel (verticalLinePoint width y) ∈
        finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier
      hnotVisible
  exact havoids _ hlabelMem (by simpa [verticalLinePoint] using hlabelSpec.2.1)

theorem horizontalCompositeBarrier_disjoint_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {height : Nat}
    (hheight : Composite height)
    (havoids : ∀ q ∈ finiteSafeComponentActiveLabels start hbounded,
      ¬ q ∣ height) :
    ∀ x, horizontalLinePoint x height ∉ safeComponent start := by
  intro x hxComponent
  apply hbounded
  intro bound
  let point : Nat → LatticePoint := fun n ↦ horizontalLinePoint (x + n) height
  have hpointComponent : ∀ n, point n ∈ safeComponent start := by
    intro n
    induction n with
    | zero => simpa [point, horizontalLinePoint] using hxComponent
    | succ n ih =>
        have hsafe := safePoint_of_mem_safeComponent ih
        have hadjacent : Adjacent (point n) (point (n + 1)) := by
          left
          simp only [point, horizontalLinePoint]
          exact ⟨by omega, trivial⟩
        by_contra hnext
        have hfrontier : point (n + 1) ∈ safeComponentFrontier start :=
          ⟨hnext, point n, ih, hadjacent⟩
        exact horizontalLinePoint_not_frontier hheight
          (x := x + (n + 1)) (by
            have : 1 < (point n).x := hsafe.1
            simp [point, horizontalLinePoint] at this ⊢
            omega)
          havoids hfrontier
  refine ⟨point bound, Or.inl ?_, ?_⟩
  · simp [point, horizontalLinePoint]
  · exact hpointComponent bound

theorem verticalCompositeBarrier_disjoint_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {width : Nat}
    (hwidth : Composite width)
    (havoids : ∀ q ∈ finiteSafeComponentActiveLabels start hbounded,
      ¬ q ∣ width) :
    ∀ y, verticalLinePoint width y ∉ safeComponent start := by
  intro y hyComponent
  apply hbounded
  intro bound
  let point : Nat → LatticePoint := fun n ↦ verticalLinePoint width (y + n)
  have hpointComponent : ∀ n, point n ∈ safeComponent start := by
    intro n
    induction n with
    | zero => simpa [point, verticalLinePoint] using hyComponent
    | succ n ih =>
        have hsafe := safePoint_of_mem_safeComponent ih
        have hadjacent : Adjacent (point n) (point (n + 1)) := by
          right
          right
          left
          simp only [point, verticalLinePoint]
          exact ⟨by omega, trivial⟩
        by_contra hnext
        have hfrontier : point (n + 1) ∈ safeComponentFrontier start :=
          ⟨hnext, point n, ih, hadjacent⟩
        exact verticalLinePoint_not_frontier hwidth
          (y := y + (n + 1)) (by
            have : 1 < (point n).y := hsafe.2.1
            simp [point, verticalLinePoint] at this ⊢
            omega)
          havoids hfrontier
  refine ⟨point bound, Or.inr ?_, ?_⟩
  · simp [point, verticalLinePoint]
  · exact hpointComponent bound

end Erdos1212Kernel
