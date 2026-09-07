import Erdos1212Kernel.UniformCompositeBarriers

namespace Erdos1212Kernel

/-!
# Coordinate crossing inside a safe component

A nearest-neighbour walk cannot cross a horizontal or vertical coordinate
without visiting it.  Applying this discrete intermediate-value fact to the
safe witness walk shows that every coordinate crossed between the root and a
component vertex is itself represented by a vertex of the same component.
-/

theorem adjacent_x_le_succ {p q : LatticePoint} (hpq : Adjacent p q) :
    q.x ≤ p.x + 1 := by
  rcases hpq with h | h | h | h <;> omega

theorem adjacent_y_le_succ {p q : LatticePoint} (hpq : Adjacent p q) :
    q.y ≤ p.y + 1 := by
  rcases hpq with h | h | h | h <;> omega

theorem walk_hits_x_of_crosses_above
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {width : Nat}
    (hstart : start.x < width)
    (hfinish : width ≤ finish.x) :
    ∃ index ≤ walk.length, (walk.getVert index).x = width := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ width ≤ (walk.getVert index).x := by
    exact ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
  let first := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := by omega
    have hle : width ≤ start.x := by
      simpa [first, hzero] using hfirst.2
    omega
  have hpreviousNot : ¬ width ≤ (walk.getVert (first - 1)).x := by
    intro hprevious
    exact (Nat.find_min hexists (by simpa [first] using hfirstPositive))
      ⟨(by omega : first - 1 ≤ walk.length), hprevious⟩
  have hadjacent :
      Adjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : width ≤ (walk.getVert first).x := by
    simpa [first] using hfirst.2
  have hstep := adjacent_x_le_succ hadjacent
  omega

theorem walk_hits_x_of_crosses_below
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {width : Nat}
    (hstart : width < start.x)
    (hfinish : finish.x ≤ width) :
    ∃ index ≤ walk.length, (walk.getVert index).x = width := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ (walk.getVert index).x ≤ width := by
    exact ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
  let first := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := by omega
    have hle : start.x ≤ width := by
      simpa [first, hzero] using hfirst.2
    omega
  have hpreviousNot : ¬ (walk.getVert (first - 1)).x ≤ width := by
    intro hprevious
    exact (Nat.find_min hexists (by simpa [first] using hfirstPositive))
      ⟨(by omega : first - 1 ≤ walk.length), hprevious⟩
  have hadjacent :
      Adjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : (walk.getVert first).x ≤ width := by
    simpa [first] using hfirst.2
  have hstep := adjacent_x_le_succ (adjacent_symm hadjacent)
  omega

theorem walk_hits_y_of_crosses_above
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {height : Nat}
    (hstart : start.y < height)
    (hfinish : height ≤ finish.y) :
    ∃ index ≤ walk.length, (walk.getVert index).y = height := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ height ≤ (walk.getVert index).y := by
    exact ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
  let first := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := by omega
    have hle : height ≤ start.y := by
      simpa [first, hzero] using hfirst.2
    omega
  have hpreviousNot : ¬ height ≤ (walk.getVert (first - 1)).y := by
    intro hprevious
    exact (Nat.find_min hexists (by simpa [first] using hfirstPositive))
      ⟨(by omega : first - 1 ≤ walk.length), hprevious⟩
  have hadjacent :
      Adjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : height ≤ (walk.getVert first).y := by
    simpa [first] using hfirst.2
  have hstep := adjacent_y_le_succ hadjacent
  omega

theorem walk_hits_y_of_crosses_below
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {height : Nat}
    (hstart : height < start.y)
    (hfinish : finish.y ≤ height) :
    ∃ index ≤ walk.length, (walk.getVert index).y = height := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ (walk.getVert index).y ≤ height := by
    exact ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
  let first := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := by omega
    have hle : start.y ≤ height := by
      simpa [first, hzero] using hfirst.2
    omega
  have hpreviousNot : ¬ (walk.getVert (first - 1)).y ≤ height := by
    intro hprevious
    exact (Nat.find_min hexists (by simpa [first] using hfirstPositive))
      ⟨(by omega : first - 1 ≤ walk.length), hprevious⟩
  have hadjacent :
      Adjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : (walk.getVert first).y ≤ height := by
    simpa [first] using hfirst.2
  have hstep := adjacent_y_le_succ (adjacent_symm hadjacent)
  omega

theorem safeComponent_hits_vertical_of_crosses_above
    {start finish : LatticePoint}
    (hfinishComponent : finish ∈ safeComponent start)
    {width : Nat}
    (hstart : start.x < width)
    (hfinish : width ≤ finish.x) :
    ∃ y, verticalLinePoint width y ∈ safeComponent start := by
  obtain ⟨walk, hwalkSafe⟩ := hfinishComponent
  obtain ⟨index, _hindex, hcoordinate⟩ :=
    walk_hits_x_of_crosses_above walk hstart hfinish
  let point := walk.getVert index
  have hpointSupport : point ∈ walk.support := walk.getVert_mem_support index
  have hpointComponent : point ∈ safeComponent start :=
    ⟨walk.takeUntil point hpointSupport,
      fun q hq ↦ hwalkSafe q (walk.support_takeUntil_subset hpointSupport hq)⟩
  refine ⟨point.y, ?_⟩
  have hpointEq : verticalLinePoint width point.y = point := by
    apply LatticePoint.ext
    · simpa [point, verticalLinePoint] using hcoordinate.symm
    · rfl
  rw [hpointEq]
  exact hpointComponent

theorem safeComponent_hits_vertical_of_crosses_below
    {start finish : LatticePoint}
    (hfinishComponent : finish ∈ safeComponent start)
    {width : Nat}
    (hstart : width < start.x)
    (hfinish : finish.x ≤ width) :
    ∃ y, verticalLinePoint width y ∈ safeComponent start := by
  obtain ⟨walk, hwalkSafe⟩ := hfinishComponent
  obtain ⟨index, _hindex, hcoordinate⟩ :=
    walk_hits_x_of_crosses_below walk hstart hfinish
  let point := walk.getVert index
  have hpointSupport : point ∈ walk.support := walk.getVert_mem_support index
  have hpointComponent : point ∈ safeComponent start :=
    ⟨walk.takeUntil point hpointSupport,
      fun q hq ↦ hwalkSafe q (walk.support_takeUntil_subset hpointSupport hq)⟩
  refine ⟨point.y, ?_⟩
  have hpointEq : verticalLinePoint width point.y = point := by
    apply LatticePoint.ext
    · simpa [point, verticalLinePoint] using hcoordinate.symm
    · rfl
  rw [hpointEq]
  exact hpointComponent

theorem safeComponent_hits_horizontal_of_crosses_above
    {start finish : LatticePoint}
    (hfinishComponent : finish ∈ safeComponent start)
    {height : Nat}
    (hstart : start.y < height)
    (hfinish : height ≤ finish.y) :
    ∃ x, horizontalLinePoint x height ∈ safeComponent start := by
  obtain ⟨walk, hwalkSafe⟩ := hfinishComponent
  obtain ⟨index, _hindex, hcoordinate⟩ :=
    walk_hits_y_of_crosses_above walk hstart hfinish
  let point := walk.getVert index
  have hpointSupport : point ∈ walk.support := walk.getVert_mem_support index
  have hpointComponent : point ∈ safeComponent start :=
    ⟨walk.takeUntil point hpointSupport,
      fun q hq ↦ hwalkSafe q (walk.support_takeUntil_subset hpointSupport hq)⟩
  refine ⟨point.x, ?_⟩
  have hpointEq : horizontalLinePoint point.x height = point := by
    apply LatticePoint.ext
    · rfl
    · simpa [point, horizontalLinePoint] using hcoordinate.symm
  rw [hpointEq]
  exact hpointComponent

theorem safeComponent_hits_horizontal_of_crosses_below
    {start finish : LatticePoint}
    (hfinishComponent : finish ∈ safeComponent start)
    {height : Nat}
    (hstart : height < start.y)
    (hfinish : finish.y ≤ height) :
    ∃ x, horizontalLinePoint x height ∈ safeComponent start := by
  obtain ⟨walk, hwalkSafe⟩ := hfinishComponent
  obtain ⟨index, _hindex, hcoordinate⟩ :=
    walk_hits_y_of_crosses_below walk hstart hfinish
  let point := walk.getVert index
  have hpointSupport : point ∈ walk.support := walk.getVert_mem_support index
  have hpointComponent : point ∈ safeComponent start :=
    ⟨walk.takeUntil point hpointSupport,
      fun q hq ↦ hwalkSafe q (walk.support_takeUntil_subset hpointSupport hq)⟩
  refine ⟨point.x, ?_⟩
  have hpointEq : horizontalLinePoint point.x height = point := by
    apply LatticePoint.ext
    · rfl
    · simpa [point, horizontalLinePoint] using hcoordinate.symm
  rw [hpointEq]
  exact hpointComponent

end Erdos1212Kernel
