import Erdos1212Kernel.ExplicitFixedRankRootCounting

namespace Erdos1212Kernel

/-!
# Actual-component barrier recruitment

This file records the non-circular exploration principle needed by the exact
rank tail.  Prime--prime vertices are never adjoined to a promoted divisor
component.  Instead, start with any already paid set `R` of prime boundary
labels.  A composite coordinate avoiding every member of `R` is tested as a
literal line in the original safe component.  If the component crosses that
line, the line cannot be a barrier yet, so an actual boundary label outside
`R` must divide its coordinate.

The four directional statements below keep the original component and the
original cut.  Every successful recruitment is a genuine member of
`finiteSafeComponentActiveLabels`, is new relative to `R`, and is read from
the crossed composite coordinate itself.
-/

theorem exists_verticalLine_frontier_above_of_component_meets
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {width y : Nat}
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ frontierY,
      y ≤ frontierY ∧
      verticalLinePoint width frontierY ∈ safeComponentFrontier start := by
  classical
  let point : Nat → LatticePoint :=
    fun n ↦ verticalLinePoint width (y + n)
  have hexists : ∃ n, point n ∉ safeComponent start := by
    by_contra hnone
    push Not at hnone
    apply hbounded
    intro bound
    refine ⟨point bound, Or.inr ?_, hnone bound⟩
    simp [point, verticalLinePoint]
  let first := Nat.find hexists
  have hfirstOutside : point first ∉ safeComponent start :=
    Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnotPositive
    have hfirstZero : first = 0 := by omega
    apply hfirstOutside
    simpa [point, hfirstZero] using hmeets
  have hpreviousInside : point (first - 1) ∈ safeComponent start := by
    by_contra hpreviousOutside
    exact Nat.find_min hexists (by omega) hpreviousOutside
  have hadjacent : Adjacent (point (first - 1)) (point first) := by
    right
    right
    left
    simp only [point, verticalLinePoint]
    constructor
    · omega
    · trivial
  refine ⟨y + first, by omega, ?_⟩
  exact ⟨hfirstOutside, point (first - 1), hpreviousInside, hadjacent⟩

theorem exists_horizontalLine_frontier_right_of_component_meets
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {height x : Nat}
    (hmeets : horizontalLinePoint x height ∈ safeComponent start) :
    ∃ frontierX,
      x ≤ frontierX ∧
      horizontalLinePoint frontierX height ∈ safeComponentFrontier start := by
  classical
  let point : Nat → LatticePoint :=
    fun n ↦ horizontalLinePoint (x + n) height
  have hexists : ∃ n, point n ∉ safeComponent start := by
    by_contra hnone
    push Not at hnone
    apply hbounded
    intro bound
    refine ⟨point bound, Or.inl ?_, hnone bound⟩
    simp [point, horizontalLinePoint]
  let first := Nat.find hexists
  have hfirstOutside : point first ∉ safeComponent start :=
    Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hnotPositive
    have hfirstZero : first = 0 := by omega
    apply hfirstOutside
    simpa [point, hfirstZero] using hmeets
  have hpreviousInside : point (first - 1) ∈ safeComponent start := by
    by_contra hpreviousOutside
    exact Nat.find_min hexists (by omega) hpreviousOutside
  have hadjacent : Adjacent (point (first - 1)) (point first) := by
    left
    simp only [point, horizontalLinePoint]
    constructor
    · omega
    · trivial
  refine ⟨x + first, by omega, ?_⟩
  exact ⟨hfirstOutside, point (first - 1), hpreviousInside, hadjacent⟩

/--
The last component point on an upward vertical ray gives an exterior frontier
site whose remaining ray is disjoint from the component.  This rules out an
internal-hole exit and is the outer-boundary form needed by the paid contour.
-/
theorem exists_verticalLine_outer_frontier_above_of_component_meets
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {width y : Nat}
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ frontierY,
      y ≤ frontierY ∧
      verticalLinePoint width frontierY ∈ safeComponentFrontier start ∧
      (∀ z, frontierY ≤ z →
        verticalLinePoint width z ∉ safeComponent start) := by
  classical
  let sectionPoints :=
    (finiteSafeComponent start hbounded).filter fun point ↦
      point.x = width
  let heights := sectionPoints.image fun point ↦ point.y
  have hyMem : y ∈ heights := by
    apply Finset.mem_image.mpr
    refine ⟨verticalLinePoint width y, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_finiteSafeComponent.mpr hmeets, rfl⟩
  have hnonempty : heights.Nonempty := ⟨y, hyMem⟩
  let last := heights.max' hnonempty
  have hlastMem : last ∈ heights := heights.max'_mem hnonempty
  obtain ⟨point, hpointSection, hpointY⟩ :=
    Finset.mem_image.mp hlastMem
  have hpointData := Finset.mem_filter.mp hpointSection
  have hpointEq : point = verticalLinePoint width last := by
    cases point with
    | mk px py =>
        simp only [LatticePoint.x, LatticePoint.y] at hpointData hpointY
        simp [verticalLinePoint, hpointData.2, hpointY]
  have hlastInside :
      verticalLinePoint width last ∈ safeComponent start := by
    rw [← hpointEq]
    exact mem_finiteSafeComponent.mp hpointData.1
  have htailOutside : ∀ z, last + 1 ≤ z →
      verticalLinePoint width z ∉ safeComponent start := by
    intro z hz hzin
    have hzMem : z ∈ heights := by
      apply Finset.mem_image.mpr
      refine ⟨verticalLinePoint width z, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨mem_finiteSafeComponent.mpr hzin, rfl⟩
    have hzLe : z ≤ last := heights.le_max' z hzMem
    omega
  have hfrontier :
      verticalLinePoint width (last + 1) ∈ safeComponentFrontier start := by
    refine ⟨htailOutside (last + 1) (le_refl _),
      verticalLinePoint width last, hlastInside, ?_⟩
    right
    right
    left
    simp [verticalLinePoint]
  refine ⟨last + 1, ?_, hfrontier, htailOutside⟩
  have hyLe : y ≤ last := heights.le_max' y hyMem
  omega

/--
The first component point on a downward vertical ray gives an exterior
frontier site whose whole remaining ray to the lower boundary is disjoint
from the component.  Unlike an arbitrary deleted vertex on the column, this
site cannot lie on the boundary of a hole surrounded by the component.
-/
theorem exists_verticalLine_outer_frontier_below_of_component_meets
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {width y : Nat}
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ frontierY,
      frontierY ≤ y ∧
      verticalLinePoint width (frontierY + 1) ∈ safeComponent start ∧
      verticalLinePoint width frontierY ∈ safeComponentFrontier start ∧
      (∀ z, z ≤ frontierY →
        verticalLinePoint width z ∉ safeComponent start) := by
  classical
  let sectionPoints :=
    (finiteSafeComponent start hbounded).filter fun point ↦
      point.x = width
  let heights := sectionPoints.image fun point ↦ point.y
  have hyMem : y ∈ heights := by
    apply Finset.mem_image.mpr
    refine ⟨verticalLinePoint width y, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_finiteSafeComponent.mpr hmeets, rfl⟩
  have hnonempty : heights.Nonempty := ⟨y, hyMem⟩
  let first := heights.min' hnonempty
  have hfirstMem : first ∈ heights := heights.min'_mem hnonempty
  obtain ⟨point, hpointSection, hpointY⟩ :=
    Finset.mem_image.mp hfirstMem
  have hpointData := Finset.mem_filter.mp hpointSection
  have hpointEq : point = verticalLinePoint width first := by
    cases point with
    | mk px py =>
        simp only [LatticePoint.x, LatticePoint.y] at hpointData hpointY
        simp [verticalLinePoint, hpointData.2, hpointY]
  have hfirstInside :
      verticalLinePoint width first ∈ safeComponent start := by
    rw [← hpointEq]
    exact mem_finiteSafeComponent.mp hpointData.1
  have hfirstPositive : 0 < first := by
    have hsafe := safePoint_of_mem_safeComponent hfirstInside
    have hfirstGtOne : 1 < first := by
      simpa [verticalLinePoint] using hsafe.2.1
    omega
  have htailOutside : ∀ z, z ≤ first - 1 →
      verticalLinePoint width z ∉ safeComponent start := by
    intro z hz hzin
    have hzMem : z ∈ heights := by
      apply Finset.mem_image.mpr
      refine ⟨verticalLinePoint width z, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨mem_finiteSafeComponent.mpr hzin, rfl⟩
    have hfirstLe : first ≤ z := heights.min'_le z hzMem
    omega
  have hfrontier :
      verticalLinePoint width (first - 1) ∈
        safeComponentFrontier start := by
    refine ⟨htailOutside (first - 1) (le_refl _),
      verticalLinePoint width first, hfirstInside, ?_⟩
    right
    right
    right
    simp only [verticalLinePoint]
    constructor
    · omega
    · trivial
  refine ⟨first - 1, ?_, ?_, hfrontier, htailOutside⟩
  have hfirstLe : first ≤ y := heights.min'_le y hyMem
  omega
  have hsucc : first - 1 + 1 = first := by omega
  simpa [hsucc] using hfirstInside

/-- Rightward outer-ray analogue of
`exists_verticalLine_outer_frontier_above_of_component_meets`. -/
theorem exists_horizontalLine_outer_frontier_right_of_component_meets
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {height x : Nat}
    (hmeets : horizontalLinePoint x height ∈ safeComponent start) :
    ∃ frontierX,
      x ≤ frontierX ∧
      horizontalLinePoint (frontierX - 1) height ∈ safeComponent start ∧
      horizontalLinePoint frontierX height ∈ safeComponentFrontier start ∧
      (∀ z, frontierX ≤ z →
        horizontalLinePoint z height ∉ safeComponent start) := by
  classical
  let sectionPoints :=
    (finiteSafeComponent start hbounded).filter fun point ↦
      point.y = height
  let widths := sectionPoints.image fun point ↦ point.x
  have hxMem : x ∈ widths := by
    apply Finset.mem_image.mpr
    refine ⟨horizontalLinePoint x height, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_finiteSafeComponent.mpr hmeets, rfl⟩
  have hnonempty : widths.Nonempty := ⟨x, hxMem⟩
  let last := widths.max' hnonempty
  have hlastMem : last ∈ widths := widths.max'_mem hnonempty
  obtain ⟨point, hpointSection, hpointX⟩ :=
    Finset.mem_image.mp hlastMem
  have hpointData := Finset.mem_filter.mp hpointSection
  have hpointEq : point = horizontalLinePoint last height := by
    cases point with
    | mk px py =>
        simp only [LatticePoint.x, LatticePoint.y] at hpointData hpointX
        simp [horizontalLinePoint, hpointData.2, hpointX]
  have hlastInside :
      horizontalLinePoint last height ∈ safeComponent start := by
    rw [← hpointEq]
    exact mem_finiteSafeComponent.mp hpointData.1
  have htailOutside : ∀ z, last + 1 ≤ z →
      horizontalLinePoint z height ∉ safeComponent start := by
    intro z hz hzin
    have hzMem : z ∈ widths := by
      apply Finset.mem_image.mpr
      refine ⟨horizontalLinePoint z height, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨mem_finiteSafeComponent.mpr hzin, rfl⟩
    have hzLe : z ≤ last := widths.le_max' z hzMem
    omega
  have hfrontier :
      horizontalLinePoint (last + 1) height ∈
        safeComponentFrontier start := by
    refine ⟨htailOutside (last + 1) (le_refl _),
      horizontalLinePoint last height, hlastInside, ?_⟩
    left
    simp [horizontalLinePoint]
  refine ⟨last + 1, ?_, ?_, hfrontier, htailOutside⟩
  have hxLe : x ≤ last := widths.le_max' x hxMem
  omega
  simpa using hlastInside

theorem exists_fresh_activeLabel_site_of_verticalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {width y : Nat}
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width)
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ site q,
      site ∈ safeComponentFrontier start ∧
      site.x = width ∧
      q = commonPrimeLabel site ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ site.x ∧ q ∣ site.y := by
  obtain ⟨frontierY, hyLe, hfrontier⟩ :=
    exists_verticalLine_frontier_above_of_component_meets
      (hbounded := hbounded) hmeets
  let site := verticalLinePoint width frontierY
  have hsiteEq : site = verticalLinePoint width frontierY := rfl
  have hyStart : 1 < y :=
    (safePoint_of_mem_safeComponent hmeets).2.1
  have hySite : 1 < site.y := by
    simp only [site, verticalLinePoint]
    omega
  have hxSite : 1 < site.x := by
    simpa [site, verticalLinePoint] using composite_one_lt hwidth
  have hnotVisible : ¬ Visible site := by
    intro hvisible
    exact safeComponentFrontier_not_safe hfrontier
      ⟨hxSite, hySite, hvisible, Or.inl (by
        simpa [site, verticalLinePoint] using hwidth)⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelActive :
      commonPrimeLabel site ∈ finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier hnotVisible
  have hlabelFresh : commonPrimeLabel site ∉ R := by
    intro hmem
    exact havoids _ hmem (by
      simpa [site, verticalLinePoint] using hlabelSpec.2.1)
  exact ⟨site, commonPrimeLabel site, hfrontier, by rfl, rfl,
    hlabelActive, hlabelFresh, hlabelSpec.2.1, hlabelSpec.2.2⟩

theorem exists_fresh_activeLabel_site_of_horizontalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {height x : Nat}
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height)
    (hmeets : horizontalLinePoint x height ∈ safeComponent start) :
    ∃ site q,
      site ∈ safeComponentFrontier start ∧
      site.y = height ∧
      q = commonPrimeLabel site ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ site.x ∧ q ∣ site.y := by
  obtain ⟨frontierX, hxLe, hfrontier⟩ :=
    exists_horizontalLine_frontier_right_of_component_meets
      (hbounded := hbounded) hmeets
  let site := horizontalLinePoint frontierX height
  have hxStart : 1 < x :=
    (safePoint_of_mem_safeComponent hmeets).1
  have hxSite : 1 < site.x := by
    simp only [site, horizontalLinePoint]
    omega
  have hySite : 1 < site.y := by
    simpa [site, horizontalLinePoint] using composite_one_lt hheight
  have hnotVisible : ¬ Visible site := by
    intro hvisible
    exact safeComponentFrontier_not_safe hfrontier
      ⟨hxSite, hySite, hvisible, Or.inr (by
        simpa [site, horizontalLinePoint] using hheight)⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelActive :
      commonPrimeLabel site ∈ finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier hnotVisible
  have hlabelFresh : commonPrimeLabel site ∉ R := by
    intro hmem
    exact havoids _ hmem (by
      simpa [site, horizontalLinePoint] using hlabelSpec.2.2)
  exact ⟨site, commonPrimeLabel site, hfrontier, by rfl, rfl,
    hlabelActive, hlabelFresh, hlabelSpec.2.1, hlabelSpec.2.2⟩

theorem exists_outer_fresh_activeLabel_site_of_verticalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {width y : Nat}
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width)
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ site q,
      site ∈ safeComponentFrontier start ∧
      site.x = width ∧
      q = commonPrimeLabel site ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ site.x ∧ q ∣ site.y ∧
      (∀ z, site.y ≤ z →
        verticalLinePoint site.x z ∉ safeComponent start) := by
  obtain ⟨frontierY, hyLe, hfrontier, htail⟩ :=
    exists_verticalLine_outer_frontier_above_of_component_meets
      (hbounded := hbounded) hmeets
  let site := verticalLinePoint width frontierY
  have hyStart : 1 < y :=
    (safePoint_of_mem_safeComponent hmeets).2.1
  have hySite : 1 < site.y := by
    simp only [site, verticalLinePoint]
    omega
  have hxSite : 1 < site.x := by
    simpa [site, verticalLinePoint] using composite_one_lt hwidth
  have hnotVisible : ¬ Visible site := by
    intro hvisible
    exact safeComponentFrontier_not_safe hfrontier
      ⟨hxSite, hySite, hvisible, Or.inl (by
        simpa [site, verticalLinePoint] using hwidth)⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelActive :
      commonPrimeLabel site ∈ finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier hnotVisible
  have hlabelFresh : commonPrimeLabel site ∉ R := by
    intro hmem
    exact havoids _ hmem (by
      simpa [site, verticalLinePoint] using hlabelSpec.2.1)
  refine ⟨site, commonPrimeLabel site, hfrontier, rfl, rfl,
    hlabelActive, hlabelFresh, hlabelSpec.2.1, hlabelSpec.2.2, ?_⟩
  intro z hz
  simpa [site, verticalLinePoint] using htail z hz

theorem exists_outer_fresh_activeLabel_site_of_horizontalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {height x : Nat}
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height)
    (hmeets : horizontalLinePoint x height ∈ safeComponent start) :
    ∃ site q,
      site ∈ safeComponentFrontier start ∧
      site.y = height ∧
      q = commonPrimeLabel site ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ site.x ∧ q ∣ site.y ∧
      (∀ z, site.x ≤ z →
        horizontalLinePoint z site.y ∉ safeComponent start) := by
  obtain ⟨frontierX, hxLe, _hinside, hfrontier, htail⟩ :=
    exists_horizontalLine_outer_frontier_right_of_component_meets
      (hbounded := hbounded) hmeets
  let site := horizontalLinePoint frontierX height
  have hxStart : 1 < x :=
    (safePoint_of_mem_safeComponent hmeets).1
  have hxSite : 1 < site.x := by
    simp only [site, horizontalLinePoint]
    omega
  have hySite : 1 < site.y := by
    simpa [site, horizontalLinePoint] using composite_one_lt hheight
  have hnotVisible : ¬ Visible site := by
    intro hvisible
    exact safeComponentFrontier_not_safe hfrontier
      ⟨hxSite, hySite, hvisible, Or.inr (by
        simpa [site, horizontalLinePoint] using hheight)⟩
  have hlabelSpec := commonPrimeLabel_spec_of_not_visible hnotVisible
  have hlabelActive :
      commonPrimeLabel site ∈ finiteSafeComponentActiveLabels start hbounded :=
    commonPrimeLabel_mem_activeLabels_of_frontier hfrontier hnotVisible
  have hlabelFresh : commonPrimeLabel site ∉ R := by
    intro hmem
    exact havoids _ hmem (by
      simpa [site, horizontalLinePoint] using hlabelSpec.2.2)
  refine ⟨site, commonPrimeLabel site, hfrontier, rfl, rfl,
    hlabelActive, hlabelFresh, hlabelSpec.2.1, hlabelSpec.2.2, ?_⟩
  intro z hz
  simpa [site, horizontalLinePoint] using htail z hz

theorem exists_fresh_activeLabel_of_verticalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {width y : Nat}
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width)
    (hmeets : verticalLinePoint width y ∈ safeComponent start) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ width := by
  obtain ⟨_site, q, _hfrontier, _hx, _hlabel,
      hqActive, hqFresh, hqx, _hqy⟩ :=
    exists_fresh_activeLabel_site_of_verticalLine_meets_component
      hwidth havoids hmeets
  exact ⟨q, hqActive, hqFresh, by simpa [_hx] using hqx⟩

theorem exists_fresh_activeLabel_of_horizontalLine_meets_component
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {height x : Nat}
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height)
    (hmeets : horizontalLinePoint x height ∈ safeComponent start) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ height := by
  obtain ⟨_site, q, _hfrontier, _hy, _hlabel,
      hqActive, hqFresh, _hqx, hqy⟩ :=
    exists_fresh_activeLabel_site_of_horizontalLine_meets_component
      hheight havoids hmeets
  exact ⟨q, hqActive, hqFresh, by simpa [_hy] using hqy⟩

theorem component_crosses_upper_vertical_recruits
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {width : Nat}
    (hfinish : finish ∈ safeComponent start)
    (hstart : start.x < width)
    (hcross : width ≤ finish.x)
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ width := by
  obtain ⟨y, hy⟩ :=
    safeComponent_hits_vertical_of_crosses_above hfinish hstart hcross
  exact exists_fresh_activeLabel_of_verticalLine_meets_component
    hwidth havoids hy

theorem component_crosses_lower_vertical_recruits
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {width : Nat}
    (hfinish : finish ∈ safeComponent start)
    (hstart : width < start.x)
    (hcross : finish.x ≤ width)
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ width := by
  obtain ⟨y, hy⟩ :=
    safeComponent_hits_vertical_of_crosses_below hfinish hstart hcross
  exact exists_fresh_activeLabel_of_verticalLine_meets_component
    hwidth havoids hy

theorem component_crosses_upper_horizontal_recruits
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {height : Nat}
    (hfinish : finish ∈ safeComponent start)
    (hstart : start.y < height)
    (hcross : height ≤ finish.y)
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ height := by
  obtain ⟨x, hx⟩ :=
    safeComponent_hits_horizontal_of_crosses_above hfinish hstart hcross
  exact exists_fresh_activeLabel_of_horizontalLine_meets_component
    hheight havoids hx

theorem component_crosses_lower_horizontal_recruits
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {height : Nat}
    (hfinish : finish ∈ safeComponent start)
    (hstart : height < start.y)
    (hcross : finish.y ≤ height)
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded,
      q ∉ R ∧ q ∣ height := by
  obtain ⟨x, hx⟩ :=
    safeComponent_hits_horizontal_of_crosses_below hfinish hstart hcross
  exact exists_fresh_activeLabel_of_horizontalLine_meets_component
    hheight havoids hx

/-! ## Quantitative one-step recruitment -/

theorem exists_fresh_activeLabel_of_component_far_right
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge : Nat.nth Nat.Prime H ≤ start.x)
    (hfinish : finish ∈ safeComponent start)
    (hfar : start.x + uniformCompositeSurvivorGap H < finish.x) :
    ∃ width q,
      start.x < width ∧
      width ≤ start.x + uniformCompositeSurvivorGap H ∧
      Composite width ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ width := by
  obtain ⟨width, hwidthGt, hwidthLe, hwidthComposite, hwidthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.x) (Q := R) hcard hprime hxLarge
  have hcross : width ≤ finish.x := hwidthLe.trans (Nat.le_of_lt hfar)
  obtain ⟨q, hqActive, hqFresh, hqDvd⟩ :=
    component_crosses_upper_vertical_recruits
      hfinish hwidthGt hcross hwidthComposite hwidthAvoids
  exact ⟨width, q, hwidthGt, hwidthLe, hwidthComposite,
    hqActive, hqFresh, hqDvd⟩

theorem exists_fresh_activeLabel_of_component_far_left
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hfinish : finish ∈ safeComponent start)
    (hfar : finish.x + uniformCompositeSurvivorGap H < start.x) :
    ∃ width q,
      width < start.x ∧
      start.x ≤ width + uniformCompositeSurvivorGap H ∧
      Composite width ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ width := by
  let gap := uniformCompositeSurvivorGap H
  let lowerBase := start.x - gap - 1
  have hnth : Nat.nth Nat.Prime H ≤ lowerBase := by
    dsimp [lowerBase, gap] at hxLarge ⊢
    omega
  obtain ⟨width, hwidthGt, hwidthLe, hwidthComposite, hwidthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerBase) (Q := R) hcard hprime hnth
  have hwidthLt : width < start.x := by
    change width ≤ lowerBase + gap at hwidthLe
    dsimp [lowerBase, gap] at hwidthLe hxLarge
    omega
  have hcross : finish.x ≤ width := by
    dsimp [lowerBase, gap] at hwidthGt hfar ⊢
    omega
  obtain ⟨q, hqActive, hqFresh, hqDvd⟩ :=
    component_crosses_lower_vertical_recruits
      hfinish hwidthLt hcross hwidthComposite hwidthAvoids
  refine ⟨width, q, hwidthLt, ?_, hwidthComposite,
    hqActive, hqFresh, hqDvd⟩
  dsimp [lowerBase, gap] at hxLarge hwidthGt ⊢
  omega

theorem exists_fresh_activeLabel_of_component_far_above
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hyLarge : Nat.nth Nat.Prime H ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (hfar : start.y + uniformCompositeSurvivorGap H < finish.y) :
    ∃ height q,
      start.y < height ∧
      height ≤ start.y + uniformCompositeSurvivorGap H ∧
      Composite height ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ height := by
  obtain ⟨height, hheightGt, hheightLe, hheightComposite, hheightAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.y) (Q := R) hcard hprime hyLarge
  have hcross : height ≤ finish.y := hheightLe.trans (Nat.le_of_lt hfar)
  obtain ⟨q, hqActive, hqFresh, hqDvd⟩ :=
    component_crosses_upper_horizontal_recruits
      hfinish hheightGt hcross hheightComposite hheightAvoids
  exact ⟨height, q, hheightGt, hheightLe, hheightComposite,
    hqActive, hqFresh, hqDvd⟩

theorem exists_fresh_activeLabel_of_component_far_below
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (hfar : finish.y + uniformCompositeSurvivorGap H < start.y) :
    ∃ height q,
      height < start.y ∧
      start.y ≤ height + uniformCompositeSurvivorGap H ∧
      Composite height ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧ q ∣ height := by
  let gap := uniformCompositeSurvivorGap H
  let lowerBase := start.y - gap - 1
  have hnth : Nat.nth Nat.Prime H ≤ lowerBase := by
    dsimp [lowerBase, gap] at hyLarge ⊢
    omega
  obtain ⟨height, hheightGt, hheightLe, hheightComposite, hheightAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerBase) (Q := R) hcard hprime hnth
  have hheightLt : height < start.y := by
    change height ≤ lowerBase + gap at hheightLe
    dsimp [lowerBase, gap] at hheightLe hyLarge
    omega
  have hcross : finish.y ≤ height := by
    dsimp [lowerBase, gap] at hheightGt hfar ⊢
    omega
  obtain ⟨q, hqActive, hqFresh, hqDvd⟩ :=
    component_crosses_lower_horizontal_recruits
      hfinish hheightLt hcross hheightComposite hheightAvoids
  refine ⟨height, q, hheightLt, ?_, hheightComposite,
    hqActive, hqFresh, hqDvd⟩
  dsimp [lowerBase, gap] at hyLarge hheightGt ⊢
  omega

/--
If an actual component vertex leaves the current rank window, one of the four
nearby composite survivor lines recruits a previously unpaid actual boundary
label.  This is the finite-step alternative used by the without-replacement
rank exploration; prime--prime sites never enter its state.
-/
theorem component_outside_current_rank_window_recruits
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (houtside :
      start.x + uniformCompositeSurvivorGap H < finish.x ∨
      finish.x + uniformCompositeSurvivorGap H < start.x ∨
      start.y + uniformCompositeSurvivorGap H < finish.y ∨
      finish.y + uniformCompositeSurvivorGap H < start.y) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded, q ∉ R := by
  rcases houtside with hright | hleft | habove | hbelow
  · obtain ⟨_width, q, _hgt, _hle, _hcomp, hqActive, hqFresh, _hdiv⟩ :=
      exists_fresh_activeLabel_of_component_far_right hcard hprime
        (by omega) hfinish hright
    exact ⟨q, hqActive, hqFresh⟩
  · obtain ⟨_width, q, _hlt, _hle, _hcomp, hqActive, hqFresh, _hdiv⟩ :=
      exists_fresh_activeLabel_of_component_far_left hcard hprime
        hxLarge hfinish hleft
    exact ⟨q, hqActive, hqFresh⟩
  · obtain ⟨_height, q, _hgt, _hle, _hcomp, hqActive, hqFresh, _hdiv⟩ :=
      exists_fresh_activeLabel_of_component_far_above hcard hprime
        (by omega) hfinish habove
    exact ⟨q, hqActive, hqFresh⟩
  · obtain ⟨_height, q, _hlt, _hle, _hcomp, hqActive, hqFresh, _hdiv⟩ :=
      exists_fresh_activeLabel_of_component_far_below hcard hprime
        hyLarge hfinish hbelow
    exact ⟨q, hqActive, hqFresh⟩

/-! ## Finite without-replacement history -/

/-- Every vertex of the actual component lies in the symmetric coordinate
window of radius `gap` around its root. -/
def SafeComponentConfinedWithin (start : LatticePoint) (gap : Nat) : Prop :=
  ∀ finish, finish ∈ safeComponent start →
    finish.x ≤ start.x + gap ∧
    start.x ≤ finish.x + gap ∧
    finish.y ≤ start.y + gap ∧
    start.y ≤ finish.y + gap

theorem frontier_mem_latticeWindow_of_component_confined
    {start site : LatticePoint} {gap : Nat}
    (hconfined : SafeComponentConfinedWithin start gap)
    (hfrontier : site ∈ safeComponentFrontier start) :
    site ∈ latticeWindow start (gap + 1) := by
  obtain ⟨_houtside, predecessor, hpredecessor, hadjacent⟩ := hfrontier
  have hpredecessorBounds := hconfined predecessor hpredecessor
  have hsiteXStep := adjacent_x_le_succ hadjacent
  have hpredecessorXStep := adjacent_x_le_succ (adjacent_symm hadjacent)
  have hsiteYStep := adjacent_y_le_succ hadjacent
  have hpredecessorYStep := adjacent_y_le_succ (adjacent_symm hadjacent)
  apply mem_latticeWindow.mpr
  omega

/-- Every exact nonpermanent label of a confined actual component has a
literal labelled frontier site in the corresponding finite relative window. -/
theorem exactBoundaryLabel_has_local_frontierSite
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {gap q : Nat}
    (hconfined : SafeComponentConfinedWithin start gap)
    (hq : q ∈ exactNonpermanentBoundaryLabels start hbounded) :
    ∃ site ∈ latticeWindow start (gap + 1),
      site ∈ safeComponentFrontier start ∧ commonPrimeLabel site = q := by
  obtain ⟨hqImage, _hqLarge⟩ := Finset.mem_filter.mp hq
  obtain ⟨site, hsiteFiniteFrontier, hsiteLabel⟩ :=
    Finset.mem_image.mp hqImage
  have hsiteFrontier : site ∈ safeComponentFrontier start :=
    mem_finiteSafeComponentFrontier.mp hsiteFiniteFrontier
  exact ⟨site,
    frontier_mem_latticeWindow_of_component_confined hconfined hsiteFrontier,
    hsiteFrontier, hsiteLabel⟩

theorem exactBoundaryLabelRank_le_window_card_of_confined
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {gap : Nat}
    (hconfined : SafeComponentConfinedWithin start gap) :
    exactBoundaryLabelRank start ≤ (latticeWindow start (gap + 1)).card := by
  rw [exactBoundaryLabelRank_eq_card hbounded]
  let frontier := finiteSafeComponentFrontier start hbounded
  have hfrontierSubset : frontier ⊆ latticeWindow start (gap + 1) := by
    intro site hsite
    apply frontier_mem_latticeWindow_of_component_confined hconfined
    exact mem_finiteSafeComponentFrontier.mp hsite
  calc
    (exactNonpermanentBoundaryLabels start hbounded).card
        ≤ (frontier.image commonPrimeLabel).card := by
          exact Finset.card_filter_le _ _
    _ ≤ frontier.card := Finset.card_image_le
    _ ≤ (latticeWindow start (gap + 1)).card :=
      Finset.card_le_card hfrontierSubset

theorem exactBoundaryLabelRank_le_window_square_of_confined
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {gap : Nat}
    (hconfined : SafeComponentConfinedWithin start gap) :
    exactBoundaryLabelRank start ≤ (2 * (gap + 1) + 1) ^ 2 :=
  (exactBoundaryLabelRank_le_window_card_of_confined
    (hbounded := hbounded) hconfined).trans
      (latticeWindow_card_le start (gap + 1))

theorem exists_fresh_activeLabel_of_not_confined_current_rank_window
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hnotConfined :
      ¬ SafeComponentConfinedWithin start (uniformCompositeSurvivorGap H)) :
    ∃ q ∈ finiteSafeComponentActiveLabels start hbounded, q ∉ R := by
  classical
  by_contra hnone
  push Not at hnone
  apply hnotConfined
  intro finish hfinish
  have hnotOutside :
      ¬ (start.x + uniformCompositeSurvivorGap H < finish.x ∨
        finish.x + uniformCompositeSurvivorGap H < start.x ∨
        start.y + uniformCompositeSurvivorGap H < finish.y ∨
        finish.y + uniformCompositeSurvivorGap H < start.y) := by
    intro houtside
    obtain ⟨q, hqActive, hqFresh⟩ :=
      component_outside_current_rank_window_recruits
        hcard hprime hxLarge hyLarge hfinish houtside
    exact hqFresh (hnone q hqActive)
  simp only [not_or] at hnotOutside
  rcases hnotOutside with ⟨hxUpper, hxLower, hyUpper, hyLower⟩
  omega

/-- Insert the labels of a recruitment word into its initial paid state. -/
def recruitedLabelSet : Finset Nat → List Nat → Finset Nat
  | R, [] => R
  | R, q :: history => recruitedLabelSet (insert q R) history

/--
An exact recruitment history.  Before every insertion the actual component
escapes the current composite-survivor window; the inserted label is an
actual active boundary label and has not appeared earlier in the history.
-/
def ActualRankRecruitmentHistory
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    Finset Nat → List Nat → Prop
  | _R, [] => True
  | R, q :: history =>
      ¬ SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap R.card) ∧
      q ∈ finiteSafeComponentActiveLabels start hbounded ∧
      q ∉ R ∧
      ActualRankRecruitmentHistory start hbounded (insert q R) history

theorem ActualRankRecruitmentHistory.labels_mem_active
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded R history) :
    ∀ q ∈ history, q ∈ finiteSafeComponentActiveLabels start hbounded := by
  induction history generalizing R with
  | nil => simp
  | cons q history ih =>
      rcases hhistory with ⟨_hnot, hqActive, _hqFresh, htail⟩
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hqActive
      · exact ih htail r hr

theorem ActualRankRecruitmentHistory.labels_fresh_from_initial
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded R history) :
    ∀ q ∈ history, q ∉ R := by
  induction history generalizing R with
  | nil => simp
  | cons q history ih =>
      rcases hhistory with ⟨_hnot, _hqActive, hqFresh, htail⟩
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hqFresh
      · have hrFresh := ih htail r hr
        exact fun hrR ↦ hrFresh (Finset.mem_insert_of_mem hrR)

theorem ActualRankRecruitmentHistory.nodup
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded R history) :
    history.Nodup := by
  induction history generalizing R with
  | nil => exact List.nodup_nil
  | cons q history ih =>
      rcases hhistory with ⟨hnot, hqActive, hqFresh, htail⟩
      apply List.nodup_cons.mpr
      refine ⟨?_, ih htail⟩
      intro hqTail
      have hqNotInserted :=
        ActualRankRecruitmentHistory.labels_fresh_from_initial htail q hqTail
      exact hqNotInserted (Finset.mem_insert_self q R)

theorem recruitedLabelSet_eq_union_toFinset
    (R : Finset Nat) (history : List Nat) :
    recruitedLabelSet R history = R ∪ history.toFinset := by
  induction history generalizing R with
  | nil => simp [recruitedLabelSet]
  | cons q history ih =>
      simp only [recruitedLabelSet, ih, List.toFinset_cons]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

theorem ActualRankRecruitmentHistory.length_le_activeLabel_card
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded R history) :
    history.length ≤
      (finiteSafeComponentActiveLabels start hbounded).card := by
  have hsubset : history.toFinset ⊆
      finiteSafeComponentActiveLabels start hbounded := by
    intro q hq
    exact hhistory.labels_mem_active q (List.mem_toFinset.mp hq)
  have hcard := Finset.card_le_card hsubset
  simpa [List.toFinset_card_of_nodup hhistory.nodup] using hcard

theorem ActualRankRecruitmentHistory.recruitedLabelSet_card
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded R history) :
    (recruitedLabelSet R history).card = R.card + history.length := by
  rw [recruitedLabelSet_eq_union_toFinset]
  have hdisjoint : Disjoint R history.toFinset := by
    rw [Finset.disjoint_left]
    intro q hqR hqHistory
    exact hhistory.labels_fresh_from_initial q
      (List.mem_toFinset.mp hqHistory) hqR
  rw [Finset.card_union_of_disjoint hdisjoint]
  simp [List.toFinset_card_of_nodup hhistory.nodup]

theorem ActualRankRecruitmentHistory.length_le_exactBoundaryLabelRank
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {history : List Nat}
    (hhistory :
      ActualRankRecruitmentHistory start hbounded (Nat.primesLE 11) history) :
    history.length ≤ exactBoundaryLabelRank start := by
  have hsubset :
      history.toFinset ⊆ exactNonpermanentBoundaryLabels start hbounded := by
    intro q hqHistory
    have hqList : q ∈ history := List.mem_toFinset.mp hqHistory
    have hqActive := hhistory.labels_mem_active q hqList
    have hqFresh := hhistory.labels_fresh_from_initial q hqList
    rcases Finset.mem_union.mp hqActive with hqExact | hqPermanent
    · exact hqExact
    · exact False.elim (hqFresh hqPermanent)
  have hcard := Finset.card_le_card hsubset
  rw [exactBoundaryLabelRank_eq_card hbounded]
  simpa [List.toFinset_card_of_nodup hhistory.nodup] using hcard

/--
Starting from any paid subset of the actual active labels, repeated literal
barrier crossings produce a finite without-replacement history and terminate
at a window containing the whole original safe component.  Termination is by
the number of actual active labels not yet paid.  Prime--prime vertices do not
belong to the state or to the termination measure.
-/
theorem exists_complete_actualRankRecruitmentHistory
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (R₀ : Finset Nat)
    (hR₀ : R₀ ⊆ finiteSafeComponentActiveLabels start hbounded)
    (hxLarge :
      Nat.nth Nat.Prime
            (finiteSafeComponentActiveLabels start hbounded).card +
          uniformCompositeSurvivorGap
            (finiteSafeComponentActiveLabels start hbounded).card + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime
            (finiteSafeComponentActiveLabels start hbounded).card +
          uniformCompositeSurvivorGap
            (finiteSafeComponentActiveLabels start hbounded).card + 1 ≤ start.y) :
    ∃ history,
      ActualRankRecruitmentHistory start hbounded R₀ history ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap
          (recruitedLabelSet R₀ history).card) := by
  classical
  let Q := finiteSafeComponentActiveLabels start hbounded
  have hQPrime : ∀ q ∈ Q, Nat.Prime q := by
    intro q hq
    exact finiteSafeComponentActiveLabel_prime hq
  let rec go (R : Finset Nat) (hRQ : R ⊆ Q) :
      ∃ history,
        ActualRankRecruitmentHistory start hbounded R history ∧
        SafeComponentConfinedWithin start
          (uniformCompositeSurvivorGap
            (recruitedLabelSet R history).card) := by
    by_cases hterminal :
        SafeComponentConfinedWithin start
          (uniformCompositeSurvivorGap R.card)
    · exact ⟨[], trivial, hterminal⟩
    · have hcardRQ : R.card ≤ Q.card := Finset.card_le_card hRQ
      have hxCurrent :
          Nat.nth Nat.Prime R.card +
              uniformCompositeSurvivorGap R.card + 1 ≤ start.x := by
        have hnth : Nat.nth Nat.Prime R.card ≤ Nat.nth Nat.Prime Q.card :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcardRQ
        have hgap :
            uniformCompositeSurvivorGap R.card ≤
              uniformCompositeSurvivorGap Q.card :=
          uniformCompositeSurvivorGap_mono hcardRQ
        have hxMax := hxLarge
        change Nat.nth Nat.Prime Q.card +
            uniformCompositeSurvivorGap Q.card + 1 ≤ start.x at hxMax
        omega
      have hyCurrent :
          Nat.nth Nat.Prime R.card +
              uniformCompositeSurvivorGap R.card + 1 ≤ start.y := by
        have hnth : Nat.nth Nat.Prime R.card ≤ Nat.nth Nat.Prime Q.card :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcardRQ
        have hgap :
            uniformCompositeSurvivorGap R.card ≤
              uniformCompositeSurvivorGap Q.card :=
          uniformCompositeSurvivorGap_mono hcardRQ
        have hyMax := hyLarge
        change Nat.nth Nat.Prime Q.card +
            uniformCompositeSurvivorGap Q.card + 1 ≤ start.y at hyMax
        omega
      have hRPrime : ∀ q ∈ R, Nat.Prime q := by
        intro q hq
        exact hQPrime q (hRQ hq)
      obtain ⟨q, hqQ, hqFresh⟩ :=
        exists_fresh_activeLabel_of_not_confined_current_rank_window
          (H := R.card) (R := R) (le_refl _) hRPrime
          hxCurrent hyCurrent hterminal
      have hnextSubset : insert q R ⊆ Q := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hqQ
        · exact hRQ hxR
      obtain ⟨history, hhistory, hfinal⟩ := go (insert q R) hnextSubset
      refine ⟨q :: history, ?_, ?_⟩
      · exact ⟨hterminal, hqQ, hqFresh, hhistory⟩
      · exact hfinal
  termination_by
    (finiteSafeComponentActiveLabels start hbounded \ R).card
  decreasing_by
    rw [Finset.sdiff_insert]
    exact Finset.card_erase_lt_of_mem
      (Finset.mem_sdiff.mpr ⟨by simpa [Q] using hqQ, hqFresh⟩)
  simpa [Q] using go R₀ hR₀

/--
Concrete exact-rank form of the history theorem.  Starting with precisely the
five permanent labels, the adaptive history has at most the actual
nonpermanent rank `K`; after `m` recruitments the whole component is confined
by the survivor gap for exactly `m + 5` paid labels.
-/
theorem exists_complete_exactRankRecruitmentHistory
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y) :
    ∃ history,
      ActualRankRecruitmentHistory start hbounded (Nat.primesLE 11) history ∧
      history.Nodup ∧
      history.length ≤ K ∧
      (recruitedLabelSet (Nat.primesLE 11) history).card =
        history.length + 5 ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap (history.length + 5)) := by
  classical
  let Q := finiteSafeComponentActiveLabels start hbounded
  have hQCard : Q.card ≤ K + 5 := by
    dsimp [Q]
    simpa [hrank] using
      finiteSafeComponentActiveLabels_card_le_rank_add_five start hbounded
  have hxQ :
      Nat.nth Nat.Prime Q.card + uniformCompositeSurvivorGap Q.card + 1 ≤
        start.x := by
    have hnth : Nat.nth Nat.Prime Q.card ≤ Nat.nth Nat.Prime (K + 5) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hQCard
    have hgap : uniformCompositeSurvivorGap Q.card ≤
        uniformCompositeSurvivorGap (K + 5) :=
      uniformCompositeSurvivorGap_mono hQCard
    dsimp [componentRankThreshold, componentRankGap] at hxLarge
    omega
  have hyQ :
      Nat.nth Nat.Prime Q.card + uniformCompositeSurvivorGap Q.card + 1 ≤
        start.y := by
    have hnth : Nat.nth Nat.Prime Q.card ≤ Nat.nth Nat.Prime (K + 5) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hQCard
    have hgap : uniformCompositeSurvivorGap Q.card ≤
        uniformCompositeSurvivorGap (K + 5) :=
      uniformCompositeSurvivorGap_mono hQCard
    dsimp [componentRankThreshold, componentRankGap] at hyLarge
    omega
  have hpermanent : Nat.primesLE 11 ⊆ Q := by
    intro q hq
    exact Finset.mem_union_right _ hq
  obtain ⟨history, hhistory, hconfined⟩ :=
    exists_complete_actualRankRecruitmentHistory
      (hbounded := hbounded) (Nat.primesLE 11)
      (by simpa [Q] using hpermanent)
      (by simpa [Q] using hxQ) (by simpa [Q] using hyQ)
  have hnodup := hhistory.nodup
  have hlength := hhistory.length_le_exactBoundaryLabelRank
  have hcardFinal :
      (recruitedLabelSet (Nat.primesLE 11) history).card =
        history.length + 5 := by
    rw [recruitedLabelSet_eq_union_toFinset]
    have hdisjoint : Disjoint (Nat.primesLE 11) history.toFinset := by
      rw [Finset.disjoint_left]
      intro q hqPermanent hqHistory
      exact hhistory.labels_fresh_from_initial q
        (List.mem_toFinset.mp hqHistory) hqPermanent
    rw [Finset.card_union_of_disjoint hdisjoint, primesLE_eleven_card]
    simp [List.toFinset_card_of_nodup hnodup, Nat.add_comm]
  refine ⟨history, hhistory, hnodup, ?_, hcardFinal, ?_⟩
  · simpa [hrank] using hlength
  · simpa [hcardFinal] using hconfined

theorem exists_exactRankRecruitmentHistory_with_rank_window_bound
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y) :
    ∃ history,
      ActualRankRecruitmentHistory start hbounded (Nat.primesLE 11) history ∧
      history.Nodup ∧
      history.length ≤ K ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap (history.length + 5)) ∧
      K ≤
        (2 * (uniformCompositeSurvivorGap (history.length + 5) + 1) + 1) ^ 2 := by
  obtain ⟨history, hhistory, hnodup, hlength, _hcard, hconfined⟩ :=
    exists_complete_exactRankRecruitmentHistory
      (hbounded := hbounded) hrank hxLarge hyLarge
  have hrankWindow :=
    exactBoundaryLabelRank_le_window_square_of_confined
      (hbounded := hbounded) hconfined
  exact ⟨history, hhistory, hnodup, hlength, hconfined, by
    simpa [hrank] using hrankWindow⟩

theorem exists_exactRankRecruitmentHistory_with_exponential_rank_bound
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y) :
    ∃ history,
      ActualRankRecruitmentHistory start hbounded (Nat.primesLE 11) history ∧
      history.Nodup ∧
      history.length ≤ K ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap (history.length + 5)) ∧
      K ≤ (5 * 16 ^ (history.length + 6)) ^ 2 := by
  obtain ⟨history, hhistory, hnodup, hlength, hconfined, hrankWindow⟩ :=
    exists_exactRankRecruitmentHistory_with_rank_window_bound
      (hbounded := hbounded) hrank hxLarge hyLarge
  have hdiameter := componentRankAnchorDiameter_le history.length
  have hwindowEq :
      2 * (uniformCompositeSurvivorGap (history.length + 5) + 1) + 1 =
        2 * componentRankAnchorRadius history.length + 1 := by
    rfl
  refine ⟨history, hhistory, hnodup, hlength, hconfined, ?_⟩
  rw [hwindowEq] at hrankWindow
  exact hrankWindow.trans <| by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul hdiameter hdiameter

/-! ## Growing-cutoff form -/

noncomputable def cutoffActiveLabels
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start)
    (Y : Nat) : Finset Nat :=
  (finiteSafeComponentActiveLabels start hbounded).filter fun q ↦ q ≤ Y

theorem cutoffActiveLabels_subset_activeLabels
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {Y : Nat} :
    cutoffActiveLabels start hbounded Y ⊆
      finiteSafeComponentActiveLabels start hbounded := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

theorem ActualRankRecruitmentHistory.labels_above_cutoff
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {Y : Nat} {history : List Nat}
    (hhistory : ActualRankRecruitmentHistory start hbounded
      (cutoffActiveLabels start hbounded Y) history) :
    ∀ q ∈ history, Y < q := by
  intro q hqHistory
  have hqActive := hhistory.labels_mem_active q hqHistory
  have hqFresh := hhistory.labels_fresh_from_initial q hqHistory
  by_contra hnotLarge
  have hqLe : q ≤ Y := Nat.le_of_not_gt hnotLarge
  exact hqFresh (Finset.mem_filter.mpr ⟨hqActive, hqLe⟩)

theorem exists_complete_cutoffRankRecruitmentHistory
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K Y : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y) :
    ∃ history,
      ActualRankRecruitmentHistory start hbounded
        (cutoffActiveLabels start hbounded Y) history ∧
      history.Nodup ∧
      (∀ q ∈ history, Y < q) ∧
      history.length ≤ K + 5 ∧
      (recruitedLabelSet (cutoffActiveLabels start hbounded Y) history).card =
        (cutoffActiveLabels start hbounded Y).card + history.length ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap
          ((cutoffActiveLabels start hbounded Y).card + history.length)) := by
  classical
  let Q := finiteSafeComponentActiveLabels start hbounded
  have hQCard : Q.card ≤ K + 5 := by
    dsimp [Q]
    simpa [hrank] using
      finiteSafeComponentActiveLabels_card_le_rank_add_five start hbounded
  have hxQ :
      Nat.nth Nat.Prime Q.card + uniformCompositeSurvivorGap Q.card + 1 ≤
        start.x := by
    have hnth : Nat.nth Nat.Prime Q.card ≤ Nat.nth Nat.Prime (K + 5) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hQCard
    have hgap : uniformCompositeSurvivorGap Q.card ≤
        uniformCompositeSurvivorGap (K + 5) :=
      uniformCompositeSurvivorGap_mono hQCard
    dsimp [componentRankThreshold, componentRankGap] at hxLarge
    omega
  have hyQ :
      Nat.nth Nat.Prime Q.card + uniformCompositeSurvivorGap Q.card + 1 ≤
        start.y := by
    have hnth : Nat.nth Nat.Prime Q.card ≤ Nat.nth Nat.Prime (K + 5) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hQCard
    have hgap : uniformCompositeSurvivorGap Q.card ≤
        uniformCompositeSurvivorGap (K + 5) :=
      uniformCompositeSurvivorGap_mono hQCard
    dsimp [componentRankThreshold, componentRankGap] at hyLarge
    omega
  obtain ⟨history, hhistory, hconfined⟩ :=
    exists_complete_actualRankRecruitmentHistory
      (hbounded := hbounded) (cutoffActiveLabels start hbounded Y)
      cutoffActiveLabels_subset_activeLabels
      (by simpa [Q] using hxQ) (by simpa [Q] using hyQ)
  have hnodup := hhistory.nodup
  have habove := hhistory.labels_above_cutoff
  have hlength := hhistory.length_le_activeLabel_card
  have hcard := hhistory.recruitedLabelSet_card
  refine ⟨history, hhistory, hnodup, habove, ?_, hcard, ?_⟩
  · exact hlength.trans hQCard
  · simpa [hcard] using hconfined

/-! ## Paid two-coordinate barrier histories -/

/--
A paid recruitment retains the literal exterior-frontier site at which its
new label was read.  In particular, the label divides both coordinates of
that same site.  One coordinate of the site is the composite survivor line
crossed by the original safe component and lies in the current rank window.
-/
structure ActualPaidBarrierWitness where
  site : LatticePoint
  label : Nat

def ActualPaidBarrierWitness.Valid
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start)
    (R : Finset Nat) (H : Nat)
    (witness : ActualPaidBarrierWitness) : Prop :=
  witness.site ∈ safeComponentFrontier start ∧
  witness.label = commonPrimeLabel witness.site ∧
  witness.label ∈ finiteSafeComponentActiveLabels start hbounded ∧
  witness.label ∉ R ∧
  witness.label ∣ witness.site.x ∧
  witness.label ∣ witness.site.y ∧
  ((Composite witness.site.x ∧
      ((start.x < witness.site.x ∧
          witness.site.x ≤ start.x + uniformCompositeSurvivorGap H) ∨
        (witness.site.x < start.x ∧
          start.x ≤ witness.site.x + uniformCompositeSurvivorGap H)) ∧
      (∀ z, witness.site.y ≤ z →
        verticalLinePoint witness.site.x z ∉ safeComponent start)) ∨
    (Composite witness.site.y ∧
      ((start.y < witness.site.y ∧
          witness.site.y ≤ start.y + uniformCompositeSurvivorGap H) ∨
        (witness.site.y < start.y ∧
          start.y ≤ witness.site.y + uniformCompositeSurvivorGap H)) ∧
      (∀ z, witness.site.x ≤ z →
        horizontalLinePoint z witness.site.y ∉ safeComponent start)))

theorem exists_actualPaidBarrierWitness_of_component_far_right
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge : Nat.nth Nat.Prime H ≤ start.x)
    (hfinish : finish ∈ safeComponent start)
    (hfar : start.x + uniformCompositeSurvivorGap H < finish.x) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  obtain ⟨width, hwidthGt, hwidthLe, hwidthComposite, hwidthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.x) (Q := R) hcard hprime hxLarge
  have hcross : width ≤ finish.x := hwidthLe.trans (Nat.le_of_lt hfar)
  obtain ⟨y, hmeets⟩ :=
    safeComponent_hits_vertical_of_crosses_above hfinish hwidthGt hcross
  obtain ⟨site, q, hfrontier, hsiteX, hlabel,
      hqActive, hqFresh, hqx, hqy, houter⟩ :=
    exists_outer_fresh_activeLabel_site_of_verticalLine_meets_component
      hwidthComposite hwidthAvoids hmeets
  refine ⟨⟨site, q⟩, ?_⟩
  refine ⟨hfrontier, hlabel, hqActive, hqFresh, hqx, hqy, Or.inl ?_⟩
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, houter⟩
  · simpa [hsiteX] using hwidthComposite
  · simpa [hsiteX] using hwidthGt
  · simpa [hsiteX] using hwidthLe

theorem exists_actualPaidBarrierWitness_of_component_far_left
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hfinish : finish ∈ safeComponent start)
    (hfar : finish.x + uniformCompositeSurvivorGap H < start.x) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  let gap := uniformCompositeSurvivorGap H
  let lowerBase := start.x - gap - 1
  have hnth : Nat.nth Nat.Prime H ≤ lowerBase := by
    dsimp [lowerBase, gap] at hxLarge ⊢
    omega
  obtain ⟨width, hwidthGt, hwidthLe, hwidthComposite, hwidthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerBase) (Q := R) hcard hprime hnth
  have hwidthLt : width < start.x := by
    change width ≤ lowerBase + gap at hwidthLe
    dsimp [lowerBase, gap] at hwidthLe hxLarge
    omega
  have hcross : finish.x ≤ width := by
    dsimp [lowerBase, gap] at hwidthGt hfar ⊢
    omega
  have hnear : start.x ≤ width + uniformCompositeSurvivorGap H := by
    dsimp [lowerBase, gap] at hxLarge hwidthGt ⊢
    omega
  obtain ⟨y, hmeets⟩ :=
    safeComponent_hits_vertical_of_crosses_below hfinish hwidthLt hcross
  obtain ⟨site, q, hfrontier, hsiteX, hlabel,
      hqActive, hqFresh, hqx, hqy, houter⟩ :=
    exists_outer_fresh_activeLabel_site_of_verticalLine_meets_component
      hwidthComposite hwidthAvoids hmeets
  refine ⟨⟨site, q⟩, ?_⟩
  refine ⟨hfrontier, hlabel, hqActive, hqFresh, hqx, hqy, Or.inl ?_⟩
  refine ⟨?_, Or.inr ⟨?_, ?_⟩, houter⟩
  · simpa [hsiteX] using hwidthComposite
  · simpa [hsiteX] using hwidthLt
  · simpa [hsiteX] using hnear

theorem exists_actualPaidBarrierWitness_of_component_far_above
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hyLarge : Nat.nth Nat.Prime H ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (hfar : start.y + uniformCompositeSurvivorGap H < finish.y) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  obtain ⟨height, hheightGt, hheightLe, hheightComposite, hheightAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.y) (Q := R) hcard hprime hyLarge
  have hcross : height ≤ finish.y := hheightLe.trans (Nat.le_of_lt hfar)
  obtain ⟨x, hmeets⟩ :=
    safeComponent_hits_horizontal_of_crosses_above hfinish hheightGt hcross
  obtain ⟨site, q, hfrontier, hsiteY, hlabel,
      hqActive, hqFresh, hqx, hqy, houter⟩ :=
    exists_outer_fresh_activeLabel_site_of_horizontalLine_meets_component
      hheightComposite hheightAvoids hmeets
  refine ⟨⟨site, q⟩, ?_⟩
  refine ⟨hfrontier, hlabel, hqActive, hqFresh, hqx, hqy, Or.inr ?_⟩
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, houter⟩
  · simpa [hsiteY] using hheightComposite
  · simpa [hsiteY] using hheightGt
  · simpa [hsiteY] using hheightLe

theorem exists_actualPaidBarrierWitness_of_component_far_below
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (hfar : finish.y + uniformCompositeSurvivorGap H < start.y) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  let gap := uniformCompositeSurvivorGap H
  let lowerBase := start.y - gap - 1
  have hnth : Nat.nth Nat.Prime H ≤ lowerBase := by
    dsimp [lowerBase, gap] at hyLarge ⊢
    omega
  obtain ⟨height, hheightGt, hheightLe, hheightComposite, hheightAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerBase) (Q := R) hcard hprime hnth
  have hheightLt : height < start.y := by
    change height ≤ lowerBase + gap at hheightLe
    dsimp [lowerBase, gap] at hheightLe hyLarge
    omega
  have hcross : finish.y ≤ height := by
    dsimp [lowerBase, gap] at hheightGt hfar ⊢
    omega
  have hnear : start.y ≤ height + uniformCompositeSurvivorGap H := by
    dsimp [lowerBase, gap] at hyLarge hheightGt ⊢
    omega
  obtain ⟨x, hmeets⟩ :=
    safeComponent_hits_horizontal_of_crosses_below hfinish hheightLt hcross
  obtain ⟨site, q, hfrontier, hsiteY, hlabel,
      hqActive, hqFresh, hqx, hqy, houter⟩ :=
    exists_outer_fresh_activeLabel_site_of_horizontalLine_meets_component
      hheightComposite hheightAvoids hmeets
  refine ⟨⟨site, q⟩, ?_⟩
  refine ⟨hfrontier, hlabel, hqActive, hqFresh, hqx, hqy, Or.inr ?_⟩
  refine ⟨?_, Or.inr ⟨?_, ?_⟩, houter⟩
  · simpa [hsiteY] using hheightComposite
  · simpa [hsiteY] using hheightLt
  · simpa [hsiteY] using hnear

theorem exists_actualPaidBarrierWitness_of_component_outside_current_rank_window
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hfinish : finish ∈ safeComponent start)
    (houtside :
      start.x + uniformCompositeSurvivorGap H < finish.x ∨
      finish.x + uniformCompositeSurvivorGap H < start.x ∨
      start.y + uniformCompositeSurvivorGap H < finish.y ∨
      finish.y + uniformCompositeSurvivorGap H < start.y) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  rcases houtside with hright | hleft | habove | hbelow
  · exact exists_actualPaidBarrierWitness_of_component_far_right
      hcard hprime (by omega) hfinish hright
  · exact exists_actualPaidBarrierWitness_of_component_far_left
      hcard hprime hxLarge hfinish hleft
  · exact exists_actualPaidBarrierWitness_of_component_far_above
      hcard hprime (by omega) hfinish habove
  · exact exists_actualPaidBarrierWitness_of_component_far_below
      hcard hprime hyLarge hfinish hbelow

theorem exists_actualPaidBarrierWitness_of_not_confined_current_rank_window
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y)
    (hnotConfined :
      ¬ SafeComponentConfinedWithin start (uniformCompositeSurvivorGap H)) :
    ∃ witness,
      ActualPaidBarrierWitness.Valid start hbounded R H witness := by
  classical
  by_contra hnone
  push Not at hnone
  apply hnotConfined
  intro finish hfinish
  by_contra hnotBounds
  have houtside :
      start.x + uniformCompositeSurvivorGap H < finish.x ∨
      finish.x + uniformCompositeSurvivorGap H < start.x ∨
      start.y + uniformCompositeSurvivorGap H < finish.y ∨
      finish.y + uniformCompositeSurvivorGap H < start.y := by
    omega
  obtain ⟨witness, hwitness⟩ :=
    exists_actualPaidBarrierWitness_of_component_outside_current_rank_window
      hcard hprime hxLarge hyLarge hfinish houtside
  exact hnone witness hwitness

/-- Insert all labels carried by a paid witness history. -/
def paidBarrierLabelSet :
    Finset Nat → List ActualPaidBarrierWitness → Finset Nat
  | R, [] => R
  | R, witness :: history =>
      paidBarrierLabelSet (insert witness.label R) history

/--
The witness-preserving history used by the paid-bracket route.  No phase site
is erased: at every recursive state the head stores the actual two-coordinate
frontier event that paid for insertion of its fresh label.
-/
def ActualPaidBarrierHistory
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    Finset Nat → List ActualPaidBarrierWitness → Prop
  | _R, [] => True
  | R, witness :: history =>
      ActualPaidBarrierWitness.Valid start hbounded R R.card witness ∧
      ActualPaidBarrierHistory start hbounded
        (insert witness.label R) history

theorem ActualPaidBarrierHistory.labels_mem_active
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List ActualPaidBarrierWitness}
    (hhistory : ActualPaidBarrierHistory start hbounded R history) :
    ∀ witness ∈ history,
      witness.label ∈ finiteSafeComponentActiveLabels start hbounded := by
  induction history generalizing R with
  | nil => simp
  | cons witness history ih =>
      rcases hhistory with ⟨hwitness, htail⟩
      intro other hother
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact hwitness.2.2.1
      · exact ih htail other hother

theorem ActualPaidBarrierHistory.labels_fresh_from_initial
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List ActualPaidBarrierWitness}
    (hhistory : ActualPaidBarrierHistory start hbounded R history) :
    ∀ witness ∈ history, witness.label ∉ R := by
  induction history generalizing R with
  | nil => simp
  | cons witness history ih =>
      rcases hhistory with ⟨hwitness, htail⟩
      intro other hother
      simp only [List.mem_cons] at hother
      rcases hother with rfl | hother
      · exact hwitness.2.2.2.1
      · exact fun hmem =>
          ih htail other hother (Finset.mem_insert_of_mem hmem)

theorem ActualPaidBarrierHistory.label_nodup
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {history : List ActualPaidBarrierWitness}
    (hhistory : ActualPaidBarrierHistory start hbounded R history) :
    (history.map ActualPaidBarrierWitness.label).Nodup := by
  induction history generalizing R with
  | nil => simp
  | cons witness history ih =>
      rcases hhistory with ⟨_hwitness, htail⟩
      apply List.nodup_cons.mpr
      refine ⟨?_, ih htail⟩
      intro hlabel
      obtain ⟨other, hother, hotherLabel⟩ := List.mem_map.mp hlabel
      have hfresh :=
        ActualPaidBarrierHistory.labels_fresh_from_initial htail other hother
      exact hfresh (by simpa [hotherLabel] using
        (Finset.mem_insert_self witness.label R))

theorem exists_complete_actualPaidBarrierHistory
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    (R₀ : Finset Nat)
    (hR₀ : R₀ ⊆ finiteSafeComponentActiveLabels start hbounded)
    (hxLarge :
      Nat.nth Nat.Prime
            (finiteSafeComponentActiveLabels start hbounded).card +
          uniformCompositeSurvivorGap
            (finiteSafeComponentActiveLabels start hbounded).card + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime
            (finiteSafeComponentActiveLabels start hbounded).card +
          uniformCompositeSurvivorGap
            (finiteSafeComponentActiveLabels start hbounded).card + 1 ≤ start.y) :
    ∃ history,
      ActualPaidBarrierHistory start hbounded R₀ history ∧
      SafeComponentConfinedWithin start
        (uniformCompositeSurvivorGap
          (paidBarrierLabelSet R₀ history).card) := by
  classical
  let Q := finiteSafeComponentActiveLabels start hbounded
  have hQPrime : ∀ q ∈ Q, Nat.Prime q := by
    intro q hq
    exact finiteSafeComponentActiveLabel_prime hq
  let rec go (R : Finset Nat) (hRQ : R ⊆ Q) :
      ∃ history,
        ActualPaidBarrierHistory start hbounded R history ∧
        SafeComponentConfinedWithin start
          (uniformCompositeSurvivorGap
            (paidBarrierLabelSet R history).card) := by
    by_cases hterminal :
        SafeComponentConfinedWithin start
          (uniformCompositeSurvivorGap R.card)
    · exact ⟨[], trivial, hterminal⟩
    · have hcardRQ : R.card ≤ Q.card := Finset.card_le_card hRQ
      have hxCurrent :
          Nat.nth Nat.Prime R.card +
              uniformCompositeSurvivorGap R.card + 1 ≤ start.x := by
        have hnth : Nat.nth Nat.Prime R.card ≤ Nat.nth Nat.Prime Q.card :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcardRQ
        have hgap :
            uniformCompositeSurvivorGap R.card ≤
              uniformCompositeSurvivorGap Q.card :=
          uniformCompositeSurvivorGap_mono hcardRQ
        have hxMax := hxLarge
        change Nat.nth Nat.Prime Q.card +
            uniformCompositeSurvivorGap Q.card + 1 ≤ start.x at hxMax
        omega
      have hyCurrent :
          Nat.nth Nat.Prime R.card +
              uniformCompositeSurvivorGap R.card + 1 ≤ start.y := by
        have hnth : Nat.nth Nat.Prime R.card ≤ Nat.nth Nat.Prime Q.card :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcardRQ
        have hgap :
            uniformCompositeSurvivorGap R.card ≤
              uniformCompositeSurvivorGap Q.card :=
          uniformCompositeSurvivorGap_mono hcardRQ
        have hyMax := hyLarge
        change Nat.nth Nat.Prime Q.card +
            uniformCompositeSurvivorGap Q.card + 1 ≤ start.y at hyMax
        omega
      have hRPrime : ∀ q ∈ R, Nat.Prime q := by
        intro q hq
        exact hQPrime q (hRQ hq)
      obtain ⟨witness, hwitness⟩ :=
        exists_actualPaidBarrierWitness_of_not_confined_current_rank_window
          (H := R.card) (R := R) (le_refl _) hRPrime
          hxCurrent hyCurrent hterminal
      have hnextSubset : insert witness.label R ⊆ Q := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hwitness.2.2.1
        · exact hRQ hxR
      obtain ⟨history, hhistory, hfinal⟩ :=
        go (insert witness.label R) hnextSubset
      refine ⟨witness :: history, ⟨hwitness, hhistory⟩, ?_⟩
      exact hfinal
  termination_by
    (finiteSafeComponentActiveLabels start hbounded \ R).card
  decreasing_by
    rw [Finset.sdiff_insert]
    exact Finset.card_erase_lt_of_mem
      (Finset.mem_sdiff.mpr
        ⟨by simpa [Q] using hwitness.2.2.1, hwitness.2.2.2.1⟩)
  simpa [Q] using go R₀ hR₀

/-- The largest exact boundary rank compatible with confinement at state size
`H`, using only the literal frontier window. -/
noncomputable def paidRankWindowBound (H : Nat) : Nat :=
  (2 * (uniformCompositeSurvivorGap H + 1) + 1) ^ 2

theorem paidRankWindowBound_mono {H H' : Nat} (hHH' : H ≤ H') :
    paidRankWindowBound H ≤ paidRankWindowBound H' := by
  have hgap :
      uniformCompositeSurvivorGap H ≤ uniformCompositeSurvivorGap H' :=
    uniformCompositeSurvivorGap_mono hHH'
  have hdiameter :
      2 * (uniformCompositeSurvivorGap H + 1) + 1 ≤
        2 * (uniformCompositeSurvivorGap H' + 1) + 1 := by
    omega
  dsimp [paidRankWindowBound]
  rw [pow_two, pow_two]
  exact Nat.mul_le_mul hdiameter hdiameter

theorem not_confined_of_exact_rank_gt_paidRankWindowBound
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R : Finset Nat} {H K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hcard : R.card ≤ H)
    (hhigh : paidRankWindowBound H < K) :
    ¬ SafeComponentConfinedWithin start
      (uniformCompositeSurvivorGap R.card) := by
  intro hconfined
  have hrankWindow :=
    exactBoundaryLabelRank_le_window_square_of_confined
      (hbounded := hbounded) hconfined
  have hmono : paidRankWindowBound R.card ≤ paidRankWindowBound H :=
    paidRankWindowBound_mono hcard
  change exactBoundaryLabelRank start ≤ paidRankWindowBound R.card at hrankWindow
  rw [hrank] at hrankWindow
  omega

/--
If the exact rank lies above the confinement window at state size `H`, then
the original component produces any prescribed number `m` of paid, literal
two-coordinate recruitments, provided the initial paid state and these `m`
insertions fit below `H`.  This is the direct high-rank-to-long-history bridge.
-/
theorem exists_actualPaidBarrierHistory_of_rank_gt_window
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {R₀ : Finset Nat} {H K m : Nat}
    (hR₀ : R₀ ⊆ finiteSafeComponentActiveLabels start hbounded)
    (hsize : R₀.card + m ≤ H)
    (hrank : exactBoundaryLabelRank start = K)
    (hhigh : paidRankWindowBound H < K)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ start.y) :
    ∃ history,
      history.length = m ∧
      ActualPaidBarrierHistory start hbounded R₀ history := by
  classical
  induction m generalizing R₀ with
  | zero =>
      exact ⟨[], rfl, trivial⟩
  | succ m ih =>
      have hcard : R₀.card ≤ H := by omega
      have hRPrime : ∀ q ∈ R₀, Nat.Prime q := by
        intro q hq
        exact finiteSafeComponentActiveLabel_prime (hR₀ hq)
      have hxCurrent :
          Nat.nth Nat.Prime R₀.card +
              uniformCompositeSurvivorGap R₀.card + 1 ≤ start.x := by
        have hnth : Nat.nth Nat.Prime R₀.card ≤ Nat.nth Nat.Prime H :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcard
        have hgap :
            uniformCompositeSurvivorGap R₀.card ≤
              uniformCompositeSurvivorGap H :=
          uniformCompositeSurvivorGap_mono hcard
        omega
      have hyCurrent :
          Nat.nth Nat.Prime R₀.card +
              uniformCompositeSurvivorGap R₀.card + 1 ≤ start.y := by
        have hnth : Nat.nth Nat.Prime R₀.card ≤ Nat.nth Nat.Prime H :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hcard
        have hgap :
            uniformCompositeSurvivorGap R₀.card ≤
              uniformCompositeSurvivorGap H :=
          uniformCompositeSurvivorGap_mono hcard
        omega
      have hnotConfined :
          ¬ SafeComponentConfinedWithin start
            (uniformCompositeSurvivorGap R₀.card) :=
        not_confined_of_exact_rank_gt_paidRankWindowBound
          (hbounded := hbounded) hrank hcard hhigh
      obtain ⟨witness, hwitness⟩ :=
        exists_actualPaidBarrierWitness_of_not_confined_current_rank_window
          (H := R₀.card) (R := R₀) (le_refl _) hRPrime
          hxCurrent hyCurrent hnotConfined
      have hnextSubset :
          insert witness.label R₀ ⊆
            finiteSafeComponentActiveLabels start hbounded := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqR
        · exact hwitness.2.2.1
        · exact hR₀ hqR
      have hcardInsert :
          (insert witness.label R₀).card = R₀.card + 1 := by
        rw [Finset.card_insert_of_notMem hwitness.2.2.2.1]
      have hnextSize : (insert witness.label R₀).card + m ≤ H := by
        rw [hcardInsert]
        omega
      obtain ⟨history, hlength, hhistory⟩ :=
        ih hnextSubset hnextSize
      refine ⟨witness :: history, by simp [hlength], ⟨hwitness, hhistory⟩⟩

/--
Concrete logarithmic recruitment consequence.  Exact rank above the explicit
exponential window forces `m` distinct, paid two-coordinate frontier events
before any terminal confinement is possible.
-/
theorem exists_exactRankPaidBarrierHistory_of_exponential_rank
    {start : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K m : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hhigh : (5 * 16 ^ (m + 6)) ^ 2 < K)
    (hxLarge : componentRankThreshold m ≤ start.x)
    (hyLarge : componentRankThreshold m ≤ start.y) :
    ∃ history,
      history.length = m ∧
      ActualPaidBarrierHistory start hbounded (Nat.primesLE 11) history ∧
      (history.map ActualPaidBarrierWitness.label).Nodup := by
  have hpermanent :
      Nat.primesLE 11 ⊆ finiteSafeComponentActiveLabels start hbounded := by
    intro q hq
    exact Finset.mem_union_right _ hq
  have hsize : (Nat.primesLE 11).card + m ≤ m + 5 := by
    rw [primesLE_eleven_card]
    omega
  have hdiameter := componentRankAnchorDiameter_le m
  have hwindowLe :
      paidRankWindowBound (m + 5) ≤ (5 * 16 ^ (m + 6)) ^ 2 := by
    change (2 * componentRankAnchorRadius m + 1) ^ 2 ≤
      (5 * 16 ^ (m + 6)) ^ 2
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul hdiameter hdiameter
  have hwindowHigh : paidRankWindowBound (m + 5) < K :=
    hwindowLe.trans_lt hhigh
  obtain ⟨history, hlength, hhistory⟩ :=
    exists_actualPaidBarrierHistory_of_rank_gt_window
      (hbounded := hbounded) hpermanent hsize hrank hwindowHigh
      (by simpa [componentRankThreshold, componentRankGap] using hxLarge)
      (by simpa [componentRankThreshold, componentRankGap] using hyLarge)
  exact ⟨history, hlength, hhistory, hhistory.label_nodup⟩

end Erdos1212Kernel
