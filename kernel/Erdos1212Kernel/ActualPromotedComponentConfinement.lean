import Erdos1212Kernel.ExplicitFixedRankRootCounting

namespace Erdos1212Kernel

/-!
# Confinement of actual promoted components

Fix a finite paid set `R` of prime labels.  A promoted unsafe site is either
an actual prime--prime site or an actual nonvisible site whose least common
prime label already belongs to `R`.  This is the promoted set that occurs in
the terminal without-replacement exploration; prime--prime sites are not
replaced by a periodic unit surrogate.

The decisive geometric fact is that a composite coordinate avoiding every
label in `R` supports no promoted site at all.  Uniform composite survivors
therefore give four empty coordinate lines around any promoted component.
Even for star adjacency, a path cannot cross one of these lines without
visiting it.  Hence the entire actual promoted component is contained in one
explicit finite lattice window depending only on `R.card`, not on the
identities or sizes of its primes.

This is the honest exponential version of the terminal one-hull reduction.
It makes no periodic promotion of prime pairs and uses no unproved
Jacobsthal or sieve estimate.
-/

/-- Actual unsafe sites already absorbed by the paid label state. -/
def ActualPromotedUnsafe (R : Finset Nat) (point : LatticePoint) : Prop :=
  PrimePair point ∨
    (¬ Visible point ∧ commonPrimeLabel point ∈ R)

/-- Chebyshev-neighbour adjacency used by an exterior lattice contour. -/
def StarAdjacent (left right : LatticePoint) : Prop :=
  left ≠ right ∧
  left.x ≤ right.x + 1 ∧ right.x ≤ left.x + 1 ∧
  left.y ≤ right.y + 1 ∧ right.y ≤ left.y + 1

theorem starAdjacent_symm {left right : LatticePoint} :
    StarAdjacent left right → StarAdjacent right left := by
  rintro ⟨hne, hxl, hxr, hyl, hyr⟩
  exact ⟨hne.symm, hxr, hxl, hyr, hyl⟩

theorem starAdjacent_irrefl (point : LatticePoint) :
    ¬ StarAdjacent point point := by
  intro h
  exact h.1 rfl

def starLatticeGraph : SimpleGraph LatticePoint where
  Adj := StarAdjacent
  symm := fun _ _ ↦ starAdjacent_symm
  loopless := ⟨starAdjacent_irrefl⟩

theorem starAdjacent_x_le_succ {left right : LatticePoint}
    (hadjacent : StarAdjacent left right) :
    right.x ≤ left.x + 1 :=
  hadjacent.2.2.1

theorem starAdjacent_y_le_succ {left right : LatticePoint}
    (hadjacent : StarAdjacent left right) :
    right.y ≤ left.y + 1 :=
  hadjacent.2.2.2.2

/-- Reachability inside the actual promoted set, with diagonal contour steps
allowed. -/
def ActualPromotedStarReachable
    (R : Finset Nat) (start finish : LatticePoint) : Prop :=
  ∃ walk : starLatticeGraph.Walk start finish,
    ∀ point, point ∈ walk.support → ActualPromotedUnsafe R point

theorem composite_not_prime {n : Nat} (hcomposite : Composite n) :
    ¬ Nat.Prime n := by
  exact (composite_iff_not_prime_of_one_lt
    (composite_one_lt hcomposite)).mp hcomposite

/-- A composite vertical line avoiding the paid labels contains no promoted
site, including no prime--prime site. -/
theorem actualPromotedUnsafe_not_on_vertical
    {R : Finset Nat} {width y : Nat}
    (hwidth : Composite width)
    (havoids : ∀ q ∈ R, ¬ q ∣ width) :
    ¬ ActualPromotedUnsafe R (verticalLinePoint width y) := by
  rintro (hprimePair | ⟨hnotVisible, hlabel⟩)
  · exact composite_not_prime hwidth hprimePair.1
  · have hspec := commonPrimeLabel_spec_of_not_visible hnotVisible
    exact havoids _ hlabel (by
      simpa [verticalLinePoint] using hspec.2.1)

/-- Horizontal counterpart of `actualPromotedUnsafe_not_on_vertical`. -/
theorem actualPromotedUnsafe_not_on_horizontal
    {R : Finset Nat} {x height : Nat}
    (hheight : Composite height)
    (havoids : ∀ q ∈ R, ¬ q ∣ height) :
    ¬ ActualPromotedUnsafe R (horizontalLinePoint x height) := by
  rintro (hprimePair | ⟨hnotVisible, hlabel⟩)
  · exact composite_not_prime hheight hprimePair.2
  · have hspec := commonPrimeLabel_spec_of_not_visible hnotVisible
    exact havoids _ hlabel (by
      simpa [horizontalLinePoint] using hspec.2.2)

theorem starWalk_hits_x_of_crosses_above
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {width : Nat}
    (hstart : start.x < width)
    (hfinish : width ≤ finish.x) :
    ∃ index ≤ walk.length, (walk.getVert index).x = width := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ width ≤ (walk.getVert index).x :=
    ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
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
      ⟨by omega, hprevious⟩
  have hadjacent :
      StarAdjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : width ≤ (walk.getVert first).x := by
    simpa [first] using hfirst.2
  have hstep := starAdjacent_x_le_succ hadjacent
  omega

theorem starWalk_hits_x_of_crosses_below
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {width : Nat}
    (hstart : width < start.x)
    (hfinish : finish.x ≤ width) :
    ∃ index ≤ walk.length, (walk.getVert index).x = width := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ (walk.getVert index).x ≤ width :=
    ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
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
      ⟨by omega, hprevious⟩
  have hadjacent :
      StarAdjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : (walk.getVert first).x ≤ width := by
    simpa [first] using hfirst.2
  have hstep := starAdjacent_x_le_succ (starAdjacent_symm hadjacent)
  omega

theorem starWalk_hits_y_of_crosses_above
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {height : Nat}
    (hstart : start.y < height)
    (hfinish : height ≤ finish.y) :
    ∃ index ≤ walk.length, (walk.getVert index).y = height := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ height ≤ (walk.getVert index).y :=
    ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
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
      ⟨by omega, hprevious⟩
  have hadjacent :
      StarAdjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : height ≤ (walk.getVert first).y := by
    simpa [first] using hfirst.2
  have hstep := starAdjacent_y_le_succ hadjacent
  omega

theorem starWalk_hits_y_of_crosses_below
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {height : Nat}
    (hstart : height < start.y)
    (hfinish : finish.y ≤ height) :
    ∃ index ≤ walk.length, (walk.getVert index).y = height := by
  have hexists :
      ∃ index, index ≤ walk.length ∧ (walk.getVert index).y ≤ height :=
    ⟨walk.length, Nat.le_refl _, by simpa using hfinish⟩
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
      ⟨by omega, hprevious⟩
  have hadjacent :
      StarAdjacent (walk.getVert (first - 1)) (walk.getVert first) := by
    have hindex : first - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : first - 1 + 1 = first := by omega
    simpa [hsucc] using hstep
  refine ⟨first, hfirst.1, ?_⟩
  have hcurrent : (walk.getVert first).y ≤ height := by
    simpa [first] using hfirst.2
  have hstep := starAdjacent_y_le_succ (starAdjacent_symm hadjacent)
  omega

/-- Four actual empty composite lines confine the whole promoted star
component.  The returned inequalities also retain their distance from the
anchor for the finite-window corollary. -/
theorem exists_actualPromotedStarComponent_barrier_box
    {R : Finset Nat} {anchor : LatticePoint} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ anchor.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ anchor.y) :
    ∃ west east south north,
      west < anchor.x ∧ anchor.x < east ∧
      south < anchor.y ∧ anchor.y < north ∧
      anchor.x ≤ west + uniformCompositeSurvivorGap H ∧
      east ≤ anchor.x + uniformCompositeSurvivorGap H ∧
      anchor.y ≤ south + uniformCompositeSurvivorGap H ∧
      north ≤ anchor.y + uniformCompositeSurvivorGap H ∧
      (∀ finish, ActualPromotedStarReachable R anchor finish →
        west < finish.x ∧ finish.x < east ∧
        south < finish.y ∧ finish.y < north) := by
  let gap := uniformCompositeSurvivorGap H
  let lowerX := anchor.x - gap - 1
  let lowerY := anchor.y - gap - 1
  have hnthX : Nat.nth Nat.Prime H ≤ lowerX := by
    dsimp [lowerX, gap] at hxLarge ⊢
    omega
  have hnthY : Nat.nth Nat.Prime H ≤ lowerY := by
    dsimp [lowerY, gap] at hyLarge ⊢
    omega
  have hnthAnchorX : Nat.nth Nat.Prime H ≤ anchor.x := by omega
  have hnthAnchorY : Nat.nth Nat.Prime H ≤ anchor.y := by omega
  obtain ⟨east, heastGt, heastLe, heastComposite, heastAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := anchor.x) (Q := R) hcard hprime
      hnthAnchorX
  obtain ⟨west, hwestGt, hwestLe, hwestComposite, hwestAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerX) (Q := R) hcard hprime hnthX
  obtain ⟨north, hnorthGt, hnorthLe, hnorthComposite, hnorthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := anchor.y) (Q := R) hcard hprime
      hnthAnchorY
  obtain ⟨south, hsouthGt, hsouthLe, hsouthComposite, hsouthAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := lowerY) (Q := R) hcard hprime hnthY
  have hwestLt : west < anchor.x := by
    change west ≤ lowerX + gap at hwestLe
    dsimp [lowerX, gap] at hwestLe hxLarge
    omega
  have hsouthLt : south < anchor.y := by
    change south ≤ lowerY + gap at hsouthLe
    dsimp [lowerY, gap] at hsouthLe hyLarge
    omega
  have hwestNear : anchor.x ≤ west + gap := by
    dsimp [lowerX, gap] at hwestGt hxLarge ⊢
    omega
  have hsouthNear : anchor.y ≤ south + gap := by
    dsimp [lowerY, gap] at hsouthGt hyLarge ⊢
    omega
  refine ⟨west, east, south, north,
    hwestLt, heastGt, hsouthLt, hnorthGt,
    hwestNear, heastLe, hsouthNear, hnorthLe, ?_⟩
  intro finish hreachable
  obtain ⟨walk, hwalkPromoted⟩ := hreachable
  have hfinishWest : west < finish.x := by
    by_contra hnot
    have hfinish : finish.x ≤ west := by omega
    obtain ⟨index, hindex, hhit⟩ :=
      starWalk_hits_x_of_crosses_below walk hwestLt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index =
        verticalLinePoint west (walk.getVert index).y :=
      LatticePoint.ext hhit rfl
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_vertical hwestComposite hwestAvoids
      hpromoted
  have hfinishEast : finish.x < east := by
    by_contra hnot
    have hfinish : east ≤ finish.x := by omega
    obtain ⟨index, hindex, hhit⟩ :=
      starWalk_hits_x_of_crosses_above walk heastGt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index =
        verticalLinePoint east (walk.getVert index).y :=
      LatticePoint.ext hhit rfl
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_vertical heastComposite heastAvoids
      hpromoted
  have hfinishSouth : south < finish.y := by
    by_contra hnot
    have hfinish : finish.y ≤ south := by omega
    obtain ⟨index, hindex, hhit⟩ :=
      starWalk_hits_y_of_crosses_below walk hsouthLt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index =
        horizontalLinePoint (walk.getVert index).x south :=
      LatticePoint.ext rfl hhit
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_horizontal hsouthComposite hsouthAvoids
      hpromoted
  have hfinishNorth : finish.y < north := by
    by_contra hnot
    have hfinish : north ≤ finish.y := by omega
    obtain ⟨index, hindex, hhit⟩ :=
      starWalk_hits_y_of_crosses_above walk hnorthGt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index =
        horizontalLinePoint (walk.getVert index).x north :=
      LatticePoint.ext rfl hhit
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_horizontal hnorthComposite hnorthAvoids
      hpromoted
  exact ⟨hfinishWest, hfinishEast, hfinishSouth, hfinishNorth⟩

/-- The complete actual promoted star component lies in one explicit finite
window.  In particular, all actual prime--prime sites already joined to the
paid divisor component are absorbed without a periodic surrogate. -/
theorem actualPromotedStarReachable_mem_latticeWindow
    {R : Finset Nat} {anchor finish : LatticePoint} {H : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ anchor.x)
    (hyLarge :
      Nat.nth Nat.Prime H + uniformCompositeSurvivorGap H + 1 ≤ anchor.y)
    (hreachable : ActualPromotedStarReachable R anchor finish) :
    finish ∈ latticeWindow anchor (uniformCompositeSurvivorGap H) := by
  obtain ⟨west, east, south, north,
      hwest, heast, hsouth, hnorth,
      hwestNear, heastNear, hsouthNear, hnorthNear, hbox⟩ :=
    exists_actualPromotedStarComponent_barrier_box
      hcard hprime hxLarge hyLarge
  have hfinish := hbox finish hreachable
  apply mem_latticeWindow.mpr
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Cardinal form of the one-final-hull geometry. -/
theorem actualPromotedStarComponent_window_card_le
    (anchor : LatticePoint) (H : Nat) :
    (latticeWindow anchor (uniformCompositeSurvivorGap H)).card ≤
      (2 * uniformCompositeSurvivorGap H + 1) ^ 2 :=
  latticeWindow_card_le anchor (uniformCompositeSurvivorGap H)

/-! ## Binding to the exact prime-corridor rank -/

/-- The canonical descending prime anchor lies strictly above the corridor
height parameter.  This quantitative form keeps the promoted-component box
away from the lower coordinate strip. -/
theorem root_second_lt_primeCorridorBoundaryAnchor_y
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N) :
    root.2 < (primeCorridorBoundaryAnchor root).y := by
  rcases root with ⟨p, k⟩
  have hk : 2 ≤ k :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp hroot).2).1
  obtain ⟨q, hqPrime, hkq, hqUpper⟩ :=
    exists_primeHeightBelow_double hk
  have hcandidatePositive : 0 < 2 * k - q := by omega
  have hcandidateBelow : 2 * k - q < 2 * k := by
    have hqPositive := hqPrime.pos
    omega
  have hcandidateHeight : 2 * k - (2 * k - q) = q := by omega
  have hcandidate : PrimeColumnDescentWitness k (2 * k - q) := by
    exact ⟨hcandidatePositive, hcandidateBelow,
      hcandidateHeight.symm ▸ hqPrime⟩
  have hfirstLe : firstPrimeColumnDescent k ≤ 2 * k - q := by
    rw [firstPrimeColumnDescent, dif_pos hk]
    exact Nat.find_min' (primeColumnDescentWitness_exists hk) hcandidate
  change k < 2 * k - firstPrimeColumnDescent k
  omega

/--
For an actual bounded corridor root of exact rank `K`, the whole promoted
star component of its canonical prime--pair anchor, using every actual active
boundary label, lies in the same explicit exponential rank window.  No
prime-pair surrogate and no moved cut occur in this statement.
-/
theorem exactRank_actualPromotedAnchorComponent_mem_latticeWindow
    {N K : Nat} {root : Nat × Nat} {finish : LatticePoint}
    (hbounded : ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root))
    (hN : 4 * componentRankThreshold K ≤ N)
    (hroot : root ∈ boundedHighCorridorRootsOfRank N K)
    (hreachable :
      ActualPromotedStarReachable
        (finiteSafeComponentActiveLabels (primeCorridorPoint root)
          hbounded)
        (primeCorridorBoundaryAnchor root) finish) :
    finish ∈ latticeWindow (primeCorridorBoundaryAnchor root)
      (componentRankGap K) := by
  classical
  have hrootData :
      root ∈ boundedHighPrimeCorridorRoots N ∧
        exactBoundaryLabelRank (primeCorridorPoint root) = K := by
    simpa [boundedHighCorridorRootsOfRank] using hroot
  have hrootBounded :
      root ∈ highPrimeCorridorRoots N ∧
        ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint root) := by
    simpa [boundedHighPrimeCorridorRoots] using hrootData.1
  let start := primeCorridorPoint root
  let R := finiteSafeComponentActiveLabels start hbounded
  have hcard : R.card ≤ K + 5 := by
    dsimp [R, start]
    simpa [hrootData.2] using
      finiteSafeComponentActiveLabels_card_le_rank_add_five
        (primeCorridorPoint root) hbounded
  have hprime : ∀ q ∈ R, Nat.Prime q := by
    intro q hq
    exact finiteSafeComponentActiveLabel_prime hq
  have hrootHigh := hrootBounded.1
  have hrootCorridor : root ∈ primeCorridorRoots N :=
    highPrimeCorridorRoots_subset N hrootHigh
  have hanchorX :
      componentRankThreshold K ≤ (primeCorridorBoundaryAnchor root).x := by
    rcases root with ⟨p, k⟩
    have hpLower :=
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hrootCorridor).1).2
    change componentRankThreshold K ≤ p
    omega
  have hanchorY :
      componentRankThreshold K ≤ (primeCorridorBoundaryAnchor root).y := by
    have hkMem := (Finset.mem_product.mp hrootHigh).2
    rw [highCorridorHeights] at hkMem
    have hkLower := (Finset.mem_Icc.mp hkMem).1
    have hanchorAbove :=
      root_second_lt_primeCorridorBoundaryAnchor_y hrootCorridor
    omega
  have hwindow :=
    actualPromotedStarReachable_mem_latticeWindow
      (R := R) (H := K + 5) hcard hprime
      (by simpa [componentRankThreshold, componentRankGap] using hanchorX)
      (by simpa [componentRankThreshold, componentRankGap] using hanchorY)
      (by simpa [R, start] using hreachable)
  simpa [componentRankGap] using hwindow

/-- The exact-rank promoted anchor component has one finite final-window
cardinality bound. -/
theorem exactRank_actualPromotedAnchorComponent_window_card_le
    (root : Nat × Nat) (K : Nat) :
    (latticeWindow (primeCorridorBoundaryAnchor root)
      (componentRankGap K)).card ≤
      (2 * componentRankGap K + 1) ^ 2 :=
  latticeWindow_card_le _ _

end Erdos1212Kernel
