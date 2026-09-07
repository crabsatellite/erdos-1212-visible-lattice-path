import Erdos1212Kernel.ConcreteSafeGraph

namespace Erdos1212Kernel

/-!
# The actual finite safe component and its deleted-vertex boundary

The canonical-rank argument is attached here to the original graph, before
any contour encoding.  A vertex belongs to `safeComponent start` exactly when
one finite walk from `start` to it stays in the original safe set.  Failure of
arbitrarily-far safe reachability makes this component a genuinely finite
set.  Its exterior vertex boundary consists only of unsafe vertices.

Most importantly, the first prime--prime point on an escaping full-visible
walk is an actual boundary vertex of this same component.  Thus the later
promoted-component mass is rooted at a literal deleted vertex; no periodic
surrogate, marginal prime density, or moved cut occurs at the graph boundary.
-/

def SafeReachableFrom (start finish : LatticePoint) : Prop :=
  ∃ walk : latticeGraph.Walk start finish,
    ∀ p, p ∈ walk.support → SafePoint p

def safeComponent (start : LatticePoint) : Set LatticePoint :=
  {finish | SafeReachableFrom start finish}

def safeComponentFrontier (start : LatticePoint) : Set LatticePoint :=
  {q | q ∉ safeComponent start ∧
    ∃ p ∈ safeComponent start, Adjacent p q}

def latticeBox (bound : Nat) : Finset LatticePoint :=
  ((Finset.range bound) ×ˢ (Finset.range bound)).image
    (fun coordinates ↦
      ({ x := coordinates.1, y := coordinates.2 } : LatticePoint))

@[simp] theorem mem_latticeBox {bound : Nat} {p : LatticePoint} :
    p ∈ latticeBox bound ↔ p.x < bound ∧ p.y < bound := by
  constructor
  · intro hp
    simp only [latticeBox, Finset.mem_image, Finset.mem_product,
      Finset.mem_range] at hp
    obtain ⟨coordinates, ⟨hx, hy⟩, hcoordinates⟩ := hp
    have hpairs : (coordinates.1, coordinates.2) = (p.x, p.y) := by
      exact congrArg (fun q : LatticePoint ↦ (q.x, q.y)) hcoordinates
    have hxEq : coordinates.1 = p.x := congrArg Prod.fst hpairs
    have hyEq : coordinates.2 = p.y := congrArg Prod.snd hpairs
    exact ⟨hxEq ▸ hx, hyEq ▸ hy⟩
  · rintro ⟨hx, hy⟩
    simp only [latticeBox, Finset.mem_image, Finset.mem_product,
      Finset.mem_range]
    exact ⟨(p.x, p.y), ⟨hx, hy⟩, rfl⟩

theorem safeComponent_finite_of_not_arbitrarilyFar
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    (safeComponent start).Finite := by
  classical
  rw [ArbitrarilyFarSafeReachable] at hbounded
  push Not at hbounded
  obtain ⟨bound, hbound⟩ := hbounded
  refine (latticeBox bound).finite_toSet.subset ?_
  intro finish hfinish
  obtain ⟨walk, hwalkSafe⟩ := hfinish
  have hnotFar : ¬ (bound ≤ finish.x ∨ bound ≤ finish.y) := by
    intro hfar
    obtain ⟨p, hp, hpUnsafe⟩ := hbound finish hfar walk
    exact hpUnsafe (hwalkSafe p hp)
  have hx : finish.x < bound := by
    exact Nat.lt_of_not_ge (fun hx ↦ hnotFar (Or.inl hx))
  have hy : finish.y < bound := by
    exact Nat.lt_of_not_ge (fun hy ↦ hnotFar (Or.inr hy))
  simpa using And.intro hx hy

theorem safePoint_of_mem_safeComponent
    {start finish : LatticePoint} (hfinish : finish ∈ safeComponent start) :
    SafePoint finish := by
  obtain ⟨walk, hwalkSafe⟩ := hfinish
  have hfinishSupport : finish ∈ walk.support := by
    simpa using walk.getVert_mem_support walk.length
  exact hwalkSafe finish hfinishSupport

noncomputable def finiteSafeComponent
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) : Finset LatticePoint :=
  (safeComponent_finite_of_not_arbitrarilyFar start hbounded).toFinset

@[simp] theorem mem_finiteSafeComponent
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start} :
    finish ∈ finiteSafeComponent start hbounded ↔
      finish ∈ safeComponent start := by
  simp [finiteSafeComponent]

def gridNeighbours (p : LatticePoint) : Finset LatticePoint :=
  Finset.univ.image (gridStep p)

noncomputable def finiteSafeComponentFrontier
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) : Finset LatticePoint :=
  let component := finiteSafeComponent start hbounded
  (component.biUnion gridNeighbours).filter fun q ↦ q ∉ component

@[simp] theorem mem_gridNeighbours_of_safe {p q : LatticePoint}
    (hp : SafePoint p) :
    q ∈ gridNeighbours p ↔ Adjacent p q := by
  constructor
  · intro hq
    simp only [gridNeighbours, Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨direction, hdirection⟩ := hq
    rw [← hdirection]
    exact adjacent_gridStep p direction hp
  · intro hpq
    obtain ⟨direction, hdirection⟩ := exists_gridDirection_of_adjacent hpq
    simp only [gridNeighbours, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨direction, hdirection⟩

@[simp] theorem mem_finiteSafeComponentFrontier
    {start q : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start} :
    q ∈ finiteSafeComponentFrontier start hbounded ↔
      q ∈ safeComponentFrontier start := by
  classical
  simp only [finiteSafeComponentFrontier, Finset.mem_filter,
    Finset.mem_biUnion, mem_finiteSafeComponent]
  constructor
  · rintro ⟨⟨p, hpComponent, hqNeighbour⟩, hqOutside⟩
    exact ⟨hqOutside, p, hpComponent,
      (mem_gridNeighbours_of_safe (safePoint_of_mem_safeComponent hpComponent)).mp
        hqNeighbour⟩
  · rintro ⟨hqOutside, p, hpComponent, hpq⟩
    exact ⟨⟨p, hpComponent,
      (mem_gridNeighbours_of_safe (safePoint_of_mem_safeComponent hpComponent)).mpr
        hpq⟩, hqOutside⟩

theorem safeComponentFrontier_not_safe
    {start q : LatticePoint} (hq : q ∈ safeComponentFrontier start) :
    ¬ SafePoint q := by
  rintro hqSafe
  rcases hq with ⟨hqOutside, p, hpComponent, hpq⟩
  obtain ⟨walk, hwalkSafe⟩ := hpComponent
  apply hqOutside
  refine ⟨walk.concat hpq, ?_⟩
  intro r hr
  rw [SimpleGraph.Walk.support_concat] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hwalkSafe r hr
  · have hrq : r = q := by simpa using hr
    simpa [hrq] using hqSafe

theorem primePair_of_mem_safeComponentFrontier_of_interiorVisible
    {start q : LatticePoint}
    (hq : q ∈ safeComponentFrontier start)
    (hvisible : InteriorVisible q) :
    PrimePair q := by
  by_contra hnotPrimePair
  exact safeComponentFrontier_not_safe hq <|
    (safePoint_iff_interiorVisible_not_primePair q).mpr
      ⟨hvisible, hnotPrimePair⟩

theorem primePair_not_mem_safeComponent
    {start q : LatticePoint} (hq : PrimePair q) :
    q ∉ safeComponent start := by
  rintro ⟨walk, hwalkSafe⟩
  have hqSupport : q ∈ walk.support := by
    simpa using walk.getVert_mem_support walk.length
  have hqSafe := hwalkSafe q hqSupport
  exact (safePoint_iff_interiorVisible_not_primePair q).mp hqSafe |>.2 hq

/--
The first deleted point of the escaping full-visible path is a vertex of the
actual outer vertex boundary of the bounded safe component.  The predecessor
is reached by the literal safe prefix of that same walk.
-/
theorem exists_primePair_on_safeComponentFrontier
    (start : LatticePoint)
    (hstart : SafePoint start)
    (hvisible : ArbitrarilyFarInteriorVisibleReachable start)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    ∃ q, q ∈ safeComponentFrontier start ∧ PrimePair q := by
  classical
  obtain ⟨_bound, _finish, _hfar, walk, _hwalkPath, first,
      hfirstLength, hfirstPrime, hbeforeSafe⟩ :=
    exists_first_primePair_on_fullVisible_escape start hvisible hbounded
  have hfirstPositive : 0 < first := by
    by_contra hnotPositive
    have hfirstZero : first = 0 := by omega
    have hstartPrime : PrimePair start := by
      simpa [hfirstZero] using hfirstPrime
    exact (safePoint_iff_interiorVisible_not_primePair start).mp hstart |>.2
      hstartPrime
  let predecessor := walk.getVert (first - 1)
  let q := walk.getVert first
  have hpredecessorReachable : predecessor ∈ safeComponent start := by
    let initialWalk : latticeGraph.Walk start predecessor :=
      walk.take (first - 1)
    have hinitialSafe : ∀ p, p ∈ initialWalk.support → SafePoint p := by
      intro p hp
      obtain ⟨index, hindexPoint, hindexLength⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hp
      have hinitialLength : initialWalk.length = first - 1 := by
        simpa [initialWalk, SimpleGraph.Walk.take_length,
          Nat.min_eq_left (by omega : first - 1 ≤ walk.length)]
      have hindexBefore : index < first := by
        rw [hinitialLength] at hindexLength
        omega
      have hindexLe : index ≤ first - 1 := by omega
      have hindexPointOriginal : walk.getVert index = p := by
        rw [← hindexPoint]
        simp [initialWalk, SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right hindexLe]
      rw [← hindexPointOriginal]
      exact hbeforeSafe index hindexBefore
    exact ⟨initialWalk, hinitialSafe⟩
  have hadjacent : Adjacent predecessor q := by
    have hindex : first - 1 < walk.length := by omega
    have hadj := walk.adj_getVert_succ hindex
    have hstep : first - 1 + 1 = first := by omega
    simpa [predecessor, q, hstep] using hadj
  refine ⟨q, ⟨?_, predecessor, hpredecessorReachable, hadjacent⟩, ?_⟩
  · exact primePair_not_mem_safeComponent hfirstPrime
  · exact hfirstPrime

end Erdos1212Kernel
