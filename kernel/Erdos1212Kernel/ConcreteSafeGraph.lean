import Erdos1212Kernel.FiniteReachability

namespace Erdos1212Kernel

/-!
# The concrete deleted-visible graph

This file removes the first semantic abstraction at the boundary of the
Erdos 1212 statement.  Above the two coordinate axes, a visible lattice point
fails to be safe exactly when both coordinates are prime.  Consequently, if
an unbounded full-visible walk leaves a bounded safe component, an actual
prime--prime vertex occurs on that same walk.  No contour relaxation or
periodic surrogate is used.
-/

def InteriorVisible (p : LatticePoint) : Prop :=
  1 < p.x ∧ 1 < p.y ∧ Visible p

def PrimePair (p : LatticePoint) : Prop :=
  Nat.Prime p.x ∧ Nat.Prime p.y

theorem composite_iff_not_prime_of_one_lt {n : Nat} (hn : 1 < n) :
    Composite n ↔ ¬ Nat.Prime n := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact Nat.not_prime_mul (by omega) (by omega)
  · intro hnprime
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ n)).mp hnprime
    refine ⟨a, b, ?_, ?_, hab.symm⟩ <;> nlinarith

theorem safePoint_iff_interiorVisible_not_primePair (p : LatticePoint) :
    SafePoint p ↔ InteriorVisible p ∧ ¬ PrimePair p := by
  constructor
  · rintro ⟨hx, hy, hvis, hcomposite⟩
    refine ⟨⟨hx, hy, hvis⟩, ?_⟩
    rintro ⟨hpx, hpy⟩
    rcases hcomposite with hxcomp | hycomp
    · exact (composite_iff_not_prime_of_one_lt hx).mp hxcomp hpx
    · exact (composite_iff_not_prime_of_one_lt hy).mp hycomp hpy
  · rintro ⟨⟨hx, hy, hvis⟩, hnprimePair⟩
    refine ⟨hx, hy, hvis, ?_⟩
    by_cases hpx : Nat.Prime p.x
    · right
      apply (composite_iff_not_prime_of_one_lt hy).mpr
      intro hpy
      exact hnprimePair ⟨hpx, hpy⟩
    · left
      exact (composite_iff_not_prime_of_one_lt hx).mpr hpx

def ArbitrarilyFarInteriorVisibleReachable (start : LatticePoint) : Prop :=
  ∀ bound, ∃ finish : LatticePoint,
    (bound ≤ finish.x ∨ bound ≤ finish.y) ∧
    ∃ walk : latticeGraph.Walk start finish,
      ∀ p, p ∈ walk.support → InteriorVisible p

/--
The exact graph boundary forced by deleting prime--prime vertices.

If the starting point reaches arbitrarily far points through the full visible
graph but does not do so through the safe graph, then one of those very same
finite visible walks contains a prime--prime vertex.  This is the direct
component boundary statement needed before any quantitative rank estimate is
applied.
-/
theorem exists_primePair_on_fullVisible_escape
    (start : LatticePoint)
    (hvisible : ArbitrarilyFarInteriorVisibleReachable start)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    ∃ bound finish,
      (bound ≤ finish.x ∨ bound ≤ finish.y) ∧
      ∃ walk : latticeGraph.Walk start finish,
        walk.IsPath ∧
        (∀ p, p ∈ walk.support → InteriorVisible p) ∧
        ∃ p, p ∈ walk.support ∧ PrimePair p := by
  classical
  rw [ArbitrarilyFarSafeReachable] at hbounded
  push Not at hbounded
  obtain ⟨bound, hbound⟩ := hbounded
  obtain ⟨finish, hfar, rawWalk, hrawVisible⟩ := hvisible bound
  let walk : latticeGraph.Walk start finish := rawWalk.toPath
  have hwalkPath : walk.IsPath := rawWalk.toPath.property
  have hwalkSupport : walk.support ⊆ rawWalk.support :=
    rawWalk.support_toPath_subset
  have hwalkVisible : ∀ p, p ∈ walk.support → InteriorVisible p := by
    intro p hp
    exact hrawVisible p (hwalkSupport hp)
  refine ⟨bound, finish, hfar, walk, hwalkPath, hwalkVisible, ?_⟩
  obtain ⟨p, hp, hpUnsafe⟩ := hbound finish hfar walk
  refine ⟨p, hp, ?_⟩
  by_contra hpNotPrimePair
  exact hpUnsafe <|
    (safePoint_iff_interiorVisible_not_primePair p).mpr
      ⟨hwalkVisible p hp, hpNotPrimePair⟩

/--
The prime--prime cut can be taken at the first actual deleted vertex of the
same full-visible walk.  Every earlier vertex is safe, so this is a literal
first-anchor cut rather than a marginal counting surrogate.
-/
theorem exists_first_primePair_on_fullVisible_escape
    (start : LatticePoint)
    (hvisible : ArbitrarilyFarInteriorVisibleReachable start)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) :
    ∃ bound finish,
      (bound ≤ finish.x ∨ bound ≤ finish.y) ∧
      ∃ walk : latticeGraph.Walk start finish,
        walk.IsPath ∧
        ∃ first,
          first ≤ walk.length ∧
          PrimePair (walk.getVert first) ∧
          ∀ s < first, SafePoint (walk.getVert s) := by
  classical
  obtain ⟨bound, finish, hfar, walk, hwalkPath,
      hwalkVisible, p, hp, hpPrimePair⟩ :=
    exists_primePair_on_fullVisible_escape start hvisible hbounded
  have hpUnsafe : ¬ SafePoint p := by
    intro hpSafe
    exact (safePoint_iff_interiorVisible_not_primePair p).mp hpSafe |>.2 hpPrimePair
  obtain ⟨index, hindexPoint, hindexLength⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hp
  have hexists :
      ∃ index, index ≤ walk.length ∧ ¬ SafePoint (walk.getVert index) :=
    ⟨index, hindexLength, hindexPoint.symm ▸ hpUnsafe⟩
  let first := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  refine ⟨bound, finish, hfar, walk, hwalkPath, first, hfirst.1, ?_, ?_⟩
  · have hfirstVisible : InteriorVisible (walk.getVert first) := by
      exact hwalkVisible _ (walk.getVert_mem_support first)
    by_contra hnotPrimePair
    exact hfirst.2 <|
      (safePoint_iff_interiorVisible_not_primePair _).mpr
        ⟨hfirstVisible, hnotPrimePair⟩
  · intro s hs
    by_contra hsUnsafe
    have hsLength : s ≤ walk.length := hs.le.trans hfirst.1
    exact Nat.find_min hexists hs ⟨hsLength, hsUnsafe⟩

end Erdos1212Kernel
