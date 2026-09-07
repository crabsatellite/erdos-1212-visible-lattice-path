import Erdos1212Kernel.AlgebraicCorridorPolynomialTranspose
import Erdos1212Kernel.AlgebraicCorridorScaleGluing

namespace Erdos1212Kernel
noncomputable section

/-- Join any two vertices on a supplied walk without leaving its support. -/
theorem walk_between_support_vertices
    {G : SimpleGraph LatticePoint} {a b p q : LatticePoint}
    (w : G.Walk a b) (hp : p ∈ w.support) (hq : q ∈ w.support) :
    ∃ v : G.Walk p q, v.support ⊆ w.support := by
  classical
  let u := w.takeUntil p hp
  let v := w.takeUntil q hq
  refine ⟨u.reverse.append v, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · have hzu : z ∈ u.support := by simpa using hz
    exact (w.isSubwalk_takeUntil hp).support_subset hzu
  · exact (w.isSubwalk_takeUntil hq).support_subset hz

/-- The literal three-walk concatenation used for adjacent squares: travel
along the first crossing, the bridge, then the second crossing. -/
theorem corridor_three_walk_bridge
    {a b c d e f p q : LatticePoint}
    (left : latticeGraph.Walk a b) (bridge : latticeGraph.Walk c d)
    (right : latticeGraph.Walk e f)
    (hpLeft : p ∈ left.support) (hpBridge : p ∈ bridge.support)
    (hqBridge : q ∈ bridge.support) (hqRight : q ∈ right.support) :
    ∃ joined : latticeGraph.Walk a f,
      ∀ z ∈ joined.support,
        z ∈ left.support ∨ z ∈ bridge.support ∨ z ∈ right.support := by
  classical
  obtain ⟨middle, hmiddle⟩ := walk_between_support_vertices bridge hpBridge hqBridge
  obtain ⟨last, hlast⟩ := walk_between_support_vertices right hqRight right.end_mem_support
  let first := left.takeUntil p hpLeft
  refine ⟨(first.append middle).append last, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact Or.inl ((left.isSubwalk_takeUntil hpLeft).support_subset hz)
    · exact Or.inr (Or.inl (hmiddle hz))
  · exact Or.inr (Or.inr (hlast hz))

theorem corridor_safe_three_walk_bridge
    {a b c d e f p q : LatticePoint}
    (left : CorridorSafeWalk a b) (bridge : CorridorSafeWalk c d)
    (right : CorridorSafeWalk e f)
    (hpLeft : p ∈ left.walk.support) (hpBridge : p ∈ bridge.walk.support)
    (hqBridge : q ∈ bridge.walk.support) (hqRight : q ∈ right.walk.support) :
    ∃ joined : CorridorSafeWalk a f,
      ∀ z ∈ joined.walk.support,
        z ∈ left.walk.support ∨ z ∈ bridge.walk.support ∨ z ∈ right.walk.support := by
  obtain ⟨w, hw⟩ := corridor_three_walk_bridge left.walk bridge.walk right.walk
    hpLeft hpBridge hqBridge hqRight
  have hsafe : ∀ z ∈ w.support, SafePoint z := by
    intro z hz
    rcases hw z hz with hz | hz | hz
    · exact left.safe z hz
    · exact bridge.safe z hz
    · exact right.safe z hz
  exact ⟨⟨w, hsafe⟩, hw⟩

/-- Any pointwise corridor constraint on the original three paths is retained. -/
theorem corridor_three_walk_bridge_preserves
    {a b c d e f p q : LatticePoint} (P : LatticePoint → Prop)
    (left : CorridorSafeWalk a b) (bridge : CorridorSafeWalk c d)
    (right : CorridorSafeWalk e f)
    (hpLeft : p ∈ left.walk.support) (hpBridge : p ∈ bridge.walk.support)
    (hqBridge : q ∈ bridge.walk.support) (hqRight : q ∈ right.walk.support)
    (hleft : ∀ z ∈ left.walk.support, P z)
    (hbridge : ∀ z ∈ bridge.walk.support, P z)
    (hright : ∀ z ∈ right.walk.support, P z) :
    ∃ joined : CorridorSafeWalk a f, ∀ z ∈ joined.walk.support, P z := by
  obtain ⟨joined, hj⟩ := corridor_safe_three_walk_bridge left bridge right
    hpLeft hpBridge hqBridge hqRight
  refine ⟨joined, ?_⟩
  intro z hz
  rcases hj z hz with hz | hz | hz
  · exact hleft z hz
  · exact hbridge z hz
  · exact hright z hz

end
end Erdos1212Kernel
