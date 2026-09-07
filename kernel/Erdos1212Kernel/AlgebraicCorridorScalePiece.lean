import Erdos1212Kernel.AlgebraicCorridorFiniteChain
import Erdos1212Kernel.AlgebraicCorridorCrossScaleConnection

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

/-- The actual first and last selected crossings, together with their finite
connection at one scale. The crossings are retained for cross-scale gluing. -/
structure CorridorScalePiece (N α : ℝ) (M : ℕ) where
  firstLeft : LatticePoint
  firstRight : LatticePoint
  lastLeft : LatticePoint
  lastRight : LatticePoint
  first : CorridorSafeWalk firstLeft firstRight
  last : CorridorSafeWalk lastLeft lastRight
  first_left : firstLeft.x = (corridorSquare N α M).left
  first_right : firstRight.x = (corridorSquare N α M).right
  last_left : lastLeft.x = (corridorSquare N α (2 * M)).left
  last_right : lastRight.x = (corridorSquare N α (2 * M)).right
  first_contains : ∀ p ∈ first.walk.support, (corridorSquare N α M).Contains p
  last_contains : ∀ p ∈ last.walk.support, (corridorSquare N α (2 * M)).Contains p
  spine : CorridorSafeWalk firstRight lastRight
  spine_corridor : ∀ p ∈ spine.walk.support, directionCorridor N α p

theorem eventually_scalePiece_exists :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ M : ℕ, (M : ℝ) = N →
        Nonempty (CorridorScalePiece N α M) := by
  filter_upwards [eventually_heightGrid_safe_chain, eventually_squareHalfSide_bounds]
    with N hchain hside
  intro α hα havoid M hM
  obtain ⟨a, b, crossing, ha, hb, hc, hpaths⟩ := hchain α hα havoid M hM
  let k := heightGridLast M (squareStep N)
  have hk : heightGrid M (squareStep N) k = 2 * M :=
    heightGrid_last M (squareStep N) hside.2.2
  obtain ⟨path, hp⟩ := hpaths k
  exact ⟨{
    firstLeft := a 0
    firstRight := b 0
    lastLeft := a k
    lastRight := b k
    first := crossing 0
    last := crossing k
    first_left := by simpa using ha 0
    first_right := by simpa using hb 0
    last_left := by simpa only [hk] using ha k
    last_right := by simpa only [hk] using hb k
    first_contains := by simpa using hc 0
    last_contains := by simpa only [hk] using hc k
    spine := path
    spine_corridor := hp }⟩

/-- The paper's finite within-scale connection followed by its endpoint bridge.
No walk or intersection input is requested beyond the two actual scale pieces. -/
theorem eventually_scalePieces_connect :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance (2 * N) α → ∀ M : ℕ, (M : ℝ) = N →
      ∀ (small : CorridorScalePiece N α M) (large : CorridorScalePiece (2 * N) α (2 * M)),
      ∃ v : CorridorSafeWalk small.firstRight large.firstRight,
        ∀ p ∈ v.walk.support, directionCorridor N α p ∨ directionCorridor (2 * N) α p := by
  filter_upwards [eventually_crossScale_crossings_connected,
    eventually_corridorSquare_contained, eventually_large_domain] with N hconnect hcont hdom
  intro α hα havoid M hM small large
  have ht : ((2 * M : ℕ) : ℝ) = 2 * N := by simp [hM]
  obtain ⟨bridge, hb⟩ := hconnect α hα havoid (2 * M) ht small.last large.first
    small.last_left small.last_right large.first_left large.first_right
    small.last_contains large.first_contains
  let w := (small.spine.walk.append small.last.walk.reverse).append bridge.walk
  have hmem : ∀ p ∈ w.support,
      p ∈ small.spine.walk.support ∨ p ∈ small.last.walk.support ∨ p ∈ bridge.walk.support := by
    intro p hp
    simp only [w, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
    tauto
  have hsafe : ∀ p ∈ w.support, SafePoint p := by
    intro p hp
    rcases hmem p hp with hp | hp | hp
    · exact small.spine.safe p hp
    · exact small.last.safe p hp
    · exact bridge.safe p hp
  refine ⟨⟨w, hsafe⟩, ?_⟩
  intro p hp
  rcases hmem p hp with hp | hp | hp
  · exact Or.inl (small.spine_corridor p hp)
  · exact Or.inl ((hcont α hα (2 * M) (by linarith [hdom.1]) ht.le p
      (small.last_contains p hp)).1)
  · exact Or.inr (hb p hp)

end
end Erdos1212Kernel.CorridorScale
