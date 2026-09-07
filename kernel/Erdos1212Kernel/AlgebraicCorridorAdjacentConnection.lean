import Erdos1212Kernel.AlgebraicCorridorBridgeIntersection
import Erdos1212Kernel.AlgebraicCorridorBridgeWalk
import Erdos1212Kernel.AlgebraicCorridorSquareOverlap

namespace Erdos1212Kernel.CorridorScale
noncomputable section

/-- Connect the actual chosen crossings through the paper's adjacent-square
bridge. The output uses only vertices of those three original safe walks. -/
theorem adjacentSquareBridge_connects {N α : ℝ} (hα : 0 ≤ α) {t u : ℕ}
    (htu : t ≤ u)
    (hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right)
    (hwidth : (corridorSquare N α u).left < (corridorSquare N α t).right)
    (hh : 0 < squareHalfSide N) (ht : squareHalfSide N < t)
    {a b c d e f : LatticePoint}
    (left : CorridorSafeWalk a b) (bridge : CorridorSafeWalk c d)
    (right : CorridorSafeWalk e f)
    (ha : a.x = (corridorSquare N α t).left)
    (hb : b.x = (corridorSquare N α t).right)
    (he : e.x = (corridorSquare N α u).left)
    (hf : f.x = (corridorSquare N α u).right)
    (hc : c.y = (adjacentSquareBridge N α t u htu hoverlap).bottom)
    (hd : d.y = (adjacentSquareBridge N α t u htu hoverlap).top)
    (hl : ∀ p ∈ left.walk.support, (corridorSquare N α t).Contains p)
    (hm : ∀ p ∈ bridge.walk.support,
      (adjacentSquareBridge N α t u htu hoverlap).Contains p)
    (hr : ∀ p ∈ right.walk.support, (corridorSquare N α u).Contains p) :
    ∃ joined : CorridorSafeWalk a f, ∀ p ∈ joined.walk.support,
      p ∈ left.walk.support ∨ p ∈ bridge.walk.support ∨ p ∈ right.walk.support := by
  have hmono := squareCenter_mono hα htu
  obtain ⟨p, hpl, hpm⟩ := (corridorSquare N α t).bridge_crossing_intersects
    (adjacentSquareBridge N α t u htu hoverlap)
    (by dsimp [corridorSquare]; omega)
    (by dsimp [corridorSquare]; omega) hwidth
    (by dsimp [corridorSquare, adjacentSquareBridge]; omega) (by rfl)
    (by rfl) (by dsimp [corridorSquare, adjacentSquareBridge]; omega)
    left.walk bridge.walk ha hb hc hd hl hm
  obtain ⟨q, hqr, hqm⟩ := (corridorSquare N α u).bridge_crossing_intersects
    (adjacentSquareBridge N α t u htu hoverlap)
    (by dsimp [corridorSquare]; omega)
    (by dsimp [corridorSquare]; omega) hwidth
    (by rfl) (by dsimp [corridorSquare, adjacentSquareBridge]; omega)
    (by dsimp [corridorSquare, adjacentSquareBridge]; omega) (by rfl)
    right.walk bridge.walk he hf hc hd hr hm
  exact corridor_safe_three_walk_bridge left bridge right hpl hpm hqm hqr

end
end Erdos1212Kernel.CorridorScale
