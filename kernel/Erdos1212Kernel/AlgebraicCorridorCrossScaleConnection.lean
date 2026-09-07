import Erdos1212Kernel.AlgebraicCorridorCrossScaleBridge

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

theorem corridorSquare_subset_double {N α : ℝ} {t : ℕ}
    (hh : squareHalfSide N ≤ squareHalfSide (2 * N)) {p : LatticePoint}
    (hp : (corridorSquare N α t).Contains p) :
    (corridorSquare (2 * N) α t).Contains p := by
  rcases hp with ⟨hl, hr, hb, ht⟩
  dsimp [CorridorRectangle.Contains, corridorSquare] at hl hr hb ht ⊢
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Intersect the original horizontal crossings with the original nested
endpoint bridge, retaining their literal supports in the resulting safe walk. -/
theorem crossScaleBridge_connects {N α : ℝ} {t : ℕ}
    (hh : 0 < squareHalfSide N)
    (hmono : squareHalfSide N ≤ squareHalfSide (2 * N))
    (ht : squareHalfSide (2 * N) < t)
    {a b c d e f : LatticePoint}
    (left : CorridorSafeWalk a b) (bridge : CorridorSafeWalk c d)
    (right : CorridorSafeWalk e f)
    (ha : a.x = (corridorSquare N α t).left)
    (hb : b.x = (corridorSquare N α t).right)
    (he : e.x = (corridorSquare (2 * N) α t).left)
    (hf : f.x = (corridorSquare (2 * N) α t).right)
    (hc : c.y = (crossScaleBridge N α t).bottom)
    (hd : d.y = (crossScaleBridge N α t).top)
    (hl : ∀ p ∈ left.walk.support, (corridorSquare N α t).Contains p)
    (hm : ∀ p ∈ bridge.walk.support, (crossScaleBridge N α t).Contains p)
    (hr : ∀ p ∈ right.walk.support, (corridorSquare (2 * N) α t).Contains p) :
    ∃ joined : CorridorSafeWalk a f, ∀ p ∈ joined.walk.support,
      p ∈ left.walk.support ∨ p ∈ bridge.walk.support ∨ p ∈ right.walk.support := by
  have hwidth : (crossScaleBridge N α t).left < (crossScaleBridge N α t).right := by
    dsimp [crossScaleBridge, corridorSquare]
    omega
  obtain ⟨p, hpl, hpm⟩ := (corridorSquare N α t).bridge_crossing_intersects
    (crossScaleBridge N α t)
    (by dsimp [corridorSquare]; omega) (by dsimp [corridorSquare]; omega)
    hwidth (by rfl) (by rfl)
    (by dsimp [crossScaleBridge, corridorSquare]; omega)
    (by dsimp [crossScaleBridge, corridorSquare]; omega)
    left.walk bridge.walk ha hb hc hd hl hm
  obtain ⟨q, hqr, hqm⟩ := (corridorSquare (2 * N) α t).bridge_crossing_intersects
    (crossScaleBridge N α t)
    (by dsimp [corridorSquare]; omega) (by dsimp [corridorSquare]; omega)
    hwidth
    (by dsimp [crossScaleBridge, corridorSquare]; omega)
    (by dsimp [crossScaleBridge, corridorSquare]; omega) (by rfl) (by rfl)
    right.walk bridge.walk he hf hc hd hr hm
  exact corridor_safe_three_walk_bridge left bridge right hpl hpm hqm hqr

theorem eventually_crossScale_crossings_connected :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance (2 * N) α → ∀ t : ℕ, (t : ℝ) = 2 * N →
      ∀ {a b e f : LatticePoint} (left : CorridorSafeWalk a b)
        (right : CorridorSafeWalk e f),
      a.x = (corridorSquare N α t).left → b.x = (corridorSquare N α t).right →
      e.x = (corridorSquare (2 * N) α t).left → f.x = (corridorSquare (2 * N) α t).right →
      (∀ p ∈ left.walk.support, (corridorSquare N α t).Contains p) →
      (∀ p ∈ right.walk.support, (corridorSquare (2 * N) α t).Contains p) →
      ∃ joined : CorridorSafeWalk a f,
        ∀ p ∈ joined.walk.support, directionCorridor (2 * N) α p := by
  have hdouble : Tendsto (fun N : ℝ => 2 * N) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [eventually_crossScaleBridge_safe_vertical,
    eventually_dyadic_squareHalfSide_comparison, eventually_squareHalfSide_bounds,
    hdouble.eventually eventually_square_geometry_inputs,
    hdouble.eventually eventually_corridorSquare_contained,
    eventually_large_domain] with N hprod hcomp hside hgeom hcont hdom
  intro α hα havoid t ht a b e f left right ha hb he hf hl hr
  obtain ⟨c, d, hc, hd, w, hw⟩ := hprod α hα havoid t ht
  let bridge : CorridorSafeWalk c d := ⟨w, fun p hp => (hw p hp).2⟩
  have hhalf : squareHalfSide (2 * N) < t := (hgeom.2 α hα t ht.ge).1
  have hh : 0 < squareHalfSide N := by have h := hside.1; omega
  obtain ⟨joined, hj⟩ := crossScaleBridge_connects hh hcomp.1 hhalf
    left bridge right ha hb he hf hc hd hl (fun p hp => (hw p hp).1) hr
  refine ⟨joined, ?_⟩
  intro p hp
  apply (hcont α hα t ht.ge (by linarith [hdom.1]) p ?_).1
  rcases hj p hp with hp | hp | hp
  · exact corridorSquare_subset_double hcomp.1 (hl p hp)
  · exact crossScaleBridge_subset_large hcomp.1 (hw p hp).1
  · exact hr p hp

end
end Erdos1212Kernel.CorridorScale
