import Erdos1212Kernel.AlgebraicCorridorCrossingProduction
import Erdos1212Kernel.AlgebraicCorridorAdjacentConnection

namespace Erdos1212Kernel.CorridorScale
noncomputable section

theorem eventually_square_geometry_inputs :
    ∀ᶠ N : ℝ in Filter.atTop, 12 ≤ squareHalfSide N ∧
      ∀ α ∈ algebraicCorridorSlopeInterval, ∀ t : ℕ, N ≤ (t : ℝ) →
        squareHalfSide N < t ∧ squareHalfSide N ≤ squareCenter α t := by
  filter_upwards [eventually_large_domain, eventually_squareHalfSide_bounds,
    eventually_C_mul_nineTenths_lt_squareHalfSide 12] with N hdom hside hlarge
  have hpow : (1 : ℝ) ≤ N ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hdom.1.le (by norm_num)
  have hh : 12 ≤ squareHalfSide N := by
    have hr : (12 : ℝ) ≤ squareHalfSide N := by nlinarith
    exact_mod_cast hr
  refine ⟨hh, ?_⟩
  intro α hα t ht
  have hhtR : (squareHalfSide N : ℝ) < t := by
    have h := hside.2.1
    linarith [hdom.1]
  have hht : squareHalfSide N < t := by exact_mod_cast hhtR
  have hαone : (1 : ℝ) ≤ α := by
    have h : (4 / 3 : ℝ) < α := hα.1
    linarith
  have htc : t ≤ squareCenter α t := Nat.le_floor (by
    have h := mul_le_mul_of_nonneg_right hαone (show (0 : ℝ) ≤ t by positivity)
    simpa using h)
  exact ⟨hht, hht.le.trans htc⟩

/-- Produce and consume the actual vertical bridge, joining any chosen safe
horizontal crossings of consecutive squares. All output vertices remain in
the original direction corridor. -/
theorem eventually_adjacent_crossings_connected :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ t u : ℕ,
      N ≤ (t : ℝ) → (u : ℝ) ≤ 2 * N → t ≤ u → u - t ≤ squareStep N →
      ∀ {a b e f : LatticePoint} (left : CorridorSafeWalk a b)
        (right : CorridorSafeWalk e f),
      a.x = (corridorSquare N α t).left → b.x = (corridorSquare N α t).right →
      e.x = (corridorSquare N α u).left → f.x = (corridorSquare N α u).right →
      (∀ p ∈ left.walk.support, (corridorSquare N α t).Contains p) →
      (∀ p ∈ right.walk.support, (corridorSquare N α u).Contains p) →
      ∃ joined : CorridorSafeWalk a f,
        ∀ p ∈ joined.walk.support, directionCorridor N α p := by
  filter_upwards [eventually_square_geometry_inputs,
    eventually_adjacentSquareBridge_safe_vertical, eventually_corridorSquare_contained,
    eventually_adjacentSquareBridge_contained] with N hgeom hvert hsquare hbridge
  intro α hα havoid t u ht hu htu hstep a b e f left right ha hb he hf hl hr
  have htuR : (t : ℝ) ≤ u := by exact_mod_cast htu
  have htMax : (t : ℝ) ≤ 2 * N := htuR.trans hu
  have huMin : N ≤ (u : ℝ) := ht.trans htuR
  obtain ⟨hht, hcenter⟩ := hgeom.2 α hα t ht
  obtain ⟨hoverlap, hgap⟩ :=
    adjacent_square_horizontal_overlap hα htu hstep hgeom.1 hcenter
  have hhR : (12 : ℝ) ≤ squareHalfSide N := by exact_mod_cast hgeom.1
  have hwidth : (corridorSquare N α u).left < (corridorSquare N α t).right := by
    have hR : ((corridorSquare N α u).left : ℝ) <
        (corridorSquare N α t).right := by linarith
    exact_mod_cast hR
  obtain ⟨c, d, hc, hd, w, hw⟩ :=
    hvert α hα havoid t u ht htMax htu hoverlap hstep hcenter
  let bridge : CorridorSafeWalk c d := ⟨w, fun p hp => (hw p hp).2⟩
  have hα0 : 0 ≤ α := by
    have h : (4 / 3 : ℝ) < α := hα.1
    linarith
  obtain ⟨joined, hj⟩ := adjacentSquareBridge_connects hα0 htu hoverlap hwidth
    (by omega) hht left bridge right ha hb he hf hc hd hl
      (fun p hp => (hw p hp).1) hr
  refine ⟨joined, ?_⟩
  intro p hp
  rcases hj p hp with hp | hp | hp
  · exact (hsquare α hα t ht htMax p (hl p hp)).1
  · exact hbridge α hα t u ht htMax htu hoverlap hstep p (hw p hp).1
  · exact (hsquare α hα u huMin hu p (hr p hp)).1

end
end Erdos1212Kernel.CorridorScale
