import Erdos1212Kernel.AlgebraicCorridorDyadicComparison
import Erdos1212Kernel.AlgebraicCorridorAdjacentProduction

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

/-- The paper's endpoint bridge: the smaller horizontal interval and the
larger vertical interval, with the same center at height 2N. -/
def crossScaleBridge (N α : ℝ) (t : ℕ) : CorridorRectangle where
  left := (corridorSquare N α t).left
  right := (corridorSquare N α t).right
  bottom := (corridorSquare (2 * N) α t).bottom
  top := (corridorSquare (2 * N) α t).top
  horizontal := (corridorSquare N α t).horizontal
  vertical := (corridorSquare (2 * N) α t).vertical

theorem crossScaleBridge_subset_large {N α : ℝ} {t : ℕ}
    (hh : squareHalfSide N ≤ squareHalfSide (2 * N)) {p : LatticePoint}
    (hp : (crossScaleBridge N α t).Contains p) :
    (corridorSquare (2 * N) α t).Contains p := by
  rcases hp with ⟨hl, hr, hb, ht⟩
  dsimp [CorridorRectangle.Contains, crossScaleBridge, corridorSquare] at hl hr hb ht ⊢
  exact ⟨by omega, by omega, hb, ht⟩

theorem eventually_crossScaleBridge_safe_vertical :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance (2 * N) α → ∀ t : ℕ, (t : ℝ) = 2 * N →
        (crossScaleBridge N α t).SafeVerticalCrossing := by
  have hdouble : Tendsto (fun N : ℝ => 2 * N) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [eventually_dyadic_squareHalfSide_comparison,
    eventually_dyadic_bridge_width, eventually_squareHalfSide_bounds,
    hdouble.eventually eventually_square_geometry_inputs,
    hdouble.eventually eventually_corridorSquare_contained,
    hdouble.eventually eventually_contained_rectangle_crossings,
    eventually_large_domain] with N hcomp hwidth hside hgeom hcont hcross hdom
  intro α hα havoid t ht
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hcenter : squareHalfSide N ≤ squareCenter α t :=
    hcomp.1.trans (hgeom.2 α hα t ht.ge).2
  have hc : ∀ p, (crossScaleBridge N α t).Contains p → directionCorridor (2 * N) α p := by
    intro p hp
    exact (hcont α hα t ht.ge (by linarith) p
      (crossScaleBridge_subset_large hcomp.1 hp)).1
  apply (hcross α (crossScaleBridge N α t) havoid hc).2
  · dsimp [crossScaleBridge, corridorSquare]
    have hh := hside.1
    omega
  · have heq : (crossScaleBridge N α t).right - (crossScaleBridge N α t).left + 1 =
        2 * squareHalfSide N + 1 := by
      dsimp [crossScaleBridge, corridorSquare]
      omega
    rw [heq]
    exact_mod_cast hwidth.le

end
end Erdos1212Kernel.CorridorScale
