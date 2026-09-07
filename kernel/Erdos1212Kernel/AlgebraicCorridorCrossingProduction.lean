import Erdos1212Kernel.AlgebraicCorridorPolynomialTranspose
import Erdos1212Kernel.AlgebraicCorridorBridgeGeometry

namespace Erdos1212Kernel
noncomputable section
open CorridorScale

/-- Read the actual endpoint bounds from containment, rather than requiring
the global gluing consumer to supply them independently. -/
theorem CorridorRectangle.bounds_of_directionCorridor {N α : ℝ}
    (R : CorridorRectangle) (hN : 8 ≤ N)
    (h : ∀ p, R.Contains p → directionCorridor N α p) :
    2 < R.left ∧ 2 < R.bottom ∧
      Nat.floor (N / 2) ≤ R.left ∧ Nat.floor (N / 2) ≤ R.bottom ∧
      R.right ≤ Nat.floor (4 * N) ∧ R.top ≤ Nat.floor (4 * N) := by
  have hlo := h ⟨R.left, R.bottom⟩
    ⟨le_rfl, R.horizontal, le_rfl, R.vertical⟩
  have hhi := h ⟨R.right, R.top⟩
    ⟨R.horizontal, le_rfl, R.vertical, le_rfl⟩
  have hl : N / 2 ≤ (R.left : ℝ) := hlo.1
  have hb : N / 2 ≤ (R.bottom : ℝ) := hlo.2.2.1
  have hlf : Nat.floor (N / 2) ≤ R.left := by
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ N / 2)).trans hl
  have hbf : Nat.floor (N / 2) ≤ R.bottom := by
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ N / 2)).trans hb
  refine ⟨?_, ?_, hlf, hbf, Nat.le_floor hhi.2.1, Nat.le_floor hhi.2.2.2.1⟩
  · have hr : (2 : ℝ) < R.left := by linarith
    exact_mod_cast hr
  · have hr : (2 : ℝ) < R.bottom := by linarith
    exact_mod_cast hr

theorem CorridorScale.eventually_contained_rectangle_crossings :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ (α : ℝ) (R : CorridorRectangle),
      DirectionAvoidance N α →
      (∀ p, R.Contains p → directionCorridor N α p) →
      (R.bottom < R.top →
        N ^ (9 / 10 : ℝ) ≤ ((R.top - R.bottom + 1 : ℕ) : ℝ) →
        R.SafeHorizontalCrossing) ∧
      (R.left < R.right →
        N ^ (9 / 10 : ℝ) ≤ ((R.right - R.left + 1 : ℕ) : ℝ) →
        R.SafeVerticalCrossing) := by
  filter_upwards [eventually_safe_horizontal_crossing, eventually_safe_vertical_crossing,
    Filter.eventually_ge_atTop (8 : ℝ)] with N hh hv hN
  intro α R havoid hcorr
  obtain ⟨hl, hb, hlf, hbf, hrf, htf⟩ := R.bounds_of_directionCorridor hN hcorr
  exact ⟨fun hlt hsize => hh α R havoid hl (by omega) hlt hbf htf hsize hcorr,
    fun hlt hsize => hv α R havoid hb (by omega) hlt hlf hrf hsize hcorr⟩

namespace CorridorScale

theorem eventually_corridorSquare_safe_horizontal :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ t : ℕ, N ≤ (t : ℝ) → (t : ℝ) ≤ 2 * N →
        (corridorSquare N α t).SafeHorizontalCrossing := by
  filter_upwards [eventually_contained_rectangle_crossings,
    eventually_corridorSquare_contained, eventually_squareHalfSide_bounds,
    eventually_C_mul_nineTenths_lt_squareHalfSide 1] with N hcross hcont hside hsize
  intro α hα havoid t ht htu
  apply (hcross α (corridorSquare N α t) havoid
    (fun p hp => (hcont α hα t ht htu p hp).1)).1
  · dsimp [corridorSquare]
    have hh := hside.1
    omega
  · have hn : squareHalfSide N ≤
        (corridorSquare N α t).top - (corridorSquare N α t).bottom + 1 := by
      dsimp [corridorSquare]
      omega
    have hr : (squareHalfSide N : ℝ) ≤
        (( (corridorSquare N α t).top - (corridorSquare N α t).bottom + 1 : ℕ) : ℝ) :=
      by exact_mod_cast hn
    linarith

theorem eventually_adjacentSquareBridge_safe_vertical :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      DirectionAvoidance N α → ∀ t u : ℕ,
      N ≤ (t : ℝ) → (t : ℝ) ≤ 2 * N →
      ∀ htu : t ≤ u,
      ∀ hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right,
      u - t ≤ squareStep N → squareHalfSide N ≤ squareCenter α t →
      (adjacentSquareBridge N α t u htu hoverlap).SafeVerticalCrossing := by
  filter_upwards [eventually_contained_rectangle_crossings,
    eventually_adjacentSquareBridge_contained, eventually_large_domain,
    eventually_C_mul_nineTenths_lt_squareHalfSide 12] with N hcross hcont hdom hsize
  intro α hα havoid t u ht htuN htu hoverlap hstep hcenter
  have hpow : (1 : ℝ) ≤ N ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hdom.1.le (by norm_num)
  have hhR : (12 : ℝ) ≤ squareHalfSide N := by nlinarith
  have hh : 12 ≤ squareHalfSide N := by exact_mod_cast hhR
  have hgap := (adjacent_square_horizontal_overlap hα htu hstep hh hcenter).2
  have hwidthR : ((corridorSquare N α u).left : ℝ) <
      (corridorSquare N α t).right := by linarith
  have hwidth : (corridorSquare N α u).left < (corridorSquare N α t).right :=
    by exact_mod_cast hwidthR
  apply (hcross α (adjacentSquareBridge N α t u htu hoverlap) havoid
    (hcont α hα t u ht htuN htu hoverlap hstep)).2 hwidth
  change N ^ (9 / 10 : ℝ) ≤
    (((corridorSquare N α t).right - (corridorSquare N α u).left + 1 : ℕ) : ℝ)
  rw [Nat.cast_add, Nat.cast_sub hoverlap, Nat.cast_one]
  nlinarith

end CorridorScale
end
end Erdos1212Kernel
