import Erdos1212Kernel.AlgebraicCorridorSquareGeometry

namespace Erdos1212Kernel.CorridorScale
noncomputable section

theorem squareCenter_mono {α : ℝ} (hα : 0 ≤ α) {t u : ℕ} (htu : t ≤ u) :
    squareCenter α t ≤ squareCenter α u := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast htu) hα

theorem adjacent_squareCenter_displacement {N α : ℝ}
    (hα : α ∈ algebraicCorridorSlopeInterval) {t u : ℕ}
    (htu : t ≤ u) (hstep : u - t ≤ squareStep N) (hh : 12 ≤ squareHalfSide N) :
    ((squareCenter α u - squareCenter α t : ℕ) : ℝ) ≤
      (squareHalfSide N : ℝ) / 4 := by
  have hα0 : 0 ≤ α := by have h := hα.1; change 4 / 3 < α at h; linarith
  have hαup : α ≤ 5 / 3 := hα.2.le
  have hmono := squareCenter_mono hα0 htu
  have hfloorU : (squareCenter α u : ℝ) ≤ α * u :=
    Nat.floor_le (by positivity)
  have hfloorT : α * t < (squareCenter α t : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsteps : 10 * squareStep N ≤ squareHalfSide N := by
    exact Nat.mul_div_le _ _
  have hdiff : (u : ℝ) - t ≤ (squareHalfSide N : ℝ) / 10 := by
    have hn : 10 * (u - t) ≤ squareHalfSide N :=
      (Nat.mul_le_mul_left 10 hstep).trans hsteps
    have hr : 10 * ((u : ℝ) - t) ≤ (squareHalfSide N : ℝ) := by
      exact_mod_cast hn
    linarith
  have htR : (t : ℝ) ≤ u := by exact_mod_cast htu
  have hhR : (12 : ℝ) ≤ squareHalfSide N := by exact_mod_cast hh
  have hmul := mul_le_mul_of_nonneg_right hαup (sub_nonneg.mpr htR)
  rw [Nat.cast_sub hmono]
  nlinarith

theorem adjacent_square_horizontal_overlap {N α : ℝ}
    (hα : α ∈ algebraicCorridorSlopeInterval) {t u : ℕ}
    (htu : t ≤ u) (hstep : u - t ≤ squareStep N) (hh : 12 ≤ squareHalfSide N)
    (htCenter : squareHalfSide N ≤ squareCenter α t) :
    (corridorSquare N α u).left ≤ (corridorSquare N α t).right ∧
      7 * (squareHalfSide N : ℝ) / 4 ≤
        ((corridorSquare N α t).right : ℝ) - (corridorSquare N α u).left := by
  have hα0 : 0 ≤ α := by have h := hα.1; change 4 / 3 < α at h; linarith
  have hmono := squareCenter_mono hα0 htu
  have huCenter : squareHalfSide N ≤ squareCenter α u := htCenter.trans hmono
  have hdelta := adjacent_squareCenter_displacement hα htu hstep hh
  rw [Nat.cast_sub hmono] at hdelta
  have hgap : 7 * (squareHalfSide N : ℝ) / 4 ≤
      ((corridorSquare N α t).right : ℝ) - (corridorSquare N α u).left := by
    change 7 * (squareHalfSide N : ℝ) / 4 ≤
      ((squareCenter α t + squareHalfSide N : ℕ) : ℝ) -
        ((squareCenter α u - squareHalfSide N : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_sub huCenter]
    linarith
  refine ⟨?_, hgap⟩
  have hhNonneg : (0 : ℝ) ≤ squareHalfSide N := by positivity
  have hr : ((corridorSquare N α u).left : ℝ) ≤ (corridorSquare N α t).right := by
    linarith
  exact_mod_cast hr

def adjacentSquareBridge (N α : ℝ) (t u : ℕ)
    (htu : t ≤ u)
    (hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right) :
    CorridorRectangle where
  left := (corridorSquare N α u).left
  right := (corridorSquare N α t).right
  bottom := (corridorSquare N α t).bottom
  top := (corridorSquare N α u).top
  horizontal := hoverlap
  vertical := by dsimp [corridorSquare]; omega

theorem adjacentSquareBridge_vertical_span {N α : ℝ} {t u : ℕ}
    (htu : t ≤ u)
    (hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right)
    (hstep : u - t ≤ squareStep N) (ht : squareHalfSide N ≤ t) :
    ((adjacentSquareBridge N α t u htu hoverlap).top : ℝ) -
        (adjacentSquareBridge N α t u htu hoverlap).bottom ≤
      21 * (squareHalfSide N : ℝ) / 10 := by
  have hsteps : 10 * squareStep N ≤ squareHalfSide N := Nat.mul_div_le _ _
  have hn : 10 * (u - t) ≤ squareHalfSide N :=
    (Nat.mul_le_mul_left 10 hstep).trans hsteps
  have hr : 10 * ((u : ℝ) - t) ≤ (squareHalfSide N : ℝ) := by exact_mod_cast hn
  change ((u + squareHalfSide N : ℕ) : ℝ) -
    ((t - squareHalfSide N : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add, Nat.cast_sub ht]
  linarith

end
end Erdos1212Kernel.CorridorScale
