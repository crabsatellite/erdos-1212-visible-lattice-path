import Erdos1212Kernel.AlgebraicCorridorSquareOverlap

namespace Erdos1212Kernel.CorridorScale
noncomputable section

theorem adjacentSquareBridge_errors {N α : ℝ} (hα : 0 ≤ α) {t u : ℕ}
    (htu : t ≤ u)
    (hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right)
    (hstep : u - t ≤ squareStep N) {p : LatticePoint}
    (hp : (adjacentSquareBridge N α t u htu hoverlap).Contains p) :
    |(p.x : ℝ) - (squareCenter α t : ℝ)| ≤ 5 * (squareHalfSide N : ℝ) / 4 ∧
      |(p.y : ℝ) - (t : ℝ)| ≤ 5 * (squareHalfSide N : ℝ) / 4 := by
  have hm := squareCenter_mono hα htu
  have hxl : squareCenter α u - squareHalfSide N ≤ p.x := hp.1
  have hxu : p.x ≤ squareCenter α t + squareHalfSide N := hp.2.1
  have hyl : t - squareHalfSide N ≤ p.y := hp.2.2.1
  have hyu : p.y ≤ u + squareHalfSide N := hp.2.2.2
  have hsteps : 10 * (u - t) ≤ squareHalfSide N :=
    (Nat.mul_le_mul_left 10 hstep).trans (Nat.mul_div_le _ _)
  have hxn : squareCenter α t ≤ p.x + squareHalfSide N := by omega
  have hyn : t ≤ p.y + squareHalfSide N := by omega
  have hxr : (squareCenter α t : ℝ) ≤ (p.x : ℝ) + squareHalfSide N := by exact_mod_cast hxn
  have hyr : (t : ℝ) ≤ (p.y : ℝ) + squareHalfSide N := by exact_mod_cast hyn
  have hxur : (p.x : ℝ) ≤ (squareCenter α t : ℝ) + squareHalfSide N := by exact_mod_cast hxu
  have hyur : (p.y : ℝ) ≤ (u : ℝ) + squareHalfSide N := by exact_mod_cast hyu
  have hsr : 10 * ((u : ℝ) - t) ≤ (squareHalfSide N : ℝ) := by exact_mod_cast hsteps
  have hh : (0 : ℝ) ≤ squareHalfSide N := by positivity
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem eventually_expanded_square_errors_contained :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      ∀ t : ℕ, N ≤ (t : ℝ) → (t : ℝ) ≤ 2 * N →
      ∀ p : LatticePoint,
        |(p.x : ℝ) - (squareCenter α t : ℝ)| ≤ 5 * (squareHalfSide N : ℝ) / 4 →
        |(p.y : ℝ) - (t : ℝ)| ≤ 5 * (squareHalfSide N : ℝ) / 4 →
        directionCorridor N α p := by
  filter_upwards [eventually_large_domain, eventually_squareHalfSide_bounds]
    with N hdom hside
  intro α hα t ht htu p hx hy
  have hαlow : (4 / 3 : ℝ) < α := hα.1
  have hαup : α < (5 / 3 : ℝ) := hα.2
  have hαpos : 0 ≤ α := by linarith
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hr : 0 < rho N := Real.exp_pos _
  have hh10 : (10 : ℝ) ≤ squareHalfSide N := by exact_mod_cast hside.1
  have hhN := hside.2.1
  have hhwidth : (squareHalfSide N : ℝ) ≤ N * rho N / 100 := Nat.floor_le (by positivity)
  have hc := square_center_error hαpos t
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hl := mul_le_mul_of_nonneg_right hαlow.le ht0
  have hu := mul_le_mul_of_nonneg_right hαup.le ht0
  have hxb := abs_le.mp hx
  have hyb := abs_le.mp hy
  have hcb := abs_le.mp hc
  have hpxLow : N / 2 ≤ (p.x : ℝ) := by linarith
  have hpxUp : (p.x : ℝ) ≤ 4 * N := by linarith
  have hpyLow : N / 2 ≤ (p.y : ℝ) := by linarith
  have hpyUp : (p.y : ℝ) ≤ 4 * N := by linarith
  have hyPos : (0 : ℝ) < p.y := by linarith
  have hlinear : |(p.x : ℝ) - α * p.y| ≤ 4 * (squareHalfSide N : ℝ) := by
    have ha := abs_add_le ((p.x : ℝ) - squareCenter α t) ((squareCenter α t : ℝ) - α * t)
    have hb := abs_add_le (((p.x : ℝ) - squareCenter α t) + ((squareCenter α t : ℝ) - α * t))
      (α * ((t : ℝ) - p.y))
    have hs : |α * ((t : ℝ) - p.y)| ≤ α * (5 * (squareHalfSide N : ℝ) / 4) := by
      rw [abs_mul, abs_of_nonneg hαpos, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hy hαpos
    rw [show ((p.x : ℝ) - squareCenter α t) + ((squareCenter α t : ℝ) - α * t) +
      α * ((t : ℝ) - p.y) = (p.x : ℝ) - α * p.y by ring] at hb
    nlinarith
  refine ⟨hpxLow, hpxUp, hpyLow, hpyUp, ?_⟩
  rw [show (p.x : ℝ) / (p.y : ℝ) - α = ((p.x : ℝ) - α * p.y) / p.y by field_simp,
    abs_div, abs_of_pos hyPos]
  apply (div_le_iff₀ hyPos).mpr
  have hs := mul_le_mul_of_nonneg_left hpyLow hr.le
  nlinarith

theorem eventually_adjacentSquareBridge_contained :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      ∀ t u : ℕ, N ≤ (t : ℝ) → (t : ℝ) ≤ 2 * N →
      ∀ htu : t ≤ u,
      ∀ hoverlap : (corridorSquare N α u).left ≤ (corridorSquare N α t).right,
      u - t ≤ squareStep N →
      ∀ p, (adjacentSquareBridge N α t u htu hoverlap).Contains p → directionCorridor N α p := by
  filter_upwards [eventually_expanded_square_errors_contained] with N h
  intro α hα t u ht htuMax htu hoverlap hstep p hp
  have hα0 : 0 ≤ α := by have hh := hα.1; change 4 / 3 < α at hh; linarith
  obtain ⟨hx, hy⟩ := adjacentSquareBridge_errors hα0 htu hoverlap hstep hp
  exact h α hα t ht htuMax p hx hy

end
end Erdos1212Kernel.CorridorScale
