import Erdos1212Kernel.AlgebraicCorridorSquareScale

namespace Erdos1212Kernel.CorridorScale
noncomputable section

def squareCenter (α : ℝ) (t : ℕ) : ℕ := ⌊α * t⌋₊

def corridorSquare (N α : ℝ) (t : ℕ) : CorridorRectangle where
  left := squareCenter α t - squareHalfSide N
  right := squareCenter α t + squareHalfSide N
  bottom := t - squareHalfSide N
  top := t + squareHalfSide N
  horizontal := by omega
  vertical := by omega

theorem square_center_error {α : ℝ} (hα : 0 ≤ α) (t : ℕ) :
    |(squareCenter α t : ℝ) - α * t| ≤ 1 := by
  have hfloor := Nat.floor_le (show 0 ≤ α * t by positivity)
  have hlt := Nat.lt_floor_add_one (α * t)
  change (squareCenter α t : ℝ) ≤ α * t at hfloor
  change α * t < (squareCenter α t : ℝ) + 1 at hlt
  rw [abs_le]
  constructor <;> linarith

theorem corridorSquare_coordinate_errors {N α : ℝ} {t : ℕ} {p : LatticePoint}
    (hp : (corridorSquare N α t).Contains p) :
    |(p.x : ℝ) - (squareCenter α t : ℝ)| ≤ squareHalfSide N ∧
      |(p.y : ℝ) - (t : ℝ)| ≤ squareHalfSide N := by
  have hxn : squareCenter α t ≤ p.x + squareHalfSide N := by
    have h := hp.1
    change squareCenter α t - squareHalfSide N ≤ p.x at h
    omega
  have hyn : t ≤ p.y + squareHalfSide N := by
    have h := hp.2.2.1
    change t - squareHalfSide N ≤ p.y at h
    omega
  have hxUpper : p.x ≤ squareCenter α t + squareHalfSide N := hp.2.1
  have hyUpper : p.y ≤ t + squareHalfSide N := hp.2.2.2
  have hxr : (squareCenter α t : ℝ) ≤ (p.x : ℝ) + squareHalfSide N := by exact_mod_cast hxn
  have hyr : (t : ℝ) ≤ (p.y : ℝ) + squareHalfSide N := by exact_mod_cast hyn
  have hxu : (p.x : ℝ) ≤ (squareCenter α t : ℝ) + squareHalfSide N := by exact_mod_cast hxUpper
  have hyu : (p.y : ℝ) ≤ (t : ℝ) + squareHalfSide N := by exact_mod_cast hyUpper
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem corridorSquare_linear_error {N α : ℝ} (hα : 0 ≤ α) {t : ℕ} {p : LatticePoint}
    (hp : (corridorSquare N α t).Contains p) :
    |(p.x : ℝ) - α * p.y| ≤ 1 + (1 + α) * (squareHalfSide N : ℝ) := by
  obtain ⟨hx, hy⟩ := corridorSquare_coordinate_errors hp
  have hc := square_center_error hα t
  have htri := abs_add_le ((p.x : ℝ) - squareCenter α t)
    ((squareCenter α t : ℝ) - α * t)
  have htri' := abs_add_le
    (((p.x : ℝ) - squareCenter α t) + ((squareCenter α t : ℝ) - α * t))
    (α * ((t : ℝ) - p.y))
  have hscaled : |α * ((t : ℝ) - p.y)| ≤ α * (squareHalfSide N : ℝ) := by
    rw [abs_mul, abs_of_nonneg hα, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hy hα
  have heq : ((p.x : ℝ) - squareCenter α t) +
      ((squareCenter α t : ℝ) - α * t) + α * ((t : ℝ) - p.y) =
      (p.x : ℝ) - α * p.y := by ring
  rw [heq] at htri'
  nlinarith

theorem eventually_corridorSquare_contained :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      ∀ t : ℕ, N ≤ (t : ℝ) → (t : ℝ) ≤ 2 * N →
      ∀ p : LatticePoint, (corridorSquare N α t).Contains p →
        directionCorridor N α p ∧
        |(p.x : ℝ) / (p.y : ℝ) - α| ≤ rho N / 10 := by
  filter_upwards [eventually_large_domain, eventually_squareHalfSide_bounds]
    with N hdom hside
  intro α hα t ht htu p hp
  have hαlow : (4 / 3 : ℝ) < α := hα.1
  have hαup : α < (5 / 3 : ℝ) := hα.2
  have hαpos : 0 ≤ α := by linarith
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hr : 0 < rho N := Real.exp_pos _
  have hh10 : (10 : ℝ) ≤ squareHalfSide N := by exact_mod_cast hside.1
  have hhN := hside.2.1
  have hhwidth : (squareHalfSide N : ℝ) ≤ N * rho N / 100 :=
    Nat.floor_le (by positivity)
  obtain ⟨hx, hy⟩ := corridorSquare_coordinate_errors hp
  have hc := square_center_error hαpos t
  rw [abs_le] at hx hy hc
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hcenterLow := mul_le_mul_of_nonneg_right hαlow.le ht0
  have hcenterUp := mul_le_mul_of_nonneg_right hαup.le ht0
  have hpxLow : N / 2 ≤ (p.x : ℝ) := by linarith
  have hpxUp : (p.x : ℝ) ≤ 4 * N := by linarith
  have hpyLow : N / 2 ≤ (p.y : ℝ) := by linarith
  have hpyUp : (p.y : ℝ) ≤ 4 * N := by linarith
  have hyPos : (0 : ℝ) < p.y := by linarith
  have hlinear := corridorSquare_linear_error hαpos hp
  have hlin3 : |(p.x : ℝ) - α * p.y| ≤ 3 * (squareHalfSide N : ℝ) := by
    nlinarith
  have hratio : |(p.x : ℝ) / (p.y : ℝ) - α| ≤ rho N / 10 := by
    rw [show (p.x : ℝ) / (p.y : ℝ) - α =
      ((p.x : ℝ) - α * p.y) / p.y by field_simp,
      abs_div, abs_of_pos hyPos]
    apply (div_le_iff₀ hyPos).mpr
    have hyscale : N / 2 ≤ (p.y : ℝ) := hpyLow
    have hprod := mul_le_mul_of_nonneg_left hyscale hr.le
    nlinarith
  exact ⟨⟨hpxLow, hpxUp, hpyLow, hpyUp, hratio.trans (by linarith)⟩, hratio⟩

end
end Erdos1212Kernel.CorridorScale
