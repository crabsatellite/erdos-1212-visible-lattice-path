import Erdos1212Kernel.AlgebraicCorridorGeometricScale

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

/-- Proposition 5.2 for a literal vertical bad star crossing in a rectangle
inside `[N/2,4N]^2`.  All row-selection, support-column and interpolation
inputs are produced from `N`; none remain as hypotheses. -/
theorem eventually_bad_vertical_crossing_algebraic_point :
    ∀ᶠ N : ℝ in atTop, ∀ {lower T : ℕ}
      {start finish : LatticePoint}
      (walk : starLatticeGraph.Walk start finish),
      Nat.floor (N / 2) ≤ lower → lower + T - 1 ≤ Nat.floor (4 * N) →
      N ^ (9 / 10 : ℝ) ≤ (T : ℝ) →
      start.y ≤ lower → lower + T - 1 ≤ finish.y →
      (∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y) →
      (∀ p, p ∈ walk.support → Nat.floor (N / 2) ≤ p.x) →
      (∀ p, p ∈ walk.support → CorridorBad p) →
      (∀ p, p ∈ walk.support →
        p.x ≤ Nat.floor (4 * N) ∧ p.y ≤ Nat.floor (4 * N)) →
      ∃ base : LatticePoint, base ∈ walk.support ∧
        ∃ F : MvPolynomial (Fin 2) ℤ,
          F ≠ 0 ∧ F.totalDegree ≤ degree N ∧
          MvPolynomial.eval (corridorRoot base) F = 0 ∧
          corridorPolynomialHeight F ≤ height N := by
  filter_upwards [eventually_large_domain,
    eventually_two_z_lt_floor_half,
    eventually_band_lt_z,
    eventually_band_two,
    eventually_exists_corridor_band_rows_in_interval,
    eventually_actual_band_safe_supports,
    eventually_AlgebraicPointAtScale,
    z_tendsto.eventually_ge_atTop (2 : ℝ)] with
      N hdom htwoZ hbandZ hbandTwo hrows hsupports hscale hzTwo
  intro lower T start finish walk hlower hupper hT hstart hfinish
    hcoordinate hwalkXLower hbad hbox
  have hNPos : 0 < N := zero_lt_one.trans hdom.1
  have hlowerPos : 0 < lower := by
    have hfloorPos : (0 : ℝ) < (Nat.floor (N / 2) : ℝ) :=
      (show 0 < 2 * z N by nlinarith).trans htwoZ
    exact lt_of_lt_of_le (by exact_mod_cast hfloorPos) hlower
  have hfar : (2 * z N : ℝ) < lower :=
    htwoZ.trans_le (by exact_mod_cast hlower)
  obtain ⟨blockLower, row, hrow, hblockRange, hrowBand,
      hrowComposite, hrough⟩ := hrows lower T hlowerPos hfar hT
  have hblockTwo : 1 < blockLower := by
    have hzPos : 0 < z N := by linarith
    have hlowReal : (2 : ℝ) < lower := by nlinarith
    have hlowNat : 2 < lower := by exact_mod_cast hlowReal
    omega
  have hblockUpper : blockLower + band N - 1 ≤ Nat.floor (4 * N) := by
    omega
  have hsupportAll : ∀ x : ℕ, Nat.floor (N / 2) ≤ x →
      ∃ west east : ℕ,
        west < x ∧ x < east ∧ west < east ∧
        x ≤ west + supportGap N ∧ east ≤ x + supportGap N ∧
        (∀ y, CorridorBandPoint blockLower (band N) {x := west, y := y} →
          SafePoint {x := west, y := y}) ∧
        (∀ y, CorridorBandPoint blockLower (band N) {x := east, y := y} →
          SafePoint {x := east, y := y}) := by
    intro x hx
    exact hsupports blockLower x hblockTwo hblockUpper hx
  have hstartBlock : start.y ≤ blockLower :=
    hstart.trans hblockRange.1
  have hfinishBlock : blockLower + band N - 1 ≤ finish.y := by
    omega
  exact bad_crossing_algebraic_point_at_scale hNPos hscale row hrow hrough
    hrowBand hbandZ hrowComposite hsupportAll walk hbandTwo hstartBlock
    hfinishBlock hcoordinate hwalkXLower hbad hbox

end

end Erdos1212Kernel.CorridorScale
