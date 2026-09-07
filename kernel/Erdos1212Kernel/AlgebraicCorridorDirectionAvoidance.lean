import Erdos1212Kernel.AlgebraicCorridorIntegerRoot
import Erdos1212Kernel.AlgebraicCorridorTarget

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter MeasureTheory

/-- The paper's closed lattice corridor, with real coordinate bounds. -/
def directionCorridor (N α : ℝ) (p : LatticePoint) : Prop :=
  N / 2 ≤ (p.x : ℝ) ∧ (p.x : ℝ) ≤ 4 * N ∧
  N / 2 ≤ (p.y : ℝ) ∧ (p.y : ℝ) ≤ 4 * N ∧
  |(p.x : ℝ) / (p.y : ℝ) - α| ≤ rho N

def DirectionAvoidance (N α : ℝ) : Prop :=
  ∀ p : LatticePoint, directionCorridor N α p →
    ∀ F : MvPolynomial (Fin 2) ℤ, F ≠ 0 →
      F.totalDegree ≤ degree N → corridorPolynomialHeight F ≤ height N →
      MvPolynomial.eval ![(p.x : ℤ), (p.y : ℤ)] F ≠ 0

theorem eventually_directionAvoidance_of_not_mem :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      α ∉ algebraicCorridorExceptionalSet N → DirectionAvoidance N α := by
  have hrho := rho_tendsto_zero.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num))
  filter_upwards [eventually_large_domain, hrho,
    eventually_zero_near_direction_mem_exceptional] with N hdom hrho hzero
  intro α hα hnot p hp F hF hd hh hz
  have hαUpper : α < 5 / 3 := hα.2
  have hyR : (0 : ℝ) < p.y := lt_of_lt_of_le (by linarith [hdom.1]) hp.2.2.1
  have hy : 0 < p.y := by exact_mod_cast hyR
  have hratio : (p.x : ℝ) / (p.y : ℝ) ≤ 2 := by
    have h := (abs_le.mp hp.2.2.2.2).2
    linarith
  have hx : (p.x : ℝ) ≤ 2 * (p.y : ℝ) := (div_le_iff₀ hyR).mp hratio
  exact hnot (hzero F hF hd hh p.x p.y α hy hx hp.2.2.1 hp.2.2.2.2 hz)

theorem ae_eventually_directionAvoidance :
    ∀ᵐ α : ℝ ∂volume.restrict algebraicCorridorSlopeInterval,
      ∀ᶠ j : ℕ in atTop, DirectionAvoidance (dyadicScale j) α := by
  have hdyadic : Tendsto dyadicScale atTop atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hscale := hdyadic.eventually eventually_directionAvoidance_of_not_mem
  have hae := ae_eventually_outside_dyadic_algebraicCorridorExceptionalSet
  have haeRestricted : ∀ᵐ α : ℝ ∂volume.restrict algebraicCorridorSlopeInterval,
      ∀ᶠ j : ℕ in atTop, α ∉ algebraicCorridorExceptionalSet (dyadicScale j) :=
    ae_restrict_of_ae hae
  filter_upwards [haeRestricted, ae_restrict_mem (by
    exact measurableSet_Ioo : MeasurableSet algebraicCorridorSlopeInterval)]
    with α hα hmem
  filter_upwards [hscale, hα] with j hj hnot
  exact hj α hmem hnot

theorem eventually_no_bad_vertical_crossing_of_directionAvoidance :
    ∀ᶠ N : ℝ in atTop, ∀ α : ℝ, DirectionAvoidance N α →
      ∀ {lower T : ℕ} {start finish : LatticePoint}
        (walk : starLatticeGraph.Walk start finish),
        Nat.floor (N / 2) ≤ lower → lower + T - 1 ≤ Nat.floor (4 * N) →
        N ^ (9 / 10 : ℝ) ≤ (T : ℝ) →
        start.y ≤ lower → lower + T - 1 ≤ finish.y →
        (∀ p, p ∈ walk.support → directionCorridor N α p) →
        ¬(∀ p, p ∈ walk.support → CorridorBad p) := by
  filter_upwards [eventually_bad_vertical_crossing_algebraic_point,
    eventually_ge_atTop (8 : ℝ)] with N hcross hN
  intro α havoid lower T start finish walk hl hu hT hs hf hcorr hbad
  have hcoords : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y := by
    intro p hp
    have h := hcorr p hp
    have hx : (1 : ℝ) < p.x := by linarith [h.1]
    have hy : (1 : ℝ) < p.y := by linarith [h.2.2.1]
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩
  have hxl : ∀ p, p ∈ walk.support → Nat.floor (N / 2) ≤ p.x := by
    intro p hp
    have h := hcorr p hp
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ N / 2)).trans h.1
  have hbox : ∀ p, p ∈ walk.support →
      p.x ≤ Nat.floor (4 * N) ∧ p.y ≤ Nat.floor (4 * N) := by
    intro p hp
    have h := hcorr p hp
    exact ⟨Nat.le_floor h.2.1, Nat.le_floor h.2.2.2.1⟩
  obtain ⟨base, hb, F, hF, hd, hz, hh⟩ :=
    hcross walk hl hu hT hs hf hcoords hxl hbad hbox
  apply havoid base (hcorr base hb) F hF hd hh
  have hroot : corridorRoot base = ![(base.x : ℤ), (base.y : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  rwa [hroot] at hz

end
end Erdos1212Kernel.CorridorScale
