import Erdos1212Kernel.IwaniecSmallParameterBounds

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 700000

/-- Consume the exact ordinary profile formula before cancelling the
Euler normalization. This retains the coefficient needed by Vaughan's
moving parameter, on the actual finite tree at its explicit full depth. -/
theorem exists_iwaniecCubicMain_unscaled_moving_margin :
    ∃ C D : Real, 0 < C ∧ 0 < D ∧ ∀ (y : Nat) (δ : Real),
      1 < (y : Real) → 0 ≤ δ → δ ≤ 1 → 2 + δ ≤ iwaniecPaperXi (y : Real) →
      2 ≤ Real.exp (Real.log (y : Real) / (2 + δ)) →
      δ / Real.log (y : Real) -
        D * Real.exp (-Real.sqrt (Real.log (y : Real) / (2 + δ))) -
        C * iwaniecAuxWeightPower y (2 + δ) * iwaniecAuxG 2 (2 + δ) / Real.log (y : Real) ^ 2 <
        iwaniecCubicWeightedMainExpansion
          ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1) y
          (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))) := by
  obtain ⟨C₀, D₀, hC₀, hD₀, hmain⟩ := exists_iwaniecCubicMain_lower_bound
  let C := Real.exp (-Real.eulerMascheroniConstant) * C₀
  let D := Real.exp (-Real.eulerMascheroniConstant) * D₀
  refine ⟨C, D, by dsimp [C]; positivity, by dsimp [D]; positivity, ?_⟩
  intro y δ hy hδ hδ1 hsξ hcut
  have hL := Real.log_pos hy
  have hs2 : 2 ≤ 2 + δ := by linarith
  have hs4 : 2 + δ ≤ 4 := by linarith
  have hsource := hmain ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1)
    y (2 + δ) (by omega) hy hs2 hsξ hcut (by omega)
  have hcancel : Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add]
    simp
  have hright (m : Real) : Real.exp (-Real.eulerMascheroniConstant) * (Real.exp Real.eulerMascheroniConstant * m) = m := by
    rw [← mul_assoc, hcancel, one_mul]
  have hnormal : Real.exp (-Real.eulerMascheroniConstant) *
      (((2 + δ) - iwaniecEvenSieveSeries (2 + δ)) / Real.log (y : Real)) =
      2 * Real.log (1 + δ) / Real.log (y : Real) := by
    rw [iwaniecEvenSieveSeries_explicit hs2 hs4, show (2 + δ) - 1 = 1 + δ by ring]
    calc
      _ = (Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant) *
          (2 * Real.log (1 + δ) / Real.log (y : Real)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hm := mul_lt_mul_of_pos_left hsource (Real.exp_pos (-Real.eulerMascheroniConstant))
  rw [mul_sub, mul_sub, hnormal, hright] at hm
  have hm' : 2 * Real.log (1 + δ) / Real.log (y : Real) -
      D * Real.exp (-Real.sqrt (Real.log (y : Real) / (2 + δ))) -
      C * iwaniecAuxWeightPower y (2 + δ) * iwaniecAuxG 2 (2 + δ) / Real.log (y : Real) ^ 2 <
      iwaniecCubicWeightedMainExpansion
        ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1) y
        (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))) := by
    dsimp only [C, D]
    convert hm using 1 <;> ring
  have hlog := Real.le_log_one_add_of_nonneg hδ
  have hhalf : δ / 2 ≤ 2 * δ / (δ + 2) := by
    apply (le_div_iff₀ (show 0 < δ + 2 by linarith)).mpr
    have hsq := mul_le_mul_of_nonneg_left hδ1 hδ
    nlinarith only [hsq, hδ]
  have hlower := div_le_div_of_nonneg_right
    (show δ ≤ 2 * Real.log (1 + δ) by linarith only [hhalf, hlog]) hL.le
  linarith only [hm', hlower]

/-- Uniform small-parameter lower bound for the actual finite tree.
All analytic cutoff conditions and errors are discharged above one
threshold independent of delta; only its literal range remains. -/
theorem exists_iwaniecCubicMain_uniform_small_parameter :
    ∃ B Y : Real, 0 < B ∧ 1 < Y ∧ ∀ (y : Nat) (δ : Real),
      Y ≤ (y : Real) → 0 ≤ δ → δ ≤ 1 →
      δ / Real.log (y : Real) - B / Real.log (y : Real) ^ 2 <
        iwaniecCubicWeightedMainExpansion
          ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1) y
          (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))) := by
  obtain ⟨C, D, hC, hD, hmain⟩ := exists_iwaniecCubicMain_unscaled_moving_margin
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    (eventually_iwaniecWeightPower_small_parameter_bound.and
      ((eventually_iwaniecEulerError_small_parameter hD.le).and
        ((tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop 3).and
          (Real.tendsto_log_atTop.eventually_ge_atTop 6))))
  let B := 4 * C + 1
  let Y := max 2 Y₀
  have hY : 1 < Y := lt_of_lt_of_le (by norm_num : (1 : Real) < 2) (le_max_left _ _)
  refine ⟨B, Y, by dsimp [B]; positivity, hY, ?_⟩
  intro y δ hy hδ hδ1
  obtain ⟨hweight, hEuler, hxi, hlog⟩ := hY₀ (y : Real) ((le_max_right _ _).trans hy)
  have hy1 := hweight.1
  have hL := Real.log_pos hy1
  have hs2 : 2 ≤ 2 + δ := by linarith
  have hs3 : 2 + δ ≤ 3 := by linarith
  have hs0 : 0 < 2 + δ := by linarith
  have hsxi : 2 + δ ≤ iwaniecPaperXi (y : Real) := hs3.trans hxi
  have hquot : (2 : Real) ≤ Real.log (y : Real) / (2 + δ) := by
    apply (le_div_iff₀ hs0).mpr
    linarith only [hs3, hlog]
  have hcut : (2 : Real) ≤ Real.exp (Real.log (y : Real) / (2 + δ)) := by
    have hh := Real.add_one_le_exp (Real.log (y : Real) / (2 + δ))
    linarith only [hquot, hh]
  have hW := hweight.2 (2 + δ) (by linarith) hs3
  have hG := iwaniecAuxG_le_two 2 hs2
  have hG0 := (iwaniecAuxG_pos 2 hs2).le
  have hWG : iwaniecAuxWeightPower y (2 + δ) * iwaniecAuxG 2 (2 + δ) ≤ 4 := by
    have hh := mul_le_mul hW hG hG0 (by norm_num : (0 : Real) ≤ 2)
    norm_num at hh
    exact hh
  have hCerr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hWG hC.le) (sq_nonneg (Real.log (y : Real)))
  have hCerr' : C * iwaniecAuxWeightPower y (2 + δ) * iwaniecAuxG 2 (2 + δ) / Real.log (y : Real) ^ 2 ≤
      4 * C / Real.log (y : Real) ^ 2 := by
    convert hCerr using 1 <;> ring
  have hDerr := hEuler.2 (2 + δ) hs2 hs3
  have hm := hmain y δ hy1 hδ hδ1 hsxi hcut
  dsimp only [B]
  rw [add_div]
  linarith only [hm, hCerr', hDerr]

end

end Erdos1212Kernel
