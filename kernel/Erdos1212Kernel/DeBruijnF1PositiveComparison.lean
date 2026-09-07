import Erdos1212Kernel.DeBruijnF1SaddleEstimate
import Erdos1212Kernel.DeBruijnF1Comparison

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem eventually_deBruijnF1_pos : ∀ᶠ u : Real in atTop, 0 < deBruijnF1 u := by
  have h := tendsto_deBruijnF1_saddle_ratio.eventually (Ioi_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [h] with u hu
  have hp := (lt_div_iff₀ (deBruijnF1SaddleMain_pos u)).mp hu
  simpa only [zero_mul] using hp

/-- Eventual positivity from the actual saddle estimate is propagated
through the original Volterra equation, excluding a zero comparison limit. -/
theorem deBruijnF1_ratio_has_positive_limit :
    ∃ C : Real, 0 < C ∧ Tendsto (fun x : Real => deBruijnF1 x / deBruijnRho x) atTop (nhds C) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_deBruijnF1_pos
  let a : Real := max A 1 + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [le_max_right A (1 : Real)]
  have hf : ContinuousOn (deBruijnRhoSolutionRatio deBruijnF1) (Set.Ici (0 : Real)) :=
    deBruijnRhoSolutionRatio_continuousOn deBruijnF1_continuous.continuousOn
  have heq : DeBruijnRhoVolterraEquation (deBruijnRhoSolutionRatio deBruijnF1) :=
    deBruijnRhoSolutionRatio_equation (fun x _hx => deBruijnF1_convolution x)
  have hc : ContinuousOn (deBruijnRhoSolutionRatio deBruijnF1) (Set.Icc (a - 1) a) :=
    hf.mono (fun x hx => by change 0 ≤ x; linarith [hx.1])
  have hpos : ∀ x ∈ Set.Icc (a - 1) a, (0 : Real) < deBruijnRhoSolutionRatio deBruijnF1 x := by
    intro x hx
    have hxA : A ≤ x := by dsimp [a] at hx; linarith [hx.1, le_max_left A (1 : Real)]
    have hx0 : 0 ≤ x := by linarith [hx.1]
    unfold deBruijnRhoSolutionRatio
    rw [deBruijnRho_eq_dickman hx0]
    exact div_pos (hA x hxA) (iwaniecDickman_pos hx0)
  obtain ⟨m, hm, hmw⟩ := isCompact_Icc.exists_forall_le' hc hpos
  have hfuture := deBruijnRhoVolterra_lower_propagation hf heq ha hmw
  obtain ⟨C, hC⟩ := deBruijnF1_ratio_has_limit
  have hmC : m ≤ C := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hC
    filter_upwards [eventually_ge_atTop a] with x hx
    exact hfuture x hx
  exact ⟨C, hm.trans_le hmC, hC⟩

theorem deBruijnF1_rho_positive_comparison :
    ∃ C : Real, 0 < C ∧
      Tendsto (fun x : Real => deBruijnF1 x / deBruijnRho x) atTop (nhds C) ∧
      Tendsto (fun x : Real => deBruijnRho x / deBruijnF1 x) atTop (nhds (1 / C)) := by
  obtain ⟨C, hCpos, hC⟩ := deBruijnF1_ratio_has_positive_limit
  refine ⟨C, hCpos, hC, ?_⟩
  have h := hC.inv₀ hCpos.ne'
  simpa only [inv_div, one_div] using h

end

end Erdos1212Kernel
