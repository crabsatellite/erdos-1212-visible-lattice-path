import Erdos1212Kernel.DeBruijnComparisonErrorPairing

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

/-- The formerly unknown Volterra comparison constant is now identified
from both actual conserved pairings. No normalization hypothesis remains. -/
theorem deBruijnF1_rho_normalization :
    Tendsto (fun u : Real => deBruijnF1 u / deBruijnRho u) atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) ∧
    Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  obtain ⟨C, hC, hRatio, hInv⟩ := deBruijnF1_rho_positive_comparison
  have hEq := deBruijnComparisonConstant_eq hC hInv
  subst C
  refine ⟨hRatio, ?_⟩
  simpa only [Real.exp_neg, one_div, inv_inv] using hInv

def deBruijnRhoSaddleMain (u : Real) : Real := Real.exp Real.eulerMascheroniConstant * deBruijnF1SaddleMain u

theorem deBruijnRhoSaddleMain_pos (u : Real) : 0 < deBruijnRhoSaddleMain u :=
  mul_pos (Real.exp_pos _) (deBruijnF1SaddleMain_pos u)

theorem tendsto_deBruijnRho_saddle_ratio :
    Tendsto (fun u : Real => deBruijnRho u / deBruijnRhoSaddleMain u) atTop (nhds 1) := by
  have h := (deBruijnF1_rho_normalization.2.mul tendsto_deBruijnF1_saddle_ratio).div_const (Real.exp Real.eulerMascheroniConstant)
  simp only [mul_one, div_self (Real.exp_pos Real.eulerMascheroniConstant).ne'] at h
  apply h.congr'
  filter_upwards [eventually_deBruijnF1_pos] with u hu
  unfold deBruijnRhoSaddleMain
  field_simp [hu.ne', (Real.exp_pos Real.eulerMascheroniConstant).ne', (deBruijnF1SaddleMain_pos u).ne']

theorem deBruijnRho_saddle_asymptotic : Asymptotics.IsEquivalent atTop deBruijnRho deBruijnRhoSaddleMain :=
  Asymptotics.isEquivalent_of_tendsto_one tendsto_deBruijnRho_saddle_ratio

/-- Transport back to the actual positive-axis Dickman function used by
the downstream sieve development, rather than changing its carrier. -/
theorem iwaniecDickman_saddle_asymptotic : Asymptotics.IsEquivalent atTop iwaniecDickman deBruijnRhoSaddleMain := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply tendsto_deBruijnRho_saddle_ratio.congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with u hu
  rw [deBruijnRho_eq_dickman hu]
  rfl

end

end Erdos1212Kernel
