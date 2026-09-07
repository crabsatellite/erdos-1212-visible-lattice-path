import Erdos1212Kernel.DeBruijnLogIntegralBound
import Erdos1212Kernel.DeBruijnRhoLogSaddle

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem deBruijnRho_log_expansion :
    Asymptotics.IsBigO atTop (fun u : Real => Real.log (deBruijnRho u) + deBruijnRhoLogMain u) deBruijnRhoLogErrorScale := by
  have h := deBruijnRho_log_saddle_error.sub deBruijn1951SaddleIntegral_log_expansion
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with u
  ring

def deBruijnRhoLogRemainder (u : Real) : Real :=
  -(Real.log (deBruijnRho u) + deBruijnRhoLogMain u) / u

theorem deBruijnRhoLogRemainder_bound :
    Asymptotics.IsBigO atTop deBruijnRhoLogRemainder deBruijnSaddleLogErrorScale := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp deBruijnRho_log_expansion
  apply Asymptotics.IsBigO.of_bound c
  filter_upwards [hc, eventually_gt_atTop (0 : Real)] with u hu hu0
  have h : |Real.log (deBruijnRho u) + deBruijnRhoLogMain u| ≤ c * (u * |deBruijnSaddleLogErrorScale u|) := by
    simpa only [Real.norm_eq_abs, deBruijnRhoLogErrorScale, deBruijnSaddleLogErrorScale, abs_mul, abs_of_pos hu0] using hu
  change |-(Real.log (deBruijnRho u) + deBruijnRhoLogMain u) / u| ≤ c * |deBruijnSaddleLogErrorScale u|
  rw [abs_div, abs_neg, abs_of_pos hu0]
  apply (div_le_iff₀ hu0).mpr
  calc
    _ ≤ c * (u * |deBruijnSaddleLogErrorScale u|) := h
    _ = _ := by ring

theorem deBruijnRho_logarithmic_identity {u : Real} (hu : 1 < u) :
    deBruijnRho u = Real.exp (-u * (Real.log u + Real.log (Real.log u) - 1 - 1 / Real.log u +
      Real.log (Real.log u) / Real.log u + deBruijnRhoLogRemainder u)) := by
  have hu0 : 0 < u := by linarith
  have hρ : 0 < deBruijnRho u := by
    rw [deBruijnRho_eq_dickman hu0.le]
    exact iwaniecDickman_pos hu0.le
  have he : -u * (Real.log u + Real.log (Real.log u) - 1 - 1 / Real.log u +
      Real.log (Real.log u) / Real.log u + deBruijnRhoLogRemainder u) = Real.log (deBruijnRho u) := by
    unfold deBruijnRhoLogRemainder deBruijnRhoLogMain
    field_simp [hu0.ne']
    <;> ring
  rw [he, Real.exp_log hρ]

/-- Literal de Bruijn 1951 (1.8): all displayed signs and coefficients
and the stated big-O remainder inside the exponent are retained. -/
theorem deBruijn1951_rho_logarithmic_formula :
    ∃ E : Real → Real,
      Asymptotics.IsBigO atTop E (fun u => (Real.log (Real.log u)) ^ 2 / (Real.log u) ^ 2) ∧
      ∀ᶠ u : Real in atTop, deBruijnRho u = Real.exp (-u *
        (Real.log u + Real.log (Real.log u) - 1 - 1 / Real.log u + Real.log (Real.log u) / Real.log u + E u)) := by
  refine ⟨deBruijnRhoLogRemainder, deBruijnRhoLogRemainder_bound, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact deBruijnRho_logarithmic_identity hu

theorem iwaniecDickman_logarithmic_formula :
    ∃ E : Real → Real,
      Asymptotics.IsBigO atTop E (fun u => (Real.log (Real.log u)) ^ 2 / (Real.log u) ^ 2) ∧
      ∀ᶠ u : Real in atTop, iwaniecDickman u = Real.exp (-u *
        (Real.log u + Real.log (Real.log u) - 1 - 1 / Real.log u + Real.log (Real.log u) / Real.log u + E u)) := by
  obtain ⟨E, hE, hEq⟩ := deBruijn1951_rho_logarithmic_formula
  refine ⟨E, hE, ?_⟩
  filter_upwards [hEq, eventually_ge_atTop (0 : Real)] with u hu hpos
  rw [deBruijnRho_eq_dickman hpos] at hu
  exact hu

end

end Erdos1212Kernel
