import Erdos1212Kernel.TaoRieszNeighborhoodError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem exists_taoPsi_root_log_error :
    ∃ a A X₀ : Real, 0 < a ∧ 0 < A ∧ 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x →
        |Chebyshev.psi x - x| ≤ A * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, A, X₀, ha, hA, hX, herr⟩ := exists_taoVonMangoldtRieszSum_root_log_error
  let X₁ : Real := max (2 * X₀) (max 4 (Real.exp ((4 * Real.log 2 / a) ^ 2)))
  have hX₁ : 1 ≤ X₁ := by
    have ht := le_max_left (2 * X₀) (max 4 (Real.exp ((4 * Real.log 2 / a) ^ 2)))
    dsimp [X₁]
    linarith
  refine ⟨a / 4, 1 + 8 * A, X₁, by positivity, by positivity, hX₁, ?_⟩
  intro x hx
  have hXx : 2 * X₀ ≤ x := (le_max_left _ _).trans hx
  have hx4 : 4 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxexp : Real.exp ((4 * Real.log 2 / a) ^ 2) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := by linarith
  let e : Real := Real.exp (-(a / 4) * Real.sqrt (Real.log x))
  let h : Real := x * e
  let E : Real := 4 * A * x ^ 2 * Real.exp (-(a / 2) * Real.sqrt (Real.log x))
  have he0 : 0 < e := Real.exp_pos _
  have hehalf : e ≤ 1 / 2 := tao_unsmoothing_step_decay ha hxexp
  have hh0 : 0 < h := mul_pos hx0 he0
  have hhhalf : h ≤ x / 2 := by
    have ht := mul_le_mul_of_nonneg_left hehalf hx0.le
    dsimp [h]
    linarith
  have hminus : |taoVonMangoldtIntegrated (x - h) - (x - h) ^ 2 / 2| ≤ E := by
    apply taoVonMangoldtIntegrated_neighborhood_error ha hA.le hX herr hx4 hXx <;> linarith
  have hcenter : |taoVonMangoldtIntegrated x - x ^ 2 / 2| ≤ E := by
    apply taoVonMangoldtIntegrated_neighborhood_error ha hA.le hX herr hx4 hXx <;> linarith
  have hplus : |taoVonMangoldtIntegrated (x + h) - (x + h) ^ 2 / 2| ≤ E := by
    apply taoVonMangoldtIntegrated_neighborhood_error ha hA.le hX herr hx4 hXx <;> linarith
  have hpsi := taoPsi_error_of_three_integrated_errors hh0
    (show 0 < x - h by linarith) hminus hcenter hplus
  have heq : Real.exp (-(a / 2) * Real.sqrt (Real.log x)) = e ^ 2 := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbudget : (h ^ 2 / 2 + 2 * E) / h ≤ (1 + 8 * A) * x * e := by
    apply (div_le_iff₀ hh0).mpr
    dsimp [E, h]
    rw [heq]
    nlinarith only [sq_nonneg (x * e)]
  exact hpsi.trans hbudget

end

end Erdos1212Kernel
